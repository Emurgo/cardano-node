{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Cardano.Testnet.Test.Gov.DRepRetirement
  ( hprop_drep_retirement
  ) where

import           Cardano.Api

import           Cardano.Testnet

import           Prelude

import           Data.Default.Class
import qualified Data.Text as Text
import           System.FilePath ((</>))

import           Testnet.Components.Query
import           Testnet.Defaults
import           Testnet.Process.Cli.Keys
import           Testnet.Process.Run (execCli', mkExecConfig)
import           Testnet.Property.Util (integrationRetryWorkspace)
import           Testnet.Start.Types
import           Testnet.Types

import           Hedgehog
import qualified Hedgehog as H
import qualified Hedgehog.Extras as H

-- | The era in which this test runs
sbe :: ShelleyBasedEra ConwayEra
sbe = ShelleyBasedEraConway

-- Execute this test with:
-- @DISABLE_RETRIES=1 cabal test cardano-testnet-test --test-options '-p "/DRep Retirement/"'@
hprop_drep_retirement :: Property
hprop_drep_retirement = integrationRetryWorkspace 2 "drep-retirement" $ \tempAbsBasePath' -> H.runWithDefaultWatchdog_ $ do
  -- Start a local test net
  conf@Conf { tempAbsPath } <- H.noteShowM $ mkConf tempAbsBasePath'
  let tempAbsPath' = unTmpAbsPath tempAbsPath
      tempBaseAbsPath = makeTmpBaseAbsPath tempAbsPath

  work <- H.createDirectoryIfMissing $ tempAbsPath' </> "work"

  let cardanoNodeEra = AnyShelleyBasedEra sbe
      fastTestnetOptions = def { cardanoNodeEra }
      shelleyOptions = def { genesisEpochLength = 50 } -- 50 * (1/10s) length, i.e. 5 seconds

  TestnetRuntime
    { testnetMagic
    , testnetNodes
    , wallets=wallet0:_
    , configurationFile
    }
    <- cardanoTestnetDefault fastTestnetOptions shelleyOptions conf

  node <- H.headM testnetNodes
  poolSprocket1 <- H.noteShow $ nodeSprocket node
  execConfig <- mkExecConfig tempBaseAbsPath poolSprocket1 testnetMagic
  let socketPath = nodeSocketPath node

  epochStateView <- getEpochStateView configurationFile socketPath

  H.note_ $ "Sprocket: " <> show poolSprocket1
  H.note_ $ "Abs path: " <> tempAbsBasePath'
  H.note_ $ "Socketpath: " <> unFile socketPath

  -- Create Conway constitution
  gov <- H.createDirectoryIfMissing $ work </> "governance"

  let stakeVkeyFp = gov </> "stake.vkey"
      stakeSKeyFp = gov </> "stake.skey"

  cliStakeAddressKeyGen
    $ KeyPair  { verificationKey = File stakeVkeyFp
               , signingKey = File stakeSKeyFp
               }
  let sizeBefore = 3
  checkDRepsNumber epochStateView sbe sizeBefore

  -- Deregister first DRep
  let dreprRetirementCertFile = gov </> "drep-keys" <> "drep1.retirementcert"

  H.noteM_ $ execCli' execConfig
     [ "conway", "governance", "drep", "retirement-certificate"
     , "--drep-verification-key-file", verificationKeyFp $ defaultDRepKeyPair 1
     , "--deposit-amt", show @Int 1_000_000
     , "--out-file", dreprRetirementCertFile
     ]

  H.noteM_ $ execCli' execConfig
    [ "conway", "query", "utxo"
    , "--address", Text.unpack $ paymentKeyInfoAddr wallet0
    , "--cardano-mode"
    , "--out-file", work </> "utxo-11.json"
    ]

  txin2 <- findLargestUtxoForPaymentKey epochStateView sbe wallet0

  drepRetirementRegTxbodyFp <- H.note $ work </> "drep.retirement.txbody"
  drepRetirementRegTxSignedFp <- H.note $ work </> "drep.retirement.tx"

  H.noteM_ $ execCli' execConfig
    [ "conway", "transaction", "build"
    , "--tx-in", Text.unpack $ renderTxIn txin2
    , "--change-address", Text.unpack $ paymentKeyInfoAddr wallet0
    , "--certificate-file", dreprRetirementCertFile
    , "--witness-override", "2"
    , "--out-file", drepRetirementRegTxbodyFp
    ]

  H.noteM_ $ execCli' execConfig
    [ "conway", "transaction", "sign"
    , "--tx-body-file", drepRetirementRegTxbodyFp
    , "--signing-key-file", signingKeyFp $ paymentKeyInfoPair wallet0
    , "--signing-key-file", signingKeyFp $ defaultDRepKeyPair 1
    , "--out-file", drepRetirementRegTxSignedFp
    ]

  H.noteM_ $ execCli' execConfig
    [ "conway", "transaction", "submit"
    , "--tx-file", drepRetirementRegTxSignedFp
    ]

  -- The important bit is that we pass (sizeBefore - 1) as the last argument,
  -- to witness that the number of dreps indeed decreased.
  checkDRepsNumber epochStateView sbe (sizeBefore - 1)
  H.success
