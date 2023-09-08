{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Parsers.Run
  ( commands
  , runTestnetCmd
  , pref
  , opts
  ) where

import           Cardano.CLI.Environment
import           Data.Foldable
import           Options.Applicative
import qualified Options.Applicative as Opt
import           Parsers.Babbage as Babbage
import           Parsers.Byron
import           Parsers.Cardano
import           Parsers.Conway as Conway
import           Parsers.Help
import           Parsers.Shelley
import           Parsers.Version
import           Testnet.Options
import           Testnet.Property.Run (runTestnet)

pref :: ParserPrefs
pref = Opt.prefs $ showHelpOnEmpty <> showHelpOnError

opts :: EnvCli -> ParserInfo CardanoTestnetCommands
opts envCli = Opt.info (commands envCli <**> helper) idm

-- TODO: Remove StartBabbageTestnet and StartShelleyTestnet
-- by allowing the user to start testnets in any era (excluding Byron)
-- via StartCardanoTestnet
data CardanoTestnetCommands
  = StartConwayTestnet ConwayOptions
  | StartBabbageTestnet BabbageOptions
  | StartByrontestnet ByronOptions -- TODO: Do we care about being able to start a Byron only testnet?
  | StartCardanoTestnet CardanoOptions
  | StartShelleyTestnet ShelleyOptions
  | GetVersion VersionOptions
  | Help ParserPrefs (ParserInfo CardanoTestnetCommands) HelpOptions

commands :: EnvCli -> Parser CardanoTestnetCommands
commands envCli =
  asum
    [ fmap StartCardanoTestnet (subparser (cmdCardano envCli))
    , fmap StartByrontestnet (subparser cmdByron)
    , fmap StartShelleyTestnet (subparser cmdShelley)
    , fmap StartBabbageTestnet (subparser cmdBabbage)
    , fmap StartConwayTestnet (subparser cmdConway)
    , fmap GetVersion (subparser cmdVersion)
    , fmap (Help pref (opts envCli)) (subparser cmdHelp)
    ]


runTestnetCmd :: CardanoTestnetCommands -> IO ()
runTestnetCmd = \case
  StartBabbageTestnet cmdOpts -> runBabbageOptions cmdOpts
  StartConwayTestnet cmdOpts -> runConwayOptions cmdOpts
  StartByrontestnet cmdOpts -> runByronOptions cmdOpts
  StartCardanoTestnet cmdOpts -> runCardanoOptions cmdOpts
  StartShelleyTestnet cmdOpts -> runShelleyOptions cmdOpts
  GetVersion cmdOpts -> runVersionOptions cmdOpts
  Help pPrefs pInfo cmdOpts -> runHelpOptions pPrefs pInfo cmdOpts

runBabbageOptions :: BabbageOptions -> IO ()
runBabbageOptions options =
  runTestnet $ testnet (BabbageOnlyTestnetOptions $ Babbage.testnetOptions options)

runConwayOptions :: ConwayOptions -> IO ()
runConwayOptions options =
  runTestnet $ testnet (ConwayOnlyTestnetOptions $ Conway.testnetOptions options)
