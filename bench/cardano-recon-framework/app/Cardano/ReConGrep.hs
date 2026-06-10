module Main(main) where

import           Cardano.Logging.Types.TraceMessage (TraceMessage (..))
import qualified Cardano.ReCon.LTL.ContinuousFormula as CF
import           Cardano.ReCon.LTL.Formula (OnMissingKey (..))
import           Cardano.ReCon.LTL.Formula.Parser (Context (..))
import qualified Cardano.ReCon.LTL.Formula.Parser as Parser
import           Cardano.ReCon.LTL.Formula.Yaml (YamlReadError, readFormulas, readPropValues)
import           Cardano.ReCon.Trace.Event ()
import           Cardano.ReCon.Trace.Feed (TemporalEvent (..))

import           Control.Arrow ((>>>))
import           Control.Monad ((>=>))
import           Control.Monad.Reader (runReader)
import           Data.Aeson (decodeStrict')
import           Data.Aeson.Encode.Pretty (encodePrettyToTextBuilder)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BChar8
import qualified Data.Text.IO as TIO
import           Data.Text.Lazy (toStrict)
import           Data.Text.Lazy.Builder (toLazyText)
import           Data.Char (toLower)
import qualified Data.Map.Strict as Map
import           Data.Time.Clock.POSIX (utcTimeToPOSIXSeconds)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Traversable (for)
import           GHC.IO.Encoding (setLocaleEncoding, utf8)
import           Options.Applicative
import           System.Exit (die)

data CliOptions = CliOptions
  { formulas     :: FilePath
  , traces       :: Maybe FilePath
  , context      :: Maybe FilePath
  , onMissingKey :: OnMissingKey
  }

readOnMissingKey :: ReadM OnMissingKey
readOnMissingKey = eitherReader $ fmap toLower >>> \case
  "crash"  -> Right CrashOnMissingKey
  "bottom" -> Right BottomOnMissingKey
  _        -> Left "Expected either of: 'crash' or 'bottom'"

parseCliOptions :: Parser CliOptions
parseCliOptions = CliOptions
  <$> option str
        (  long "formulas"
        <> metavar "FILE"
        <> help "YAML file with a list of ContinuousFormulas")
  <*> option (optional str)
        (  long "traces"
        <> value Nothing
        <> metavar "FILE"
        <> help "JSON array of TraceMessages to filter (default: stdin)")
  <*> option (optional str)
        (  long "context"
        <> value Nothing
        <> metavar "FILE"
        <> help "context variables YAML file")
  <*> option readOnMissingKey
        (  long "on-missing-key"
        <> metavar "<crash|bottom>"
        <> showDefaultWith (\case BottomOnMissingKey -> "bottom"; CrashOnMissingKey -> "crash")
        <> value BottomOnMissingKey
        <> help "behaviour when a formula atom references a missing event property key")

opts :: ParserInfo CliOptions
opts = info (parseCliOptions <**> helper)
  (fullDesc <> progDesc "Print log events that realise all given continuous formulas (Global Realisation Print)")

msgToEvent :: TraceMessage -> TemporalEvent
msgToEvent msg = TemporalEvent { beg = round (utcTimeToPOSIXSeconds msg.tmsgAt * 1_000_000), messages = [msg] }

prettyMsg :: TraceMessage -> Text
prettyMsg = toStrict . toLazyText . encodePrettyToTextBuilder

printArray :: [TraceMessage] -> IO ()
printArray [] = TIO.putStrLn "[]"
printArray msgs =
  TIO.putStr $ Text.unlines $ "[" : map prettyMsg msgs ++ ["]"]

main :: IO ()
main = do
  setLocaleEncoding utf8
  options <- execParser opts
  ctx <- maybe [] Map.toList <$>
    for options.context (readPropValues >=> dieOnYamlError)
  rawFormulas <- readFormulas options.formulas
                   (Context { interpDomain = ctx, varKinds = Map.empty })
                   Parser.name
                 >>= dieOnYamlError
  cformulas <- mapM retractOrDie rawFormulas
  content <- maybe BS.getContents BChar8.readFile options.traces
  msgs <- maybe (die "Failed to parse input as a JSON array of TraceMessages") pure
            (decodeStrict' content :: Maybe [TraceMessage])
  let matching = [ msg | msg <- msgs
                       , let event = msgToEvent msg
                       , all (\phi -> runReader (CF.eval phi event) options.onMissingKey) cformulas ]
  printArray matching
  where
    dieOnYamlError :: Either YamlReadError a -> IO a
    dieOnYamlError (Left err) = die (Text.unpack err)
    dieOnYamlError (Right ok) = pure ok

    retractOrDie phi = case CF.retract phi of
      Just cf -> pure cf
      Nothing -> die
        "One of the formulas contains a temporal connective; filter mode only accepts continuous formulas"
