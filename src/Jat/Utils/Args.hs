-- | This moduel provides the argument parsing for the command line.
module Jat.Utils.Args
  (
    Options (..)
  , Format (..)
  , Domain (..)
  , Simplify (..)
  , parseArgs
  )
where

import Jat.Utils.Version

import System.Console.GetOpt
import System.Environment (getArgs)
import System.Exit
import System.IO

-- TODO: should define funcitons if common interface
                                    --
-- | A computation graph can be returned as Dot graph or as TRSs.
data Format = DOT | TRS | ITRS | P | PRG deriving (Show,Read)
data Domain = Sharing | UnSharing deriving (Show,Read)
data Simplify = WithNarrowing | WithNone deriving (Show,Read)

-- | The options for the arguments.
data Options = Options {
    input       :: IO String
  , output      :: String -> IO ()
  , file        :: String
  , cname       :: Maybe String
  , mname       :: Maybe String
  , timeout     :: Int
  , format      :: Format
  , simplify    :: Simplify
  , domain      :: Domain
  , interactive :: Bool
  }

defaultOptions :: Options
defaultOptions = Options {
    input       = getContents
  , output      = putStrLn
  , file        = undefined
  , cname       = Nothing
  , mname       = Nothing
  , timeout     = 10 * 1000000
  , format      = DOT
  , simplify    = WithNone
  , domain      = Sharing
  , interactive = False
  }

options :: [OptDescr (Options -> IO Options)]
options = [
    {-Option "i" ["input"]-}
      {-(ReqArg (\arg opt -> return opt { input = readFile arg}) "FILE")  -}
      {-"input file"-}
  Option "o" ["output"]
      (ReqArg (\arg opt -> return opt {output = writeFile arg}) "FILE")  
      "output file"
  , Option "f" ["format"]
      (ReqArg (\arg opt -> return opt {format = read arg :: Format}) "DOT|TRS|ITRS|PRG")
      "output format"
  , Option "s" ["simplify"]
      (ReqArg (\arg opt -> return opt {simplify = read arg :: Simplify}) "WithNarrowing|WithNone")
      "output simplify"
  , Option "d" ["domain"]
      (ReqArg (\arg opt -> return opt {domain = read arg :: Domain}) "Sharing|UnSharing")
      "heap domain"
  , Option "t" ["timeout"]
      (ReqArg (\arg opt -> return opt {timeout = 10000000 * (read arg :: Int)}) "sec")
      "timeout in seconds"
  , Option "i" ["interactive"]         
      (NoArg $ \opt -> return opt {interactive=True,timeout=0} )
      "interactive mode" 
  , Option "v" ["version"]         
      (NoArg $ \_ -> do
        hPutStrLn stderr version
        exitSuccess)
      "print version" 
  , Option "h" ["help"]         
      (NoArg $ \_ -> do
        hPutStrLn stderr (usageInfo header options)
        exitSuccess)
      "print help"
  ]

header :: String
header = "Usage: jat [OPTION...] File [ClassId MethodId]"
  
-- | Parses the command line arguments.
parseArgs :: IO Options
parseArgs = do
  args <- getArgs
  let (actions, nopts, errors) = getOpt Permute options args
  case () of
    _ | not (null errors) -> error $ concat errors ++ "\n" ++ usageInfo header options
      | otherwise         -> do
          opts <- foldl (>>=) (return defaultOptions) actions
          let opts' = case nopts of
                         [f,cn,mn] -> opts{file=f,cname=Just cn,mname=Just mn}
                         [f]       -> opts{file=f}
                         _         -> error header
          return opts'

