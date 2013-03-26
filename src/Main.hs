module Main (
    main
) where

import Jat.CompGraph
import Jat.JatM
import Jat.PState
import Jat.Program as P
import Jat.Utils.Args as A
import Jat.Utils.Pretty
import Jat.Utils.Dot
import Data.Rewriting.Rule

import qualified Data.Map as M
import System.IO
import qualified System.Timeout as T
import qualified Control.Exception as E
import Data.Char (toLower)
import Control.Monad
import Control.Monad.Identity (runIdentity)
import Data.Maybe (fromMaybe)

import Data.List (nub)


main ::  IO ()
main = do
  opts <- parseArgs
  let Options {
      A.file        = file
    , A.output      = output
    , A.cname       = cname
    , A.mname       = mname
    } = opts
  pM <- readFile file
  let p = P.parseProgram pM
  case (cname,mname) of
    (Just cn, Just mn) -> writeOne opts $ run opts p (P.ClassId cn) (P.MethodId mn)
    _                  -> writeAll opts $ runAll opts p
    

writeOne :: Options -> IO (ClassId,MethodId, Either E.SomeException String) -> IO ()
writeOne opts run = do
  (cn,nn,e) <- run
  case e of
    Left  err -> hPutStrLn stderr (show err)
    Right res -> output opts res

writeAll :: Options -> [IO (ClassId,MethodId,Either E.SomeException String)] -> IO ()
writeAll opts = mapM_ write'
  where
    write' runM = do
      let Options {
          A.file   = file
        , A.format = format
      } = opts
      (cn,mn,run) <- runM
      case run of
        Left  err -> hPutStrLn stderr (show err)
        Right res -> writeFile (dropExtension file  ++ '-':show cn ++ '-':show mn ++ '.':lower format) res
    dropExtension = takeWhile ('.' /= )
    lower a       = map toLower (show a)

run :: Options -> Program -> P.ClassId -> P.MethodId -> IO (ClassId, MethodId, Either E.SomeException String)
run opts p cn mn = do
  let Options {
      A.file    = file
    , A.cname   = cname
    , A.mname   = mname
    , A.timeout = timeout
    , A.format  = format
    } = opts
  let gM = mkJGraph cn mn :: Jat (MkJGraph SimpleIntDomain String)
      evaluationM = do
        evaluation <- T.timeout timeout $! eval p (runIdentity . evalJat gM $ initJat p) 
        return $ error "timeout" `fromMaybe` evaluation
  res <- E.try evaluationM :: IO (Either E.SomeException String)
  return (cn,mn, res)
  where
    timeouterr = error "timeout"  
    eval p g = case format opts of
      DOT ->  return . dot2String $ mkJGraph2Dot g
      TRS -> undefined

runAll :: Options -> Program -> [IO (ClassId, MethodId, Either E.SomeException String)]
runAll opts p = map (uncurry $ run opts p) (methods p) 

