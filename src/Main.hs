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

import System.IO
import qualified System.Timeout as T
import qualified Control.Exception as E
import Data.Char (toLower)
import Control.Monad.Identity (runIdentity)
import Data.Maybe (fromMaybe)



main ::  IO ()
main = do
  opts <- parseArgs
  let Options {
      A.file        = file
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
    Left  err -> hPrint stderr (show err)
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
        Left  err -> hPrint stderr (show err)
        Right res -> writeFile (dropExtension file  ++ '-':(show .pretty $ cn) ++ '-':(show . pretty $ mn) ++ '.':lower format) res
    dropExtension = takeWhile ('.' /= )
    lower a       = map toLower (show a)

run :: Options -> Program -> P.ClassId -> P.MethodId -> IO (ClassId, MethodId, Either E.SomeException String)
run opts p cn mn =
  let Options {
      A.timeout     = timeout
    , A.interactive = interactive
    } = opts
  in 
  if interactive 
    then do
      --let gM = mkJGraphIO cn mn :: JatM IO (MkJGraph SimpleIntDomain Primitive)
      let gM = mkJGraphIO cn mn :: JatM IO (MkJGraph SimpleIntDomain UnSharing)
          evaluationM = eval p (evalJat gM $ initJat p) 
      res <- E.try evaluationM :: IO (Either E.SomeException String)
      return (cn,mn, res)
    else do
    let gM = mkJGraph cn mn :: Jat (MkJGraph SimpleIntDomain UnSharing)
    --let gM = mkJGraph cn mn :: Jat (MkJGraph SimpleIntDomain Primitive)
        evaluationM = do
          evaluation <- T.timeout timeout $! (E.evaluate . runIdentity $ (eval p . evalJat gM $ initJat p))
          E.evaluate $ error "timeout" `fromMaybe` evaluation
    res <- E.try evaluationM :: IO (Either E.SomeException String)
    return (cn,mn, res)
  where
    eval _ g = case format opts of
      DOT -> (dot2String . mkJGraph2Dot) `liftM` g
      TRS -> error "TRS: yet not defined"

runAll :: Options -> Program -> [IO (ClassId, MethodId, Either E.SomeException String)]
runAll opts p = map (uncurry $ run opts p) (methods p) 
