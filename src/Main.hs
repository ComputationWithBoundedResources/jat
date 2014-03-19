-- | The main module.
module Main (
    main
) where

import Jat.CompGraph
import Jat.JatM
import Jat.PState
import Jat.Utils.Args
import Jat.Utils.Dot
import Jat.Utils.Pretty
import Jat.Utils.TRS
import Jinja.Program as P

import Control.Monad.Identity (runIdentity)
import Data.Char (toLower)
import Data.Maybe (fromMaybe)
import System.IO
import qualified Control.Exception as E
import qualified System.Timeout as T

-- | Parse arguments and start the program
main ::  IO ()
main = do
  opts <- parseArgs
  let Options {
      file  = file'
    , cname = cname'
    , mname = mname'
    } = opts
  pM <- readFile file'
  let p = P.parseProgram pM
  case (cname',mname') of
    (Just cn, Just mn) -> writeOne opts $ run opts p (P.ClassId cn) (P.MethodId mn)
    _                  -> writeAll opts $ runAll opts p
    

writeOne :: Options -> IO (ClassId,MethodId, Either E.SomeException String) -> IO ()
writeOne opts therun = do
  (_,_,e) <- therun 
  case e of
    Left  err -> hPrint stderr (show err)
    Right res -> output opts res

writeAll :: Options -> [IO (ClassId,MethodId,Either E.SomeException String)] -> IO ()
writeAll opts = mapM_ write'
  where
    write' runM = do
      let Options {
          file   = file'
        , format = format'
      } = opts
      (cn,mn,therun) <- runM
      case therun of
        Left  err -> hPrint stderr (show err)
        Right res -> writeFile (dropExtension file'  ++ '-':(show .pretty $ cn) ++ '-':(show . pretty $ mn) ++ '.':lower format') res
    dropExtension = takeWhile ('.' /= )
    lower a       = map toLower (show a)

run :: Options -> Program -> P.ClassId -> P.MethodId -> IO (ClassId, MethodId, Either E.SomeException String)
run opts p cn mn =
  let Options {
      timeout     = timeout'
    , interactive = interactive'
    } = opts
  in 
  if interactive'
    then do
      let 
        evaluationM = case domain opts of
          Sharing   -> let gM =  mkJGraphIO cn mn :: JatM IO (MkJGraph SignedIntDomain PairSharing)
                      in (dot2String . mkJGraph2Dot) `liftM` evalJat gM (initJat p)
          UnSharing -> let gM = mkJGraphIO cn mn :: JatM IO (MkJGraph SignedIntDomain UnSharing)
                      in (dot2String . mkJGraph2Dot) `liftM` evalJat gM (initJat p) 
      res <- E.try evaluationM :: IO (Either E.SomeException String)
      return (cn,mn, res)
    else do
    let 
      evalM = case domain opts of
        {-Sharing   -> theOutput opts p (mkJGraph cn mn :: Jat (MkJGraph SignedIntDomain PairSharing))-}
        Sharing   -> theOutput opts p (mkJGraph cn mn :: Jat (MkJGraph SignedIntDomain PairSharing))
        UnSharing -> theOutput opts p (mkJGraph cn mn :: Jat (MkJGraph SignedIntDomain UnSharing))
      evaluationM = do
        evaluation2 <- T.timeout timeout' $! (E.evaluate . runIdentity $ evalJat evalM ( initJat p))
        E.evaluate $ error "timeout" `fromMaybe` evaluation2
    res <- E.try evaluationM :: IO (Either E.SomeException String)
    return (cn,mn, res)

theOutput :: (Monad m, IntDomain i, MemoryModel a) => Options -> P.Program -> JatM m (MkJGraph i a) -> JatM m String 
theOutput opts p gM =
  let (simpGr,simpTRS) = 
          case simplify opts of
            WithNarrowing       -> (id, simplifyRHS . simplifyRHS . simplifyRHS)
            WithNarrowingAndSCC -> (simplifySCC, simplifyRHS)
            _                   -> (id, id)
  in
  case format opts of
    DOT  -> (dot2String . mkJGraph2Dot . simpGr) `liftM` gM 
    TRS  -> (display . prettyTRS . normaliseCTRS . simpTRS)      `liftM` (gM >>= mkJGraph2TRS . simpGr)
    ITRS -> (display . prettyITRS . toITRS . simpTRS)      `liftM` (gM >>= mkJGraph2TRS . simpGr)
    CTRS -> (display . prettyCTRS . toCTRS . simpTRS)      `liftM` (gM >>= mkJGraph2TRS . simpGr)
    PRG  -> return (display $ pretty p)

runAll :: Options -> Program -> [IO (ClassId, MethodId, Either E.SomeException String)]
runAll opts p = map (uncurry $ run opts p) (methods p) 

