-- | The typing Domain provides typing information for local variables and
-- operand stack. This analysis is necessary to provide a (upper) static type
-- for method invocations.
module Jsat.Typing where

import Jsat.Data
import Jsat.Utility (safeZipWith)
import Jat.Program as P

import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Maybe (fromJust)
import Text.PrettyPrint.ANSI.Leijen ((<+>),(<>))
import qualified Text.PrettyPrint.ANSI.Leijen as P
import qualified Data.Foldable as F

import Debug.Trace

-- Notes:
-- domain is based on the WellTyping verifier of Jinja
-- the implementation may fail with non-wellformed bytecode program
-- the number of local variables is known for each method, whereas only the
-- maximum of the stack size is known

newtype TypingFact = TyFact (Seq Type, [Type]) deriving (Eq,Ord)

instance Show TypingFact where
  show (TyFact (loc,stk)) = show $
    P.string "TyFact" 
    <+> P.lparen <> ppTys loc <+> P.char '|' 
    <+> P.string (show $ map showType stk) 
    <+> P.string "||" <+> P.int (length stk) <> P.rparen
    where ppTys tys = P.string . show $ map showType (seqToList tys)

showType :: Type -> String
showType BoolType               = "Bool"
showType IntType                = "Int"
showType (RefType (ClassId cn)) = cn
showType NullType               = "Null"
showType Void                   = "Void"


seqToList :: Seq a -> [a]
seqToList = F.foldr (:) []


tyFlow :: Flow TypingFact
tyFlow = Flow tyLattice tyTransfer tyQueryV

tyBot :: TypingFact
tyBot = TyFact (Seq.empty,[])

index' :: Show a => Seq a -> Int -> a
index' sq i = 
  if i >= Seq.length sq 
    then error $ "unexpected index?" ++ show (sq,i) 
    else Seq.index sq i

tyLattice :: SemiLattice TypingFact
tyLattice = SemiLattice tyName tyBot tyJoin
  where
    tyName = "TypingFact"

    tyJoin _ v1 v2 | trace ("tyJoin: " ++ show (v1,v2)) False = undefined
    tyJoin _ v1 v2  | v1 == tyBot = v2
                    | v2 == tyBot = v1

    tyJoin p (TyFact(loc1,stk1)) (TyFact(loc2,stk2)) = 
      TyFact (Seq.zipWith joinTypes loc1 loc2, safeZipWith joinTypes stk1 stk2)
      where
        -- void (unit) as bot element
        joinTypes (NullType) (RefType cn)     = RefType cn
        joinTypes (RefType cn) (NullType)     = RefType cn
        joinTypes (RefType cn1) (RefType cn2) = RefType (theLeastCommonSupClass p cn1 cn2)
        joinTypes (Void) ty                   = ty
        joinTypes ty (Void)                   = ty
        joinTypes ty1 ty2 
          | ty1 == ty2  = ty1
          | otherwise   = error $ "Typing.join: p not wellformed: " ++ show (ty1,ty2)

tyTransfer :: Transfer TypingFact
tyTransfer = Transfer tyTransferf tySetup tyProject tyExtend
  where
    tyTransferf p _ ins (TyFact tys@(loc,_)) = TyFact $ case ins of
      Load i         -> push (index' loc i) tys
      Store i        -> let (ty,stk') = pop tys in  (Seq.adjust (const ty) i loc,stk')
      Push v         -> push (fromJust $ P.typeOf v) tys
      New cn         -> push (RefType cn) tys
      GetField fn cn -> push (snd . fromJust $ field p cn fn) $ rear tys
      PutField _  _  -> rear2 tys
      CheckCast cn   -> push (RefType cn) $ rear tys
      Pop            -> rear tys
      IAdd           -> push IntType $ rear2 tys
      ISub           -> push IntType $ rear2 tys
      Goto _         -> tys
      IfFalse _      -> rear tys
      CmpEq          -> push BoolType $ rear2 tys 
      CmpNeq         -> push BoolType $ rear2 tys
      ICmpGeq        -> push BoolType $ rear2 tys
      BNot           -> push BoolType $ rear  tys
      BAnd           -> push BoolType $ rear2 tys
      BOr            -> push BoolType $ rear2 tys
      Return         -> undefined
      Invoke  _ _    -> undefined

    rear (a,_:xs)  = (a,xs)
    rear (_,[])    = error "Typing.rear: empty stack"
    rear2          = rear . rear
    pop (_,x:xs)   = (x,xs)
    pop (_,[])     = error "Typing.pop: empty stack"
    push ty (a,xs) = (a,ty:xs)


    tySetup p cn mn = TyFact (Seq.fromList $ this:params++locs, [])
      where
        md     = theMethod p cn mn
        this   = RefType cn
        params = methodParams md
        locs   = replicate (maxLoc md) Void
        
    tyProject p _  cn mn nparams (TyFact (_,stk)) = 
      TyFact (Seq.fromList $ this:params++locs,[])
      where
        this   = RefType cn
        params = reverse $ take nparams stk
        locs   = replicate (maxLoc $ theMethod p cn mn) Void

    tyExtend _ _ _ nparams (TyFact (loc1,stk1)) v2@(TyFact (_,stk2)) = 
      TyFact (loc1,stk3)
      where
        ret  = if v2 == tyBot then Void else head stk2
        stk3 = ret : drop (nparams + 1) stk1


tyQueryV :: QueryV TypingFact
tyQueryV = defaultQueryV {hasType = tyHasType} 
  where
    tyHasType (TyFact (loc,_)) (LocVar i) = Just $ index' loc i
    tyHasType (TyFact (_,stk)) (StkVar i) = Just $ stk !! i

