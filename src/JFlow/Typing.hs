-- | The typing Domain provides typing information for local variables and
-- operand stack. This analysis is necessary to provide a (upper) static type
-- for method invocations.
module JFlow.Typing 
  (
    TypingFact
  , tyFlow
  , vars
  , hasIndex
  , hasType
  )
where

import Prelude hiding ((<$>))
import Jat.Utils.Pretty

import JFlow.Data
import JFlow.Utility (safeZipWith)

import Jinja.Program

import Data.Maybe (fromMaybe)


-- Notes:
-- domain is based on the WellTyping verifier of Jinja
-- the implementation may fail with non-wellformed bytecode program
-- the number of local variables is known for each method, whereas only the
-- maximum of the stack size is known

-- why are they not exported
type LocVars = [[Type]]
type StkVars = [[Type]]
data TypingFact = TyFact !Int !Int LocVars StkVars deriving (Eq,Ord)

vars :: TypingFact -> [Var]
vars (TyFact _ _ lss sss) = lvars ++ svars
  where
    lvars = [LocVar i j | (i, ls) <- zip [0..] (reverse lss), (j, _) <- zip [0..] ls]
    svars = [StkVar i j | (i, ss) <- zip [0..] (reverse sss), (j, _) <- zip [0..] (reverse ss)]

instance Pretty TypingFact where
  pretty (TyFact i j locs stks) =
    string "TyFact"
    <$> tupled [int i,int j]
    <$> vsep (zipWith k locs stks)
    where  k l s = list (map pretty l) <+> char '|' <+> list (reverse $ map pretty s)

instance Show TypingFact where
  show = show . pretty

tyFlow :: Flow TypingFact w
tyFlow = Flow tyLattice tyTransfer

tyBot :: TypingFact
tyBot = TyFact (-1) (-1) [[]] [[]]

tyLattice :: SemiLattice TypingFact
tyLattice = SemiLattice tyName tyBot tyJoin
  where
    tyName = "TypingFact"

    tyJoin _ v1 v2  
      | v1 == tyBot = v2
      | v2 == tyBot = v1

    {-tyJoin _ tyf1 tyf2 | trace ("Typing.join:" ++ show (tyf1,tyf2)) False = undefined-}
    tyJoin _ (TyFact i1 j1 _ _) (TyFact i2 j2 _ _)  
      | i1 /= i2 || j1 /= j2 = error "Typing.join: index error"
    tyJoin p (TyFact i1 j1 locs1 stks1) (TyFact _ _ locs2 stks2) = 
      TyFact i1 j1 (locs1 `zips` locs2) (stks1 `zips` stks2)
      where
        zips = safeZipWith (safeZipWith joinTypes)
        joinTypes (NullType) (RefType cn)     = RefType cn
        joinTypes (RefType cn) (NullType)     = RefType cn
        joinTypes (RefType cn1) (RefType cn2) = RefType (theLeastCommonSupClass p cn1 cn2)
        joinTypes (Void) ty                   = ty
        joinTypes ty (Void)                   = ty
        joinTypes ty1 ty2 
          | ty1 == ty2 = ty1
          | otherwise  = error $ "Typing.join: p not wellformed: " ++ show (ty1,ty2)

tyTransfer :: Transfer TypingFact w
tyTransfer = Transfer tyTransferf tySetup tyProject tyExtend
  where
    set 0 y (_:xs) = y: xs
    set n y (x:xs) = x: set (n-1) y xs
    set _ _ _      = error "JFlow.Typing.set:the impossible happened"
    pop (_:xs)    = xs
    pop _         = error "JFlow.Typing.pop: the impossible happened"
    pop2 (_:_:xs) = xs
    pop2 _        = error "JFlow.Typing.pop2: the impossible happened"
    popx (x:xs)   = (x,xs)
    popx _        = error "JFlow.Typing.popx: the impossible happened"
    push = (:) 
    
    {-tyTransferf p _ ins _ tyf | trace (show tyf ++ "\n" ++ show ins) False = undefined-}
    tyTransferf p _ ins _ (TyFact i j (loc:locs) (stk:stks)) = 
      let (j',loc',stk') = tyTransferf' p j loc stk ins
      in  TyFact i j' (loc':locs) (stk':stks)
    tyTransferf _ _ ins _ tyf = error $ show ins ++ show tyf
    tyTransferf' p j loc stk ins = case ins of
      Load i         -> (j+1,loc, lookup' loc i `push` stk)
      Store i        -> let (ty,stk') = popx stk
                       in  (j-1,set i ty loc, stk')
      Push v         -> (j+1,loc, fromMaybe err (typeOf v) `push` stk)
        where err = error "Typing.Push: could not deduce type"
      New cn         -> (j+1,loc, RefType cn `push` stk)
      GetField fn cn -> (j,loc, snd (field p cn fn) `push` pop stk)
      PutField _  _  -> (j-2,loc, pop2 stk)
      CheckCast cn   -> (j,loc, RefType cn `push` pop stk)
      Pop            -> (j-1,loc, pop stk)
      IAdd           -> (j-1,loc, IntType `push` pop2 stk)
      ISub           -> (j-1,loc, IntType `push` pop2 stk)
      Goto _         -> (j,loc, stk)
      IfFalse _      -> (j-1,loc, pop stk)
      CmpEq          -> (j-1,loc, BoolType `push` pop2 stk)
      CmpNeq         -> (j-1,loc, BoolType `push` pop2 stk)
      ICmpGeq        -> (j-1,loc, BoolType `push` pop2 stk)
      BNot           -> (j,loc, BoolType `push` pop  stk)
      BAnd           -> (j-1,loc, BoolType `push` pop2 stk)
      BOr            -> (j-1,loc, BoolType `push` pop2 stk)
      Return         -> undefined
      Invoke  _ _    -> undefined


    tySetup p cn mn = TyFact 0 (-1) [this:params++locals] [[]]
      where
        md     = theMethod p cn mn
        this   = RefType cn
        params = methodParams md
        locals = replicate (maxLoc md) Void
        
    --tyProject p cn mn nparams _ (TyFact i _ locs (stk:stks)) | traceShow (stk:stks) False = undefined
    tyProject p cn mn nparams _ (TyFact i _ locs (stk:stks)) =
      TyFact (i+1) (-1) ((this:params++locals):locs) ([]:stk':stks)
      where
        this       = RefType cn
        (tys,stk') = splitAt (nparams+1) stk
        (_:params) = reverse tys
        locals     = replicate (maxLoc $ theMethod p cn mn) Void
    tyProject _ _ _ _ _ _ = error "Typing.tyProject: unexpected error"
        
    tyExtend _ _ nparams _ (TyFact i _ locs1 (stk1:stks1)) v2@(TyFact _ _ _ stks2) =
      TyFact i (length rstk - 1) locs1 (rstk:stks1)
      where 
        rstk = ret: drop (nparams+1) stk1
        ret  = if v2 == tyBot then Void else head (head stks2)
    tyExtend _ _ _ _ _ _ = error "Typing.tyExtend: unexpected error"


lookup' :: [a] -> Int -> a
lookup' (x:_) 0  = x
lookup' (_:xs) i = lookup' xs (i-1)
lookup' _ i      = error $ "Typing.lookup" ++ show i


hasIndex :: TypingFact -> (Int,Int)
hasIndex (TyFact i j _ _)                = (i,j)

hasType :: TypingFact -> Var -> Type
hasType (TyFact _ _ locs _) (LocVar i j) = (reverse locs `lookup'` i) `lookup'` j
hasType (TyFact _ _ _ stks) (StkVar i j) = reverse (reverse stks `lookup'` i) `lookup'` j

instance HasIndexQ TypingFact where
  hasIndexQ = hasIndex

instance HasTypeQ TypingFact where
  hasTypeQ = hasType

