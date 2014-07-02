{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
-- | This module provides the 'Constraint' type.
module Jat.Constraints
  (
    PATerm
  , PAFun (..)
  , PAVar (..)
  , vmap
  , top
  , bot
  , isTop,isBot
  , not
  , add,sub,and,or,gte,eq,neq,ass
  , ufun, int, bool
  , uvar, ivar, bvar
  , prettyPATerm
  , isVar,isIVar,isBVar
  , isRFun, isIFun, isBFun
  , toDNF
  , pushNot
  , normalise
  {-, simplify-}
  )
where 

import qualified Data.Rewriting.Term as T

import Jat.Utils.Pretty ((<>),(<+>))
import qualified Jat.Utils.Pretty as PP

import Prelude hiding (and,or,not)
import qualified Data.Char as Ch

data PAFun = 
    UFun String
  | IConst Int
  | BConst Bool
  | Add | Sub
  | Not | Or | And
  | Lt | Lte | Gt | Gte
  | Eq | Neq
  | Ass
  deriving(Show,Eq,Ord)

data PAVar =
    UVar String Int
  | IVar String Int
  | BVar String Int
  deriving (Show,Eq,Ord)

isVar,isIVar,isBVar :: PATerm -> Bool
isVar (T.Var _)           = True
isVar _                   = False
isIVar (T.Var (IVar _ _)) = True
isIVar _                  = False
isBVar (T.Var (BVar _ _)) = True
isBVar _                  = False

isRFun,isIFun,isBFun :: PATerm -> Bool
isRFun (T.Fun f _)          = f `elem` [Lt, Lte, Gt, Gte, Eq,Neq]
isRFun _                    = False
isIFun (T.Fun (IConst _) _) = True
isIFun (T.Fun i _)          = i `elem` [Add,Sub]
isIFun  _                   = False
isBFun (T.Fun (BConst _) _) = True
isBFun (T.Fun b _)          = b `elem` [And,Or,Not]
isBFun  _                   = False


vmap :: (Int -> Int) -> PAVar -> PAVar
vmap f (UVar s i) = UVar s (f i)
vmap f (IVar s i) = IVar s (f i)
vmap f (BVar s i) = BVar s (f i)

type PATerm = T.Term PAFun PAVar

top :: PATerm
top = T.Fun (BConst True) []

bot :: PATerm
bot = T.Fun (BConst False) []

isTop :: PATerm -> Bool
isTop (T.Fun (BConst True) []) = True
isTop _                        = False

isBot :: PATerm -> Bool
isBot (T.Fun (BConst False) []) = True
isBot _                         = False

-- only RFuns
toDNF :: PATerm -> [PATerm]
toDNF = distribute . pushNot
  where
    distribute (T.Fun Or ts)  = concatMap distribute ts
    distribute (T.Fun And ts) = [T.Fun And ts' | ts' <- sequence $ map distribute ts]
    distribute t = [t]
    


pushNot :: PATerm -> PATerm
pushNot (T.Fun Not [t]) = pushNot' t where
  pushNot' (T.Fun And ts)  = T.Fun Or $ map pushNot' ts
  pushNot' (T.Fun Or ts)   = T.Fun And $ map pushNot' ts
  pushNot' (T.Fun Not [t]) = t
  pushNot' (T.Fun Lt ts)   = T.Fun Gte ts
  pushNot' (T.Fun Lte ts)  = T.Fun Gt ts
  pushNot' (T.Fun Gte ts)  = T.Fun Lt ts
  pushNot' (T.Fun Gt ts)   = T.Fun Lte ts
  pushNot' (T.Fun Eq ts)   = T.Fun Neq ts
  pushNot' (T.Fun Neq ts)  = T.Fun Eq ts
  pushNot' (T.Fun (BConst True) []) = bot
  pushNot' (T.Fun (BConst False) []) = top
  pushNot' v@(T.Var b) = T.Fun Not [v]
pushNot (T.Fun And ts) = T.Fun And (map pushNot ts)
pushNot (T.Fun Or ts)  = T.Fun Or (map pushNot ts)
pushNot t = t

normalise :: PATerm -> PATerm
normalise = ineq . lhs
  where
    lhs c@(T.Fun f [t1@(T.Fun _ _),t2@(T.Var _)])
      | isRFun c = T.Fun (revf f) [t2,t1]
    lhs t = t
    ineq (T.Fun Gt [t1,t2]) = gte t1 (add t2 $ int 1)
    ineq (T.Fun Lt [t1,t2]) = T.Fun Lte  [t1,(sub t2 $ int 1)]
    ineq t = t
    revf Lt = Gt
    revf Gt = Lt
    revf Lte = Gte
    revf Gte = Lte
    revf f = f

add,sub,and,or,gte,eq,neq,ass :: PATerm -> PATerm -> PATerm
add t1 t2 = T.Fun Add [t1,t2]
sub t1 t2 = T.Fun Sub [t1,t2]
and t1 t2 = T.Fun And [t1,t2]
or t1 t2  = T.Fun Or [t1,t2]
gte t1 t2 = T.Fun Gte [t1,t2]
eq t1 t2  = T.Fun Eq [t1,t2]
neq t1 t2 = T.Fun Neq [t1,t2]
ass t1 t2 = T.Fun Ass [t1,t2]

not :: PATerm -> PATerm
not t = T.Fun Not [t]

ufun :: String -> [PATerm] -> PATerm
ufun = T.Fun . UFun

int :: Int -> PATerm
int i = T.Fun (IConst i) []

bool :: Bool -> PATerm
bool b = T.Fun (BConst b) []

uvar :: String -> Int -> PATerm
uvar s = T.Var . UVar s
  
ivar :: String -> Int -> PATerm
ivar s = T.Var . IVar s

bvar :: String -> Int -> PATerm
bvar s = T.Var . BVar s

instance PP.Pretty PATerm where
  pretty = prettyPATerm

prettyPATerm :: PATerm -> PP.Doc
prettyPATerm (T.Fun f ts) = case f of
  UFun s -> PP.text s <> args ts where
    args ts = PP.encloseSep PP.lparen PP.rparen PP.comma [prettyPATerm ti | ti <- ts]
  IConst i 
    | null ts   -> PP.int i 
    | otherwise -> errorx
  BConst b 
    | null ts   -> PP.bool b
    | otherwise -> errorx
  Add -> binary "+" ts
  Sub -> binary "-" ts
  Not -> unary "not" ts
  And -> binary "&&" ts
  Or  -> binary "||" ts
  Lt  -> binary "<" ts
  Lte -> binary "=<" ts
  Gte -> binary ">=" ts
  Gt  -> binary ">" ts
  Eq  -> binary "==" ts
  Neq -> binary "/=" ts
  Ass -> binary ":=" ts
  where 
    binary s [t1,t2] = PP.parens $ prettyPATerm t1 <+> PP.text s <+> prettyPATerm t2
    binary _ _       = errorx
    unary s [t] = PP.text "not" <> PP.parens (prettyPATerm t)
    unary s _   = errorx
    errorx = error "prettyCTerm: malformed tmer"
prettyPATerm (T.Var v) = case v of
  UVar s i -> PP.text s <> PP.int i
  IVar s i -> PP.char 'i' <> PP.text s <> PP.int i
  BVar s i -> PP.char 'b' <> PP.text s <> PP.int i

