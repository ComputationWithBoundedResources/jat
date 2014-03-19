{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
-- | This module provides the 'Constraint' type.
module Jat.Constraints
  (
    PATerm
  , PAFun
  , PAVar
  , top
  , isTop
  , bot
  , not
  , add,sub,and,or,gte,eq,neq,ass
  , ufun, int, bool
  , uvar, ivar, bvar
  , mkcon
  , Atom (..)
  , prettyPATerm
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
  | Add
  | Sub
  | Not
  | Or
  | And
  | Gte
  | Eq
  | Neq
  | Ass
  deriving(Show,Eq,Ord)

data PAVar=
    UVar String
  | IVar String
  | BVar String
  deriving (Show,Eq,Ord)

type PATerm = T.Term PAFun PAVar

top :: PATerm
top = T.Fun (BConst True) []

isTop :: PATerm -> Bool
isTop (T.Fun (BConst True) []) = True
isTop _                        = False

bot :: PATerm
bot = T.Fun (BConst False) []

add,sub,and,or,gte,eq,neq,ass :: PATerm -> PATerm -> PATerm
add t1 t2 = T.Fun Add [t1,t2]
sub t1 t2 = T.Fun Sub [t1,t2]
and t1 t2 = T.Fun And [t1,t2]
or t1 t2  = T.Fun And [t1,t2]
gte t1 t2 = T.Fun Gte [t1,t2]
eq t1 t2  = T.Fun Eq [t1,t2]
neq t1 t2 = T.Fun Neq [t1,t2]
ass t1 t2 = T.Fun Neq [t1,t2]

not :: PATerm -> PATerm
not t = T.Fun Not [t]

ufun :: String -> [PATerm] -> PATerm
ufun s = T.Fun (UFun s) 

int :: Int -> PATerm
int i = T.Fun (IConst i) []

bool :: Bool -> PATerm
bool b = T.Fun (BConst b) []

uvar :: String -> PATerm
uvar = T.Var . UVar
  
ivar :: String -> PATerm
ivar = T.Var . IVar

bvar :: String -> PATerm
bvar = T.Var . BVar

instance PP.Pretty PATerm where
  pretty = prettyPATerm

prettyPATerm :: PATerm -> PP.Doc
prettyPATerm (T.Fun f ts) = case f of
  UFun s -> PP.text s <> PP.encloseSep PP.lparen PP.rparen PP.comma [prettyPATerm ti | ti <- ts]
  IConst i 
    | null ts   -> PP.int i 
    | otherwise -> errorx
  BConst b 
    | null ts   -> PP.bool b
    | otherwise -> errorx
  Add    -> binary "+" ts
  Sub    -> binary "-" ts
  Not    -> unary "not" ts
  And    -> binary "&&" ts
  Or     -> binary "||" ts
  Gte    -> binary ">=" ts
  Eq     -> binary "==" ts
  Neq    -> binary "/=" ts
  Ass    -> binary ":=" ts
  where 
    binary s [t1,t2] = PP.parens $ prettyPATerm t1 <+> PP.text s <+> prettyPATerm t2
    binary _ _       = errorx
    unary s [t] = PP.text "not" <> PP.parens (prettyPATerm t)
    unary s _   = errorx
    errorx = error "prettyCTerm: malformed tmer"
prettyPATerm (T.Var v) = case v of
  UVar v -> PP.text v
  IVar v -> PP.char 'i' <> PP.text v
  BVar v -> PP.char 'b' <> PP.text v

-- | Assignment constructor.
mkcon :: (Atom a, Atom b, Atom c) =>
  a -> (PATerm -> PATerm -> PATerm) -> b -> c -> PATerm
mkcon i f j k = T.Fun Ass [atom i, atom j `f` atom k]

-- | Class for defining an atom.
class Atom a where
  atom :: a -> PATerm


{-vars :: Constraint -> [String]-}
{-vars (CVar v)    = [v]-}
{-vars (Not c)     = vars c-}
{-vars (And c1 c2) = vars c1 ++ vars c2-}
{-vars (Or c1 c2)  = vars c1 ++ vars c2-}
{-vars (MAnd c1 c2) = vars c1 ++ vars c2-}
{-vars (MOr c1 c2)  = vars c1 ++ vars c2-}
{-vars (Ass c1 c2) = vars c1 ++ vars c2-}
{-vars (Eq c1 c2)  = vars c1 ++ vars c2-}
{-vars (Neq c1 c2) = vars c1 ++ vars c2-}
{-vars (Gte c1 c2) = vars c1 ++ vars c2-}
{-vars (Add c1 c2) = vars c1 ++ vars c2-}
{-vars (Sub c1 c2) = vars c1 ++ vars c2-}
{-vars _           = []-}

{--- | Map over variables.-}
{-mapvars :: (Constraint -> Constraint) -> Constraint -> Constraint-}
{-mapvars f v@(CVar _) = f v-}
{-mapvars f	(Not c)     = Not $ mapvars f c-}
{-mapvars f	(And c1 c2) = And (mapvars f c1) (mapvars f c2)-}
{-mapvars f	(Or c1 c2)  = Or  (mapvars f c1) (mapvars f c2)-}
{-mapvars f	(MAnd c1 c2) = MAnd (mapvars f c1) (mapvars f c2)-}
{-mapvars f	(MOr c1 c2)  = MOr  (mapvars f c1) (mapvars f c2)-}
{-mapvars f	(Ass c1 c2) = Ass (mapvars f c1) (mapvars f c2)-}
{-mapvars f	(Eq c1 c2)  = Eq  (mapvars f c1) (mapvars f c2)-}
{-mapvars f	(Neq c1 c2) = Neq (mapvars f c1) (mapvars f c2)-}
{-mapvars f	(Gte c1 c2) = Gte (mapvars f c1) (mapvars f c2)-}
{-mapvars f	(Add c1 c2) = Add (mapvars f c1) (mapvars f c2)-}
{-mapvars f	(Sub c1 c2) = Sub (mapvars f c1) (mapvars f c2)-}
{-mapvars _ c           = c-}

{--- | Assignment constructor.-}
{-mkcon :: (Atom a, Atom b, Atom c) => -}
  {-a -> (Constraint -> Constraint -> Constraint) -> b -> c -> Constraint-}
{-mkcon i f j k = atom i `Ass` (atom j `f` atom k)-}

{--- | Class for defining an atom.-}
{-class Atom a where-}
  {-atom :: a -> Constraint-}

{--- | Boolean simmplification.-}
{-[>simplify :: Constraint -> Constraint<]-}
{-[>simplify c@(Not c') = case simplify c' of<]-}
  {-[>BConst True -> bot<]-}
  {-[>BConst False -> top<]-}
  {-[>c'' -> Not c''<]-}
{-[>simplify (And c1 c2) = case (simplify c1, simplify c2) of<]-}
  {-[>(BConst True, BConst True) -> BConst True<]-}
  {-[>(BConst False, _)          -> BConst True<]-}
  {-[>(_, BConst False)          -> BConst True<]-}
  {-[>(c1', c2')                 -> And c1' c2'<]-}
{-[>simplify (Or c1 c2) = case (simplify c1, simplify c2) of<]-}
  {-[>(BConst False, BConst False) -> BConst False<]-}
  {-[>(BConst True, _)          -> BConst True<]-}
  {-[>(_, BConst True)          -> BConst True<]-}
  {-[>(c1', c2')                 -> Or c1' c2'<]-}
{-[>simplify (MAnd c1 c2) = case (simplify c1, simplify c2) of<]-}
  {-[>(BConst True, BConst True) -> BConst True<]-}
  {-[>(BConst False, _)          -> BConst True<]-}
  {-[>(_, BConst False)          -> BConst True<]-}
  {-[>(c1', c2')                 -> MAnd c1' c2'<]-}
{-[>simplify (MOr c1 c2) = case (simplify c1, simplify c2) of<]-}
  {-[>(BConst False, BConst False) -> BConst False<]-}
  {-[>(BConst True, _)          -> BConst True<]-}
  {-[>(_, BConst True)          -> BConst True<]-}
  {-[>(c1', c2')                -> MOr c1' c2'<]-}
{-[>simplify v@(CVar _) = v<]-}
{-[>simplify (Ass c1 c2) = case (simplify c1, simplify c2) of<]-}
  {-[>(BConst True, BConst True)   -> BConst True<]-}
  {-[>(BConst False, BConst False) -> BConst True<]-}
  {-[>(BConst True, BConst False)  -> BConst False<]-}
  {-[>(BConst False, BConst True)  -> BConst False<]-}
  {-[>(c1',c2')                    -> Ass c1' c2'<]-}
{-[>simplify (Eq c1 c2)  = case (simplify c1, simplify c2) of<]-}
  {-[>(BConst True, BConst True) -> BConst True<]-}
  {-[>(BConst False, BConst False) -> BConst True<]-}
  {-[>(BConst True, BConst False) -> BConst False<]-}
  {-[>(BConst False, BConst True) -> BConst False<]-}
  {-[>(c1', c2')<]-}
    {-[>| c1 == c2  -> BConst True<]-}
    {-[>| otherwise -> Eq c1' c2'<]-}
{-[>simplify (Neq c1 c2) = Neq (simplify c1) (simplify c2)<]-}
{-[>simplify (Gte c1 c2) = Gte (simplify c1) (simplify c2)<]-}
{-[>simplify (Add c1 c2) = Add (simplify c1) (simplify c2)<]-}
{-[>simplify (Sub c1 c2) = Sub (simplify c1) (simplify c2)<]-}
{-[>simplify c           = c<]-}
