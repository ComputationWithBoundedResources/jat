-- | This module provides the 'Constraint' type.
module Jat.Constraints
  (
    Constraint (..)
  , top
  , var
  , mkcon
  , Atom (..)
  , mapvars
  , vars
  , simplify
  )
where 

import Jat.Utils.Pretty
import qualified Data.Char as Ch

-- | General 'Constraint' type for Boolean and Integer Arithemtic constraints.
data Constraint =
    CVar String
  | IConst Int
  | BConst Bool

	| Not Constraint
  |	And Constraint Constraint
  |	Or  Constraint Constraint

  -- FIXME: Just a Hack, as constraint format keeps changing 
  |	MAnd Constraint Constraint
  |	MOr  Constraint Constraint

  |	Ass  Constraint Constraint
  |	Eq  Constraint Constraint
	|	Neq Constraint Constraint
	|	Gte Constraint Constraint

  | Add Constraint Constraint
  | Sub Constraint Constraint
	deriving (Show, Eq, Ord)


-- | Top symbol.
top :: Constraint
top = BConst True

-- | Bottom symbol.
bot :: Constraint
bot = BConst False

-- | Variable constructor.
var :: String -> Constraint
var = CVar

vars :: Constraint -> [String]
vars (CVar v)    = [v]
vars (Not c)     = vars c
vars (And c1 c2) = vars c1 ++ vars c2
vars (Or c1 c2)  = vars c1 ++ vars c2
vars (MAnd c1 c2) = vars c1 ++ vars c2
vars (MOr c1 c2)  = vars c1 ++ vars c2
vars (Ass c1 c2) = vars c1 ++ vars c2
vars (Eq c1 c2)  = vars c1 ++ vars c2
vars (Neq c1 c2) = vars c1 ++ vars c2
vars (Gte c1 c2) = vars c1 ++ vars c2
vars (Add c1 c2) = vars c1 ++ vars c2
vars (Sub c1 c2) = vars c1 ++ vars c2
vars _           = []

-- | Map over variables.
mapvars :: (Constraint -> Constraint) -> Constraint -> Constraint
mapvars f v@(CVar _) = f v
mapvars f	(Not c)     = Not $ mapvars f c
mapvars f	(And c1 c2) = And (mapvars f c1) (mapvars f c2)
mapvars f	(Or c1 c2)  = Or  (mapvars f c1) (mapvars f c2)
mapvars f	(MAnd c1 c2) = MAnd (mapvars f c1) (mapvars f c2)
mapvars f	(MOr c1 c2)  = MOr  (mapvars f c1) (mapvars f c2)
mapvars f	(Ass c1 c2) = Ass (mapvars f c1) (mapvars f c2)
mapvars f	(Eq c1 c2)  = Eq  (mapvars f c1) (mapvars f c2)
mapvars f	(Neq c1 c2) = Neq (mapvars f c1) (mapvars f c2)
mapvars f	(Gte c1 c2) = Gte (mapvars f c1) (mapvars f c2)
mapvars f	(Add c1 c2) = Add (mapvars f c1) (mapvars f c2)
mapvars f	(Sub c1 c2) = Sub (mapvars f c1) (mapvars f c2)
mapvars _ c           = c

-- | Assignment constructor.
mkcon :: (Atom a, Atom b, Atom c) => 
  a -> (Constraint -> Constraint -> Constraint) -> b -> c -> Constraint
mkcon i f j k = atom i `Ass` (atom j `f` atom k)

-- | Class for defining an atom.
class Atom a where
  atom :: a -> Constraint

-- | Boolean simmplification.
simplify :: Constraint -> Constraint
simplify c@(Not c') = case simplify c' of
  BConst True -> bot
  BConst False -> top
  c'' -> Not c''
simplify (And c1 c2) = case (simplify c1, simplify c2) of
  (BConst True, BConst True) -> BConst True
  (BConst False, _)          -> BConst True
  (_, BConst False)          -> BConst True
  (c1', c2')                 -> And c1' c2'
simplify (Or c1 c2) = case (simplify c1, simplify c2) of
  (BConst False, BConst False) -> BConst False
  (BConst True, _)          -> BConst True
  (_, BConst True)          -> BConst True
  (c1', c2')                 -> Or c1' c2'
simplify (MAnd c1 c2) = case (simplify c1, simplify c2) of
  (BConst True, BConst True) -> BConst True
  (BConst False, _)          -> BConst True
  (_, BConst False)          -> BConst True
  (c1', c2')                 -> MAnd c1' c2'
simplify (MOr c1 c2) = case (simplify c1, simplify c2) of
  (BConst False, BConst False) -> BConst False
  (BConst True, _)          -> BConst True
  (_, BConst True)          -> BConst True
  (c1', c2')                -> MOr c1' c2'
simplify v@(CVar _) = v
simplify (Ass c1 c2) = case (simplify c1, simplify c2) of
  (BConst True, BConst True)   -> BConst True
  (BConst False, BConst False) -> BConst True
  (BConst True, BConst False)  -> BConst False
  (BConst False, BConst True)  -> BConst False
  (c1',c2')                    -> Ass c1' c2'
simplify (Eq c1 c2)  = case (simplify c1, simplify c2) of
  (BConst True, BConst True) -> BConst True
  (BConst False, BConst False) -> BConst True
  (BConst True, BConst False) -> BConst False
  (BConst False, BConst True) -> BConst False
  (c1', c2')
    | c1 == c2  -> BConst True
    | otherwise -> Eq c1' c2'
simplify (Neq c1 c2) = Neq (simplify c1) (simplify c2)
simplify (Gte c1 c2) = Gte (simplify c1) (simplify c2)
simplify (Add c1 c2) = Add (simplify c1) (simplify c2)
simplify (Sub c1 c2) = Sub (simplify c1) (simplify c2)
simplify c           = c



instance Pretty Constraint where
  pretty con = case con of
    CVar v   -> string v
    IConst i -> int i
    BConst b -> text . map Ch.toLower $ show b


    And l r  -> p l <+> string "&&" <+> p r
    Or  l r  -> p l <+> string "||" <+> p r
    Not a    -> string "not" <> lparen <> p a <> rparen

    MAnd l r -> p l <+> string "/\\" <+> p r
    MOr l r -> p l <+> string "\\/" <+> p r

    Ass  l r  -> p l <+> string "=" <+> p r
    Eq  l r  -> p l <+> string "==" <+> p r
    Neq l r  -> string "not" <> lparen <> p (Eq l r) <> rparen
    Gte l r  -> p l <+> string ">=" <+> p r

    Add l r  -> p l <+> string "+" <+> p r
    Sub l r  -> p l <+> string "-" <+> p r
    where p = pretty

