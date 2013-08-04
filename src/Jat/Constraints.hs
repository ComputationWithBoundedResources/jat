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
  )
where 

import Jat.Utils.Pretty

-- | General 'Constraint' type for Boolean and Integer Arithemtic constraints.
data Constraint =
    CVar String
  | IConst Int
  | BConst Bool

	| Not Constraint
  |	And Constraint Constraint
  |	Or  Constraint Constraint

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

-- | Variable constructor.
var :: String -> Constraint
var = CVar

vars :: Constraint -> [String]
vars (CVar v)    = [v]
vars (Not c)     = vars c
vars (And c1 c2) = vars c1 ++ vars c2
vars (Or c1 c2)  = vars c1 ++ vars c2
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

instance Pretty Constraint where
  pretty con = case con of
    CVar v   -> string v
    IConst i -> int i
    BConst b -> bool b

    And l r  -> p l <+> string "&&" <+> p r
    Or  l r  -> p l <+> string "||" <+> p r
    Not a    -> string "!" <> p a

    Ass  l r  -> p l <+> string "=" <+> p r
    Eq  l r  -> p l <+> string "==" <+> p r
    Neq l r  -> p l <+> string "!=" <+> p r
    Gte l r  -> p l <+> string ">=" <+> p r

    Add l r  -> p l <+> string "+" <+> p r
    Sub l r  -> p l <+> string "-" <+> p r
    where p = pretty

