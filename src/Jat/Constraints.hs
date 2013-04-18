-- | This module provides the 'Constraint' type.
module Jat.Constraints
  (
    Constraint (..)
  , top
  , var
  , mkcon
  , Atom (..)
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

    Ass  l r  -> p l <+> string ":=" <+> p r
    Eq  l r  -> p l <+> string "==" <+> p r
    Neq l r  -> p l <+> string "/=" <+> p r
    Gte l r  -> p l <+> string ">=" <+> p r

    Add l r  -> p l <+> string "+" <+> p r
    Sub l r  -> p l <+> string "-" <+> p r
    where p = pretty

