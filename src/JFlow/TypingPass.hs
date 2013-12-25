{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE EmptyDataDecls #-}
module Jsat.TypingPass where

import Jsat.SemiLattice
{-import Jsat.Flow-}
import Jsat.Program
import Jsat.Q

import Data.Sequence (Seq,(<|))
import qualified Data.Sequence as Seq hiding (Seq)
import Control.Monad.Reader hiding (join)
import Data.Maybe (fromJust)
import Text.PrettyPrint.ANSI.Leijen ((<>),(<+>))
import qualified Text.PrettyPrint.ANSI.Leijen as P

import Data.Foldable as F (foldr)
import Debug.Trace

data TypingLattice
newtype TypingFact = WTFact (Seq Type, Seq Type) deriving (Eq,Ord)

instance SemiLattice TypingLattice where
  data Val = TypingFact
  name     = tyName
  bot      = tyBot
  join     = tyJoin

tyName :: TypingLattice String
tyName = "WellTyping"

tyBot :: TypingFact
tyBot = WTFact (Seq.empty,Seq.empty)

tyJoin :: Q -> TypingFact -> TypingFact -> TypingFact
tyJoin q =  wtJoin' (qprogram q)
  where
    wtJoin' p (WTFact(st1,lt1)) (WTFact(st2,lt2)) = WTFact (st3,lt3)
      where
        st3 = Seq.zipWith joinTypes st1 st2
        lt3 = Seq.zipWith joinTypes lt1 lt2
        joinTypes (NullType) (RefType cn)     = RefType cn
        joinTypes (RefType cn) (NullType)     = RefType cn
        joinTypes (RefType cn1) (RefType cn2) = RefType (theLeastCommonSupClass p cn1 cn2)
        joinTypes ty1 ty2 | ty1 == ty2        = ty1
                          | otherwise         = error $ "welltyping.join: p not wellfounded: " ++ show (ty1,ty2)



{-instance Show TypingFact where-}
  {-show (WTFact (tys1, tys2)) = show $ P.lparen <+> ppTys tys2 <+> P.char '|' <+> ppTys tys1 <+> P.rparen-}
    {-where -}
      {-ppTys :: Seq Type -> P.Doc-}
      {-ppTys tys = P.string . show $ F.foldr (:) [] tys-}

{-wtFlow :: FwdFlow WellTypingFact-}
{-wtFlow = FwdFlow wtSemiLattice wtFwdTransfer-}


{-wtSemiLattice :: SemiLattice WellTypingFact-}
{-wtSemiLattice = SemiLattice wtName wtBot wtJoin-}

{-wtFwdTransfer :: FwdTransfer WellTypingFact-}
{-wtFwdTransfer = FwdTransfer $ \q -> wtFwdTransfer' (qprogram q)-}
  {-where-}
    {-wtFwdTransfer' :: Program -> Instruction -> WellTypingFact -> WellTypingFact-}
    {-wtFwdTransfer' _ ins v | trace (">>> wtFwdTransfer'" ++ show (ins,v)) False = undefined-}
    {-wtFwdTransfer' p ins (WTFact (st,lt)) = WTFact $ case ins of-}
      {-Load i         -> (index' lt i <| st,lt)-}
      {-Store i        -> let (ty,st') = heads st in  (st', Seq.adjust (const ty) i lt)-}
      {-Push v         -> (fromJust (typeOf v) <| st, lt)-}
      {-New cn         -> (RefType cn <| st,lt)-}
      {-GetField fn cn -> ((snd . fromJust $ field p cn fn)  <| pop st,lt)-}
      {-PutField _  _  -> (pop2 st,lt)-}
      {-CheckCast cn   -> (RefType cn <| pop st,lt)-}
      {-Pop            -> (pop st,lt)-}
      {-IAdd           -> (IntType <| pop2 st,lt)-}
      {-ISub           -> (IntType <| pop2 st,lt)-}
      {-Goto _         -> (st,lt)-}
      {-IfFalse _      -> (pop st,lt)-}
      {-CmpEq          -> (BoolType <| pop2 st,lt)-}
      {-CmpNeq         -> (BoolType <| pop2 st,lt)-}
      {-ICmpGeq        -> (BoolType <| pop2 st,lt)-}
      {-BNot           -> (BoolType <| pop2 st,lt)-}
      {-BAnd           -> (BoolType <| pop2 st,lt)-}
      {-BOr            -> (BoolType <| pop2 st,lt)-}
      {-Return         -> (st,lt)-}
      {-Invoke  mn n   -> (retty <| Seq.drop (n+1) st, lt)-}
        {-where-}
          {-retty = case Seq.index st n of-}
                    {-RefType cn -> methodReturn $ theMethod p cn mn-}
                    {-ty ->  error $ "welltyping.wtFwdTransfer: unexpected typ" ++ show ty-}
    {-pop :: Seq a -> Seq a-}
    {-pop = Seq.drop 1-}
    {-pop2 :: Seq a -> Seq a-}
    {-pop2 = Seq.drop 2-}
    {-heads :: Seq a -> (a, Seq a)-}
    {-heads s = let (aS,s') = Seq.splitAt 1 s in (Seq.index aS 0, s')-}
    {-index' :: Show a => Seq a -> Int -> a-}
    {-index' seq i = if i > Seq.length seq then error $ "unexpected index?" ++ show (seq,i) else Seq.index seq i-}
  


