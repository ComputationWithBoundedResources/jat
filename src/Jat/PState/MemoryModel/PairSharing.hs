module Jat.PState.MemoryModel.PairSharing



type NShares = PS.PairSet Address
type MShares = PS.PairSet Var
type TreeShs = S.Set Var

data Sharing = Sh !Int !Int NShares MShares TreeShs 

data Annot = Address :/=: Address | Var :><: Var |  TS Var

instance Pretty Annot where
  pretty (q:/=:r) = int q <> text "/=" <> int r
  pretty (q:><:r) = pretty q <> text "><" <> pretty r
  pretty (TS q)   = char '^' <> pretty q

nShares :: Sharing -> NShares
nShares (Sh _ _ ns _ _) = ns

mShares :: Sharing -> MShares
mShares (Sh _ _ _ ms _) = ms

treeShs :: Sharing -> TreeShs
treeShs (Sh _ _ _ _ ts) = ts

nShares' :: Sharing -> [Annot]
nShares' (Sh _ _ ns _ _) = uncurry (:/=:) `map` PS.elems ns

mShares' :: Sharing -> [Annot]
mShares' (Sh _ _ _ ms _) = uncurry (:><:) `map` PS.elems ms

treeShs' :: Sharing -> [Annot]
treeShs' (Sh _ _ _ _ ts) = TS `map` S.elems ts 

liftNS :: (NShares -> NShares) -> Sharing -> Sharing
liftNS f (Sh i j ns ms ts) = Sh i j (f ns) ms ts

liftMS :: (MShares -> MShares) -> Sharing -> Sharing
liftMS f (Sh i j ns ms ts) = Sh i j ns (f ms) ts

liftTS :: (TreeShs -> TreeShs) -> Sharing -> Sharing
liftTS f (Sh i j ns ms ts) = Sh i j ns ms (f ts)

insertSh :: Annot -> Sharing -> Sharing
insertSh (q:/=:r) = liftNS (PS.insert (q,r))
insertSh (q:><:r) = liftMS (PS.insert (q,r))
insertSh (TS q)   = liftTS (S.insert q)

insertsSh :: [Annot] -> Sharing -> Sharing
insertsSh = flip (foldr insertSh)

deleteSh :: Annot -> Sharing -> Sharing
deleteSh (q:/=:r) = liftNS (PS.delete (q,r))
deleteSh (q:><:r) = liftMS (PS.delete (q,r))
deleteSh (TS q)   = liftTS (S.delete q)

unionMS :: Sharing -> Sharing -> Sharing
unionMS sh1 sh2 = (mShares sh1 `PS.union`) `liftMS` sh2

unionTS :: Sharing -> Sharing -> Sharing
unionTS sh1 sh2 = (treeShs sh1 `S.union`) `liftTS` sh2

unionSh :: Sharing -> Sharing -> Sharing
unionSh (Sh i j ns1 ms1 ts1) (Sh _ _ ns2 ms2 ts2) = Sh i j ns3 ms3 ts3
  where
    ns3 = ns1 `PS.union` ns2
    ms3 = ms1 `PS.union` ms2
    ts3 = ts1 `S.union`  ts2

memberSh :: Annot -> Sharing -> Bool
memberSh a (Sh _ _ ns ms ts) = case a of
  (q:/=:r) -> PS.member (q,r) ns
  (q:><:r) -> PS.member (q,r) ms
  (TS q)   -> S.member q ts

emptySh :: Int -> Int -> Sharing
emptySh i j = Sh i j PS.empty PS.empty S.empty

instance Pretty Sharing where
  pretty sh =
    (hsep . map pretty $ nShares' sh)
    <$> (hsep . map pretty $ mShares' sh)
    <$> (hsep . map pretty $ treeShs' sh)

type Sh i = PState i Sharing

sharing :: Sh i -> Sharing
sharing (PState _ _ sh) = sh

tyOf :: P.Program -> Sh i -> Address -> P.Type
tyOf p st q = P.RefType . className $ lookupH q (heap st)

maybeShares :: P.Program -> Sh i -> Address -> Address -> Bool
maybeShares p st q r = 
  P.areSharingTypes p (tyOf p st q) (tyOf p st r) && 
  maybeSharesSh p st q r

maybeSharesSh :: P.Program -> Sh i -> Address -> Address -> Bool
maybeSharesSh p st q r = any shares (mShares' $ sharing st)
  where 
    shares (v:><:w) = 
      (q `elem` vReaches && r `elem` wReaches) || 
      (q `elem` wReaches && r `elem` vReaches)
      where
        vReaches = reachableFS v st
        wReaches = reachableFS w st

treeShapedSh :: P.Program -> Sh i -> Address -> Bool
treeShapedSh p st q = any k (treeShs' $ sharing st)
  where k (TS v) = q `elem` reachableFS v st

treeShaped :: P.Program -> Sh i -> Address -> Bool
treeShaped p st q = 
  P.isTreeShapedType p (tyOf p st q) ||
  treeShapedSh p st q
  
unShare :: P.Program -> [Address] -> [Address] -> Sh i -> Sh i
unShare p qs rs st@(PState hp frms sh) = 
  PState hp frms (insertsSh elems sh)
  where 
    elems       = [ q:/=:r | q <- qs, r <- rs, q /= r, related q r ]
    ty          = tyOf p st
    related q r = P.areRelatedTypes p (ty q) (ty r)

nullify = undefined
substituteSh = undefined

assignSh :: Var -> Var -> Sharing -> Sharing
assignSh v w = assignTS v w .assignMS v w

assignMS :: Var -> Var -> Sharing -> Sharing
assignMS v w sh
  | w:><:w `memberSh` sh =  (v:><:w `insertSh` sh') `unionMS` (PS.rename [(v,w)] `liftMS` sh')
  | otherwise            = sh'
  where sh' = PS.delete' v `liftMS` sh

assignTS :: Var -> Var -> Sharing -> Sharing
assignTS v w sh
  | TS w `memberSh` sh = TS v `insertSh` sh
  | otherwise          = TS v `deleteSh` sh




{-nullify :: Address -> Sharing -> Sharing-}
{-nullify q (Sh ns) = Sh $ S.filter k ns-}
  {-where k (r1:/=:r2) = q /= r1 && q /= r2-}

{-substituteSh :: Eq i => AbstrValue i -> AbstrValue i -> Sh i -> Sh i-}
{-substituteSh v1 v2 st = case v1 of-}
  {-RefVal q -> mapAnnotations (nullify q) $ substitute v1 v2 st-}
  {-_        -> substitute v1 v2 st-}

mname :: String
mname = "Jat.PState.MemoryModel.Sharing"

merror :: String -> a
merror msg = error $ mname ++ msg


shares :: Address -> Address -> Sh i -> Bool
shares q r = not . sharesNot q r

sharesNot :: Address -> Address -> Sh i -> Bool
sharesNot q r = undefined

-- oh no we can only make a statement for those reachable in the current frame
-- others share per assumption if types share
-- extension in the anlysis is not easy
  
liftSh :: (Sharing -> Sharing) -> Sh i -> Sh i
liftSh f (PState hp frms sh) = PState hp frms (f sh)

pushSh :: Sharing -> Sharing
pushSh (Sh i j ns ms ts) = Sh i (j+1) ns ms ts

putSh :: Sharing -> Sharing
putSh (Sh i j ns ms ts) = Sh i (j+1) ns ms (StkVar i (j+1) `S.insert` ts)

popSh :: Sharing -> Sharing
popSh (Sh i j ns ms ts) = Sh i (j-1) ns ms ts

purgeSh :: Sharing -> Sharing
purgeSh (Sh i j ns ms ts) = Sh i (j-1) ns ms' ts'
  where
    ms' = StkVar i j `PS.delete'` ms
    ts' = StkVar i j `S.delete` ts

stkSh :: Sharing -> Var
stkSh (Sh i j _ _ _) = StkVar i j

stkSh' :: Sharing -> Var
stkSh' (Sh i j _ _ _) = StkVar i j

locSh :: Sharing -> Int -> Var
locSh (Sh i _ _ _ _) = LocVar i

updateSh :: P.Instruction -> Sh i -> Sh i
updateSh ins st = updateSh' ins `liftSh` st
  where
    updateSh' ins sh = case ins of
      P.Push v         -> putSh sh
      P.Pop            -> purgeSh sh
      P.Load n         -> pushSh $ (stkSh' sh `assignSh` locSh sh n) sh
      P.Store n        -> purgeSh $ (locSh sh n `assignSh` stkSh sh) sh
      P.Goto i         -> sh 
      P.IfFalse n      -> popSh sh
      P.IAdd           -> popSh sh
      P.ISub           -> popSh sh
      P.BAnd           -> popSh sh
      P.BOr            -> popSh sh
      P.CheckCast _    -> purgeSh sh 
      P.BNot           -> popSh sh
      P.ICmpGeq        -> popSh sh 
      P.Return         -> undefined 
      P.Invoke mn n    -> undefined 
      P.CmpEq          -> popSh sh 
      P.CmpNeq         -> popSh sh 
      P.New cn         -> putSh  (v:><:v `insertSh` sh)
        where v = stkSh' sh
      P.GetField fn cn -> undefined 
      P.PutField fn cn -> undefined 


