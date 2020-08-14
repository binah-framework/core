{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Binah where

import qualified Data.Set as S
import           Labels 
import           LIO
import           ProofCombinators
-------------------------------------------------------------------------------
-- | Basic DB values 
-------------------------------------------------------------------------------
type Val = Int

-- | Labeled DB Values --------------------------------------------------------

{-@ type LValV V = {v: Labeled Val | lvValue v == V } @-}
{-@ type LValL L = {v: Labeled Val | lvLabel v == L } @-}

-------------------------------------------------------------------------------
type Policy = Val -> Val -> Label

type Field  = Row -> Labeled Val

-------------------------------------------------------------------------------
-- | DB Rows
-------------------------------------------------------------------------------
data Row = Row (Labeled Val) (Labeled Val) 

{-@ reflect rFld1 @-}
rFld1 :: Row -> Labeled Val
rFld1 (Row lv _) = lv 

{-@ reflect rFld2 @-}
rFld2 :: Row -> Labeled Val
rFld2 (Row _ lv) = lv 

{-@ reflect rVal1 @-}
rVal1 :: Row -> Val
rVal1 r = lvValue (rFld1 r)

{-@ reflect rVal2 @-}
rVal2 :: Row -> Val
rVal2 r = lvValue (rFld2 r)


-- {-@ measure rV1 @-}
-- rV1 :: Row -> Val
-- rV1 (Row v _ _ _) = v 

-- {-@ measure rV2 @-}
-- rV2 :: Row -> Val
-- rV2 (Row _ v _ _) = v 

-------------------------------------------------------------------------------
-- | Policy-indexed Row -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ type RowP P1 P2 = {r: Row | okLabel P1 rFld1 r && okLabel P2 rFld2 r} @-}

{-@ reflect okLabel @-}
okLabel :: Policy -> Field -> Row -> Bool
okLabel p fld r = lvLabel (fld r) == policyLabel p r

{-@ reflect policyLabel @-}
policyLabel :: Policy -> Row -> Label
policyLabel p r = p (rVal1 r) (rVal2 r)

-- TODO: Does this need to be an LIO?
{-@ mkRow :: p1:_ -> p2:_ -> v1:_ -> v2:_ -> RowP p1 p2 @-}
mkRow :: Policy -> Policy -> Val -> Val -> Row
mkRow p1 p2 v1 v2 = Row (Labeled (p1 v1 v2) v1) (Labeled (p2 v1 v2) v2)

{-@ reflect approx @-}
approx :: Policy -> Row -> Label -> Bool
approx p r l = l `S.isSubsetOf` (p (rVal1 r) (rVal2 r)) -- p (rVal1 r) (rVal2 r) `leq` l

-------------------------------------------------------------------------------
-- | Tables (we require Policy in the Table to compute labels) ----------------
-------------------------------------------------------------------------------
data Table = Table Policy Policy [Row]

{-@ data Table = Table 
      { tPol1 :: Policy 
      , tPol2 :: Policy 
      , tRows :: [ RowP tPol1 tPol2 ]
      }
  @-}

{-@ measure ttPol1 @-}
ttPol1 :: Table -> Policy
ttPol1 (Table p1 _ _) = p1

{-@ measure ttPol2 @-}
ttPol2 :: Table -> Policy
ttPol2 (Table _ p2 _) = p2

{-@ type TableP P1 P2 = {t:Table | ttPol1 t == P1 && ttPol2 t = P2} @-}

-------------------------------------------------------------------------------
-- | "Proofs" that a Policy is bounded by a Label -----------------------------
-------------------------------------------------------------------------------
{-@ type SubPL P L = (sv1:Val -> sv2:Val -> {pf:() | leq (P sv1 sv2) L}) @-}
type SubPL = Val -> Val -> () 

-------------------------------------------------------------------------------
-- | Field Projection ---------------------------------------------------------
-------------------------------------------------------------------------------

{-@ proj1 :: p1:_ -> p2:_ -> l:_ -> 
             r:{RowP p1 p2 | approx (fldLabel F1 p1 p2) r l} -> 
             TIO {v:Val | v = rVal1 r} l S.empty @-}
proj1 :: Policy -> Policy -> Label -> Row -> LIO Val
proj1 p1 _ l r = unlabel l (rFld1 r)

{-@ proj2 :: p1:_ -> p2:_ -> l:_ -> 
             r:{RowP p1 p2 | approx (fldLabel F2 p1 p2) r l} -> 
             TIO {v:Val | v = rVal2 r} l S.empty 
  @-}
proj2 :: Policy -> Policy -> Label -> Row -> LIO Val
proj2 _ p2 l r = unlabel l (rFld2 r)

-------------------------------------------------------------------------------
-- | A datatype to represent Binah-Filters ------------------------------------
-------------------------------------------------------------------------------
data VOp  = Eq | Le | Ne | Ge  
data BOp  = And | Or
data Fld  = F1 | F2
data Pred = Atom VOp Fld Val | BOp BOp Pred Pred 
-------------------------------------------------------------------------------

{-@ reflect fldLabel @-}
fldLabel :: Fld -> Policy -> Policy -> Val -> Val -> Label
fldLabel F1 p _ v1 v2 = p v1 v2
fldLabel F2 _ p v1 v2 = p v1 v2

{-@ evalFld :: p1:_ -> p2:_ -> l:_ -> 
               fld:_ -> 
               r:{RowP p1 p2 | approx (fldLabel fld p1 p2) r l } -> 
               TIO {v:Val | v = interpFld fld (rVal1 r) (rVal2 r)} l S.empty
  @-}
evalFld :: Policy -> Policy -> Label -> Fld -> Row -> LIO Val
evalFld p1 p2 l F1 r = proj1 p1 p2 l r
evalFld p1 p2 l F2 r = proj2 p1 p2 l r

{-@ reflect predLabel @-}
predLabel :: Pred -> Policy -> Policy -> Val -> Val -> Label
predLabel (Atom _ f _) p1 p2 x1 x2 = fldLabel  f p1 p2 x1 x2
predLabel (BOp  _ f g) p1 p2 x1 x2 = (predLabel f p1 p2 x1 x2) `S.intersection` (predLabel g p1 p2 x1 x2)

-- TODO the `S.intersection` instead of plain `join` is due to https://github.com/ucsd-progsys/liquidhaskell/issues/1738

-------------------------------------------------------------------------------------------
-- | Evaluating a Predicate on a Row
-------------------------------------------------------------------------------------------
{-@ reflect interpFld @-}
interpFld :: Fld -> Val -> Val -> Val
interpFld F1 v1 _  = v1
interpFld F2 _  v2 = v2

{-@ reflect interpPred @-}
interpPred :: Pred -> Val -> Val -> Bool
interpPred (Atom o fld val) v1 v2 = vOp o (interpFld  fld v1 v2) val
interpPred (BOp  o f   g)   v1 v2 = bOp o (interpPred f   v1 v2) (interpPred g v1 v2)

{-@ evalPred :: p1:_ -> p2:_ -> l:_ -> 
                pred:_ -> 
                r:{RowP p1 p2 | approx (predLabel pred p1 p2) r l} -> 
                TIO {b:Bool | b = interpPred pred (rVal1 r) (rVal2 r)} l S.empty 
  @-}
evalPred :: Policy -> Policy -> Label -> Pred -> Row -> LIO Bool 
evalPred p1 p2 l (Atom o fld val) r =
  lmap l S.empty 
    (\fval -> vOp o fval val) 
    (evalFld p1 p2 l fld r)
  
evalPred p1 p2 l (BOp  o f g) r = 
  lmap2 l S.empty 
    (bOp o)
    (evalPred p1 p2 l f r)
    (evalPred p1 p2 l g r)

{-@ reflect vOp @-}
vOp :: VOp -> Val -> Val -> Bool
vOp Eq v1 v2 = v1 == v2 
vOp Le v1 v2 = v1 <= v2 
vOp Ne v1 v2 = v1 /= v2 
vOp Ge v1 v2 = v1 >= v2 

{-@ reflect bOp @-}
bOp :: BOp -> Bool -> Bool -> Bool
bOp And b1 b2 = b1 && b2
bOp Or  b1 b2 = b1 || b2

-----------------------------------------------------------------------------
-- | Vanilla Select from a Table
-----------------------------------------------------------------------------

{-@ select :: p1:_ -> p2:_ -> l:_ -> pred:_ 
           -> (sv1:_ -> sv2:_ -> { leq (predLabel pred p1 p2 sv1 sv2) l }) 
           -> TableP p1 p2 -> TIO [ RowP p1 p2 ] l S.empty 
  @-}
select :: Policy -> Policy -> Label -> Pred -> SubPL -> Table -> LIO [Row]
select p1 p2 l pred pf (Table _ _ rows) = 
  filterM l S.empty (\r -> evalPred p1 p2 l pred (r ? pf (rVal1 r) (rVal2 r))) rows

-----------------------------------------------------------------------------
-- | "Self-Referential" Select using downgrade / filterM''  
-----------------------------------------------------------------------------
{-@ select' :: p1:_ -> p2:_ -> l:_ -> pred:_ -> 
               (sv1:_ -> sv2:_ -> { (interpPred pred sv1 sv2) => leq (predLabel pred p1 p2 sv1 sv2) l }) ->
               TableP p1 p2 -> 
               TIO [ {r:RowP p1 p2 | interpPredR pred r} ] l S.empty 
  @-}

-- TODO: the above signature FAILS with `interpPredR pred r` ==> `interpPred pred (rVal1 r) (rVal2 r)` 
--       maybe some strange ETA-expansion bug in PLE?

select' :: Policy -> Policy -> Label -> Pred -> SubPL -> Table -> LIO [Row]
select' p1 p2 l pred pf (Table _ _ rows) = 
  let cond = interpPredR pred in 
  filterM'' l S.empty 
    cond  -- ghost
    (\r -> evalPred p1 p2 (if cond r then l else S.empty) pred (r ? pf (rVal1 r) (rVal2 r))) 
    rows

{-@ reflect interpPredR @-}
interpPredR :: Pred -> Row -> Bool
interpPredR pred r = interpPred pred (rVal1 r) (rVal2 r)

{-

A && B 

if A then B else EMPTY

filterM :: (f: a -> Bool) -> (x:a -> TIO {b:Bool | b = f x} { } S.empty)
-- filterM :: ∀α,i,f .(x : α → TI {Bool | ν ⇒ f x} ⟨f x ∧ i⟩) → [α] → TI [{α | f ν}] ⟨i⟩
-}
-----------------------------------------------------------------------------
{- JUNK 
-------------------------------------------------------------------------------
-- fieldLabel :: Row -> Field -> Label
-- fieldLabel r F1 = lvLabel (rFld1 r)
-- fieldLabel r F2 = lvLabel (rFld2 r)
-- predLabel :: Row -> Pred -> Label
-- predLabel r (Atom _ f _) = fieldLabel r f
-- predLabel r (And p1 p2)  = (predLabel r p1) `join` (predLabel r p2)

   proj1 :: r:Row P1 P2 -> LIO Val (P1 (rVal1 r) (rVal2 r)) Bot

   Pred_1
   Pred_2
   Pred_1_2
   
   eval_1   :: (forall v1 v2. P1 v1 v2 <: l) => Pred_1 -> Row P1 P2 -> LIO Bool l Bot 
   eval_2   :: (forall v1 v2. P2 v1 v2 <: l) => Pred_1 -> Row P1 P2 -> LIO Bool l Bot 
   eval_1_2 :: (forall v1 v2. P1 v1 v2 \leq P2 v1 v2  <: l) => Pred_1 -> Row P1 P2 -> LIO Bool l Bot 


   eval_1   :: Pred_1 -> r:Row P1 P2 -> LIO Bool (rLabel1 r) Bot 
   eval_2   :: Pred_2 -> r:Row P1 P2 -> LIO Bool (rLabel2 r) Bot 
   eval_1_2 :: Pred_2 -> r:Row P1 P2 -> LIO Bool (rLabel1 r `join` rLabel2 r) Bot 

   eval     :: (forall r. funky r p `leq` l) => p:Pred -> r:Row P1 P2 -> LIO Bool l Bot 
   eval     :: p:Pred -> r:Row P1 P2 -> LIO Bool (funky r p) Bot 


 -}