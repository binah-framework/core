{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--no-adt"     @-}

module Binah2 where

import           ProofCombinators
import qualified Data.Set as S
import           Labels
import           LIO
import           LIOCombinators
import           Rows


-------------------------------------------------------------------------------
-- | Tables (we require Policy in the Table to compute labels) ----------------
-------------------------------------------------------------------------------

type TableId = Int
data Table   = Table TableId Policy Policy

{-@ measure ttPol1 @-}
ttPol1 :: Table -> Policy
ttPol1 (Table _ p1 _) = p1

{-@ measure ttPol2 @-}
ttPol2 :: Table -> Policy
ttPol2 (Table _ _ p2) = p2

{-@ type RowT T = RowP (ttPol1 T) (ttPol2 T) @-}

-------------------------------------------------------------------------------
-- | Stores map Table (References) to lists of Rows ---------------------------
-------------------------------------------------------------------------------

type Store = Table -> [Row]

{-@ type StoreP = tbl:Table -> [ RowP (ttPol1 tbl) (ttPol2 tbl) ] @-}


-------------------------------------------------------------------------------
-- | Fields -------------------------------------------------------------------
-------------------------------------------------------------------------------

data Fld = F1 Table | F2 Table 

{-@ measure fldTable @-}
fldTable :: Fld -> Table
fldTable (F1 t) = t
fldTable (F2 t) = t

{-@ type FldT T = {f:Fld | fldTable f == T} @-}

{-@ reflect fldLabel @-}
fldLabel :: Fld -> Val -> Val -> Label
fldLabel f v1 v2 = fldPolicy f v1 v2

{-@ reflect fldPolicy @-}
fldPolicy :: Fld -> Policy
fldPolicy (F1 t) = ttPol1 t
fldPolicy (F2 t) = ttPol2 t

{-@ type ValV Value = {xyz:Val | xyz = Value} @-}

-------------------------------------------------------------------------------
-- | Field Projection ---------------------------------------------------------
-------------------------------------------------------------------------------

{-@ project :: l:_ -> f:_ -> 
               {r:RowT (fldTable f) | approx (fldLabel f) r l} -> 
               TIO (ValV (sel f (rVal1 r) (rVal2 r))) l S.empty
  @-}
project :: Label -> Fld -> Row -> LIO Val
project l (F1 _) r = unlabel l (rFld1 r)
project l (F2 _) r = unlabel l (rFld2 r)


{-@ incr :: Nat -> Nat @-}
incr :: Int -> Int
incr x = x + 1

-------------------------------------------------------------------------------
-- | Filters ------------------------------------------------------------------
-------------------------------------------------------------------------------
data Pred 
  = Atom VOp Fld  Val
  | BOp  BOp Pred Pred

type RowProof = Val -> Val -> ()

data Filter = Filter Pred {- ghost -} RowInv Policy RowProof

{-@ data Filter = Filter 
      { fPred :: Pred
      , fInv  :: RowInv 
      , fPol  :: Policy 
      , fPf   :: v1:_ -> v2:_ -> { fInv v1 v2 == interpPred fPred v1 v2 && fPol v1 v2 == predLabel fPred v1 v2}
      }
  @-}

      -- , fPf   :: v1:_ -> v2:_ -> { fInv v1 v2 == interpPred fPred v1 v2 } 

{-@ measure filterInv @-}
filterInv :: Filter -> RowInv
filterInv (Filter _ i _ _) = i 

{-@ measure filterPol @-}
filterPol :: Filter -> Policy
filterPol (Filter _ _ p _) = p 

{-@ measure filterPred @-}
filterPred :: Filter -> Pred
filterPred (Filter p _ _ _) = p

{-@ type FilterP Inv Pol = {f: Filter | filterInv f == Inv && filterPol f == Pol } @-}

-------------------------------------------------------------------------------
-- | Filter Denotations -------------------------------------------------------
-------------------------------------------------------------------------------

-- {-@ reflect interpFld @-}
-- interpFld :: Fld -> Val -> Val -> Val
-- interpFld f v1 v2 = sel f v1 v2 

{-@ reflect interpPred @-}
interpPred :: Pred -> Val -> Val -> Bool
interpPred (Atom o fld val) v1 v2 = vOp o (sel fld v1 v2) val
interpPred (BOp  o f   g  ) v1 v2 = bOp o (interpPred f   v1 v2) (interpPred g v1 v2)

{-@ reflect interpPredR @-}
interpPredR :: Pred -> Row -> Bool
interpPredR pred r = interpPred pred (rVal1 r) (rVal2 r)

{-@ reflect predLabel @-}
predLabel :: Pred -> Val -> Val -> Label
predLabel (Atom _ f _) v1 v2 = fldLabel f   v1 v2
predLabel (BOp  _ q r) v1 v2 = (predLabel q v1 v2) `S.intersection` (predLabel r v1 v2)

-------------------------------------------------------------------------------
-- | Refined Filters ----------------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect sel @-}
sel :: Fld -> a -> a -> a
sel (F1 _) x1 x2 = x1
sel (F2 _) x1 x2 = x2

{-@ reflect inv @-}
inv :: VOp -> Fld -> Val -> RowInv
inv Eq f v v1 v2 = sel f v1 v2 == v
inv Ne f v v1 v2 = sel f v1 v2 /= v
inv Le f v v1 v2 = sel f v1 v2 <= v
inv Ge f v v1 v2 = sel f v1 v2 >= v

{-@ reflect inv' @-}
inv' :: BOp -> Filter -> Filter -> RowInv
inv' And (Filter _ i1 _ _) (Filter _ i2 _ _) v1 v2 = i1 v1 v2 && i2 v1 v2
inv' Or  (Filter _ i1 _ _) (Filter _ i2 _ _) v1 v2 = i1 v1 v2 || i2 v1 v2

{-@ reflect polJoin @-}
polJoin :: Filter -> Filter -> Policy
polJoin q1 q2 = \v1 v2 -> filterPol q1 v1 v2 `S.intersection` filterPol q2 v1 v2

-------------------------------------------------------------------------------
-- | Filter Combinators -------------------------------------------------------
-------------------------------------------------------------------------------

(==:) :: Fld -> Val -> Filter  
f ==: v = Filter (Atom Eq f v) 
            {- ghost -} (inv Eq f v) (fldPolicy f) (lemOp Eq f v) 

(/=:) :: Fld -> Val -> Filter  
f /=: v = Filter (Atom Ne f v) 
            {- ghost -} (inv Ne f v) (fldPolicy f) (lemOp Ne f v) 

(<=:) :: Fld -> Val -> Filter  
f <=: v = Filter (Atom Le f v) 
            {- ghost -} (inv Le f v) (fldPolicy f) (lemOp Le f v)

(>=:) :: Fld -> Val -> Filter  
f >=: v = Filter (Atom Ge f v) 
            {- ghost -} (inv Ge f v) (fldPolicy f) (lemOp Ge f v)

{-@ lemOp :: o:_ -> f:_ -> v:_ -> v1:_ -> v2:_ -> {inv o f v v1 v2 == interpPred (Atom o f v) v1 v2} @-}
lemOp :: VOp -> Fld -> Val -> Val -> Val -> ()
lemOp Eq _ _ _ _ = ()
lemOp Le _ _ _ _ = ()
lemOp Ne _ _ _ _ = ()
lemOp Ge _ _ _ _ = ()

(&&:) :: Filter -> Filter -> Filter
(&&:) f1 f2 = Filter (BOp And (filterPred f1) (filterPred f2)) 
                {- ghost -} (inv' And f1 f2) (polJoin f1 f2) (lemBOp And f1 f2)
 
(||:) :: Filter -> Filter -> Filter
(||:) f1 f2 = Filter (BOp Or (filterPred f1) (filterPred f2)) 
                {- ghost -} (inv' Or f1 f2) (polJoin f1 f2) (lemBOp Or f1 f2)       

{-@ lemBOp :: o:_ -> f1:_ -> f2:_ -> v1:_ -> v2:_ -> 
               {inv' o f1 f2 v1 v2 == interpPred (BOp o (filterPred f1) (filterPred f2)) v1 v2 &&
                polJoin f1 f2 v1 v2 == predLabel (BOp o (filterPred f1) (filterPred f2)) v1 v2
               } 
  @-}
lemBOp :: BOp -> Filter -> Filter -> Val -> Val -> ()
lemBOp And (Filter _ _ _ pf1) (Filter _ _ _ pf2) v1 v2 = pf1 v1 v2 `seq` pf2 v1 v2 `seq` () 
lemBOp Or  (Filter _ _ _ pf1) (Filter _ _ _ pf2) v1 v2 = pf1 v1 v2 `seq` pf2 v1 v2 `seq` () 

-------------------------------------------------------------------------------------------
-- | Evaluating a Predicate on a Row
-------------------------------------------------------------------------------------------

{-@ evalPred :: l:_ ->
                pred:_ ->
                r:{Row | approx (predLabel pred) r l} ->
                TIO {b:Bool | b = interpPred pred (rVal1 r) (rVal2 r)} l S.empty
  @-}
evalPred :: Label -> Pred -> Row -> LIO Bool
evalPred l (Atom o fld val) r =
  lmap l S.empty
    (\fval -> vOp o fval val)
    (evalFld l fld r)

evalPred l (BOp  o f g) r =
  lmap2 l S.empty
    (bOp o)
    (evalPred l f r)
    (evalPred l g r)

{-@ evalFld :: l:_ ->
               f:_ ->
               r:{Row | approx (fldLabel f) r l } ->
               TIO (ValV (sel f (rVal1 r) (rVal2 r))) l S.empty
  @-}
evalFld :: Label -> Fld -> Row -> LIO Val
evalFld l f r = undefined -- project l f r -- FIXME TODO HEREHEREHERE

               -- TIO (ValV (rVal fld r)) l S.empty
{- 

-- Filter and DB API

  evalPred 

  select' :: l:_ -> pred:FilterP c p  ->
             (v1:_ -> v2:_ -> {(c v1 v2) => leq (p v1 v2) l}) ->
             TableP p1 p2 ->
             TIO [ {r:RowP p1 p2 | c r.1 r.2} ] l S.empty

 -}