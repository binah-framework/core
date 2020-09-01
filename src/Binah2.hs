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
-- | Fields -------------------------------------------------------------------
-------------------------------------------------------------------------------

data Fld = F1 | F2

{-@ reflect fldPolicy @-}
fldPolicy :: Table -> Fld -> Policy
fldPolicy t F1 = ttPol1 t
fldPolicy t F2 = ttPol2 t

{-@ type ValV Value = {xyz:Val | xyz = Value} @-}

-------------------------------------------------------------------------------
-- | Field Projection ---------------------------------------------------------
-------------------------------------------------------------------------------

{-@ project :: t:_ -> l:_ -> f:Fld ->
               {r:RowT t | approx (fldPolicy t f) r l} ->
               TIO (ValV (sel f (rVal1 r) (rVal2 r))) l S.empty
  @-}
project :: Table -> Label -> Fld -> Row -> LIO Val
project _ l F1 r = unlabel l (rFld1 r)
project _ l F2 r = unlabel l (rFld2 r)


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

data Filter = Filter Table Pred {- ghost -} RowInv Policy RowProof

{-@ data Filter = Filter
      { fTable :: Table
      , fPred  :: Pred
      , fInv   :: RowInv
      , fPol   :: Policy
      , fPf    :: v1:_ -> v2:_ -> { fInv v1 v2 == interpPred fPred v1 v2 && fPol v1 v2 == predLabel fTable fPred v1 v2}
      }
  @-}

      -- , fPf   :: v1:_ -> v2:_ -> { fInv v1 v2 == interpPred fPred v1 v2 }
{-@ measure filterTable @-}
filterTable :: Filter -> Table
filterTable (Filter t _ _ _ _) = t

{-@ measure filterInv @-}
filterInv :: Filter -> RowInv
filterInv (Filter _ _ i _ _) = i

{-@ measure filterPol @-}
filterPol :: Filter -> Policy
filterPol (Filter _ _ _ p _) = p

{-@ measure filterPred @-}
filterPred :: Filter -> Pred
filterPred (Filter _ p _ _ _) = p

{-@ type FilterT T = {f: Filter | filterTable f == T } @-}
{-@ type FilterP Inv Pol = {f: Filter | filterInv f == Inv && filterPol f == Pol } @-}
{-@ type FilterTP T Inv Pol = {f: Filter | filterTable f == T && filterInv f == Inv && filterPol f == Pol } @-}

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

{-@ reflect invFilterR @-}
invFilterR :: Filter -> Row -> Bool
invFilterR q r = filterInv q (rVal1 r) (rVal2 r)


{-@ reflect predLabel @-}
predLabel :: Table -> Pred -> Val -> Val -> Label
predLabel t (Atom _ f _) v1 v2 = (fldPolicy t f)   v1 v2
predLabel t (BOp  _ q r) v1 v2 = (predLabel t q v1 v2) `S.intersection` (predLabel t r v1 v2)

-------------------------------------------------------------------------------
-- | Refined Filters ----------------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect sel @-}
sel :: Fld -> a -> a -> a
sel F1 x1 x2 = x1
sel F2 x1 x2 = x2

{-@ reflect inv @-}
inv :: VOp -> Fld -> Val -> RowInv
inv Eq f v v1 v2 = sel f v1 v2 == v
inv Ne f v v1 v2 = sel f v1 v2 /= v
inv Le f v v1 v2 = sel f v1 v2 <= v
inv Ge f v v1 v2 = sel f v1 v2 >= v

{-@ reflect inv' @-}
inv' :: BOp -> Filter -> Filter -> RowInv
inv' And (Filter _ _ i1 _ _) (Filter _ _ i2 _ _) v1 v2 = i1 v1 v2 && i2 v1 v2
inv' Or  (Filter _ _ i1 _ _) (Filter _ _ i2 _ _) v1 v2 = i1 v1 v2 || i2 v1 v2

{-@ reflect polJoin @-}
polJoin :: Filter -> Filter -> Policy
polJoin q1 q2 = \v1 v2 -> filterPol q1 v1 v2 `S.intersection` filterPol q2 v1 v2

-------------------------------------------------------------------------------
-- | Filter Combinators -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ (==:) :: t:Table -> f:Fld -> v:Val -> FilterP (inv Eq f v) (fldPolicy t f) @-}
(==:) :: Table -> Fld -> Val -> Filter
(==:) t f v = Filter t (Atom Eq f v)
            {- ghost -} (inv Eq f v) (fldPolicy t f) (lemOp t Eq f v)

{-@ (/=:) :: t:Table -> f:Fld -> v:Val -> FilterP (inv Ne f v) (fldPolicy t f) @-}
(/=:) :: Table -> Fld -> Val -> Filter
(/=:) t f v = Filter t (Atom Ne f v)
            {- ghost -} (inv Ne f v) (fldPolicy t f) (lemOp t Ne f v)

{-@ (<=:) :: t:Table -> f:Fld -> v:Val -> FilterP (inv Le f v) (fldPolicy t f) @-}
(<=:) :: Table -> Fld -> Val -> Filter
(<=:) t f v = Filter t (Atom Le f v)
            {- ghost -} (inv Le f v) (fldPolicy t f) (lemOp t Le f v)

{-@ (>=:) :: t:Table -> f:Fld -> v:Val -> FilterP (inv Ge f v) (fldPolicy t f) @-}
(>=:) :: Table -> Fld -> Val -> Filter
(>=:) t f v = Filter t (Atom Ge f v)
            {- ghost -} (inv Ge f v) (fldPolicy t f) (lemOp t Ge f v)

{-@ lemOp :: t:_ -> o:_ -> f:_ -> v:_ -> v1:_ -> v2:_ -> {inv o f v v1 v2 == interpPred (Atom o f v) v1 v2} @-}
lemOp :: Table -> VOp -> Fld -> Val -> Val -> Val -> ()
lemOp _ Eq _ _ _ _ = ()
lemOp _ Le _ _ _ _ = ()
lemOp _ Ne _ _ _ _ = ()
lemOp _ Ge _ _ _ _ = ()

{-@ (&&:) :: t:_ -> q1:FilterT t -> q2:FilterT t -> FilterTP t (inv' And q1 q2) (polJoin q1 q2) @-}
(&&:) :: Table -> Filter -> Filter -> Filter
(&&:) t f1 f2 = Filter t (BOp And (filterPred f1) (filterPred f2))
                {- ghost -} (inv' And f1 f2) (polJoin f1 f2) (lemBOp t And f1 f2)

{-@ (||:) :: t:_ -> FilterT t -> FilterT t -> FilterT t @-}
(||:) :: Table -> Filter -> Filter -> Filter
(||:) t f1 f2 = Filter t (BOp Or (filterPred f1) (filterPred f2))
                {- ghost -} (inv' Or f1 f2) (polJoin f1 f2) (lemBOp t Or f1 f2)

{-@ lemBOp :: t:_ -> o:_ -> f1:FilterT t -> f2:FilterT t -> v1:_ -> v2:_ ->
               {inv' o f1 f2 v1 v2 == interpPred (BOp o (filterPred f1) (filterPred f2)) v1 v2 &&
                polJoin f1 f2 v1 v2 == predLabel t (BOp o (filterPred f1) (filterPred f2)) v1 v2
               }
  @-}
lemBOp :: Table -> BOp -> Filter -> Filter -> Val -> Val -> ()
lemBOp _ And (Filter _ _ _ _ pf1) (Filter _ _ _ _ pf2) v1 v2 = pf1 v1 v2 `seq` pf2 v1 v2 `seq` ()
lemBOp _ Or  (Filter _ _ _ _ pf1) (Filter _ _ _ _ pf2) v1 v2 = pf1 v1 v2 `seq` pf2 v1 v2 `seq` ()

-------------------------------------------------------------------------------------------
-- | Evaluating a Predicate on a Row
-------------------------------------------------------------------------------------------
{-@ evalPred :: t:_ -> l:_ ->
                p:Pred ->
                r:{RowT t | approx (predLabel t p) r l} ->
                TIO {b:Bool | b = interpPred p (rVal1 r) (rVal2 r)} l S.empty
  @-}
evalPred :: Table -> Label -> Pred -> Row -> LIO Bool
evalPred t l (Atom o fld val) r =
  lmap l S.empty
    (\fval -> vOp o fval val)
    (project t l fld r)

evalPred t l (BOp o f g) r =
  lmap2 l S.empty
    (bOp o)
    (evalPred t l f r)
    (evalPred t l g r)

{-@ eval :: t:_ ->
            l:_ ->
            q:(FilterT t) ->
            r:{RowT t | approx (filterPol q) r l} ->
            TIO {b:Bool | b = filterInv q (rVal1 r) (rVal2 r)} l S.empty
  @-}
eval :: Table -> Label -> Filter -> Row -> LIO Bool
eval t l (Filter _ pred _ _ pf) r =
  evalPred t l pred (r ? (pf (rVal1 r) (rVal2 r)))

-------------------------------------------------------------------------------------------
-- | "Proofs" that a Policy `p` is approximated by a Label `l`
--   specify constraints of the form `forall v1, v2. (policy v1 v2) `leq` l
-------------------------------------------------------------------------------------------
type SubPL = Val -> Val -> ()


-----------------------------------------------------------------------------
-- | "Self-Referential" Select using downgrade / filterM''
-----------------------------------------------------------------------------
{-@ select' :: t:_ -> l:_ -> q:(FilterT t) ->
               (sv1:_ -> sv2:_ -> { (filterInv q sv1 sv2) => leq (filterPol q sv1 sv2) l }) ->
               [RowT t] ->
               TIO [ {r:RowT t | invFilterR q r } ] l S.empty
  @-}

-- TODO: the above signature FAILS with `invFilterR q r` ==> `filterInv q (rVal1 r) (rVal2 r)`
--       likely due to some strange ETA-expansion bug in PLE?

select' :: Table -> Label -> Filter -> SubPL -> [Row] -> LIO [Row]
select' t l q pf rows =
  let cond = invFilterR q in
  filterM'' l S.empty
    cond  -- ghost
    (\r -> eval t (if cond r then l else S.empty) q (r ? pf (rVal1 r) (rVal2 r)))
    rows


------------------------------------------------------------------------------------------------------
-- | insert TODO: update ...
------------------------------------------------------------------------------------------------------

{-@ mkRow :: t:_ -> v1:_ -> v2:_
          -> { l: Label | leq l (ttPol1 t v1 v2) && leq l (ttPol2 t v1 v2) }
          -> TIO (RowT t) {l} {meet (ttPol1 t v1 v2) (ttPol2 t v1 v2)} @-}
mkRow :: Table -> Val -> Val -> Label -> LIO Row
mkRow t v1 v2 l =
  let p1 = ttPol1 t
      p2 = ttPol2 t
  in
    bind l (p1 v1 v2) l (p2 v1 v2) (label l (p1 v1 v2) v1) (\fld1 ->
      bind l (p2 v1 v2) l S.empty (label l (p2 v1 v2) v2) (\fld2 ->
        ret l (Row fld1 fld2)
      )
    )

{-@ insert :: t:_ -> v1:_ -> v2:_
          -> { l: Label | leq l (ttPol1 t v1 v2) && leq l (ttPol2 t v1 v2) }
          -> [ RowT t ]
          -> TIO [ RowT t ] {l} {meet (ttPol1 t v1 v2) (ttPol2 t v1 v2)}
@-}
insert :: Table -> Val -> Val -> Label -> [Row] -> LIO [Row]
insert t v1 v2 l rows =
  let p1 = ttPol1 t
      p2 = ttPol2 t
  in
    bind l (p1 v1 v2 `meet` p2 v1 v2) l S.empty (mkRow t v1 v2 l) (\r ->
      ret l (r : rows)
    )


-------------------------------------------------------------------------------
-- | TODO: Stores map Table (References) to lists of Rows ---------------------------
-------------------------------------------------------------------------------

-- TODO / Easy (just get rows)
-- Rejig the above to take "Store" instead of Rows
-- insert' :: StoreP -> Table -> Val -> Val -> Label -> LIO StoreP
-- select' :: StoreP -> Table -> Label -> Filter -> SubPL -> LIO [Row]

type Store = Table -> [Row]

{-@ type StoreP = tbl:Table -> [ RowT tbl ] @-}
