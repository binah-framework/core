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

data Spec = Spec Policy Policy

{-@ type RowS S = RowP (sPol1 S) (sPol2 S) @-}

data Table = Table { ttSpec :: Spec, ttRows :: [Row] }

{-@ data Table = Table { ttSpec :: Spec, ttRows :: [RowS ttSpec] } @-}

{-@ type TableS S = {t: Table | ttSpec t == S} @-}

{-@ measure sPol1 @-}
sPol1 :: Spec -> Policy
sPol1 (Spec p1 _) = p1

{-@ measure sPol2 @-}
sPol2 :: Spec -> Policy
sPol2 (Spec _ p2) = p2

-------------------------------------------------------------------------------
-- | Fields -------------------------------------------------------------------
-------------------------------------------------------------------------------

data Fld = F1 | F2

{-@ reflect fldPolicy @-}
fldPolicy :: Spec -> Fld -> Policy
fldPolicy s F1 = sPol1 s
fldPolicy s F2 = sPol2 s

{-@ type ValV Value = {xyz:Val | xyz = Value} @-}

-------------------------------------------------------------------------------
-- | Field Projection ---------------------------------------------------------
-------------------------------------------------------------------------------

{-@ project :: s:_ -> l:_ -> f:Fld ->
               {r:RowS s | approx (fldPolicy s f) r l} ->
               TIO (ValV (sel f (rVal1 r) (rVal2 r))) l S.empty
  @-}
project :: Spec -> Label -> Fld -> Row -> LIO Val
project _ l F1 r = unlabel l (rFld1 r)
project _ l F2 r = unlabel l (rFld2 r)

-------------------------------------------------------------------------------
-- | Filters ------------------------------------------------------------------
-------------------------------------------------------------------------------
data Pred
  = Atom VOp Fld  Val
  | BOp  BOp Pred Pred

type RowProof = Val -> Val -> ()

data Filter = Filter Spec Pred {- ghost -} RowInv Policy RowProof

{-@ data Filter = Filter
      { fSpec :: Spec
      , fPred :: Pred
      , fInv  :: RowInv
      , fPol  :: Policy
      , fPf   :: v1:_ -> v2:_ -> { fInv v1 v2 == interpPred fPred v1 v2 && fPol v1 v2 == predLabel fSpec fPred v1 v2}
      }
  @-}

      -- , fPf   :: v1:_ -> v2:_ -> { fInv v1 v2 == interpPred fPred v1 v2 }
{-@ measure filterSpec @-}
filterSpec :: Filter -> Spec
filterSpec (Filter s _ _ _ _) = s

{-@ measure filterInv @-}
filterInv :: Filter -> RowInv
filterInv (Filter _ _ i _ _) = i

{-@ measure filterPol @-}
filterPol :: Filter -> Policy
filterPol (Filter _ _ _ p _) = p

{-@ measure filterPred @-}
filterPred :: Filter -> Pred
filterPred (Filter _ p _ _ _) = p

{-@ type FilterS S = {f: Filter | filterSpec f == S } @-}
{-@ type FilterP Inv Pol = {f: Filter | filterInv f == Inv && filterPol f == Pol } @-}
{-@ type FilterSP S Inv Pol = {f: Filter | filterSpec f == S && filterInv f == Inv && filterPol f == Pol } @-}

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
predLabel :: Spec -> Pred -> Val -> Val -> Label
predLabel s (Atom _ f _) v1 v2 = (fldPolicy s f)   v1 v2
predLabel s (BOp  _ q r) v1 v2 = (predLabel s q v1 v2) `S.intersection` (predLabel s r v1 v2)

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

{-@ (==:) :: s:Spec -> f:Fld -> v:Val -> FilterP (inv Eq f v) (fldPolicy s f) @-}
(==:) :: Spec -> Fld -> Val -> Filter
(==:) s f v = Filter s (Atom Eq f v)
            {- ghost -} (inv Eq f v) (fldPolicy s f) (lemOp Eq f v)

{-@ (/=:) :: s:Spec -> f:Fld -> v:Val -> FilterP (inv Ne f v) (fldPolicy s f) @-}
(/=:) :: Spec -> Fld -> Val -> Filter
(/=:) s f v = Filter s (Atom Ne f v)
            {- ghost -} (inv Ne f v) (fldPolicy s f) (lemOp Ne f v)

{-@ (<=:) :: t:Spec -> f:Fld -> v:Val -> FilterP (inv Le f v) (fldPolicy t f) @-}
(<=:) :: Spec -> Fld -> Val -> Filter
(<=:) s f v = Filter s (Atom Le f v)
            {- ghost -} (inv Le f v) (fldPolicy s f) (lemOp Le f v)

{-@ (>=:) :: s:Spec-> f:Fld -> v:Val -> FilterP (inv Ge f v) (fldPolicy s f) @-}
(>=:) :: Spec -> Fld -> Val -> Filter
(>=:) s f v = Filter s (Atom Ge f v)
            {- ghost -} (inv Ge f v) (fldPolicy s f) (lemOp Ge f v)

{-@ lemOp :: o:_ -> f:_ -> v:_ -> v1:_ -> v2:_ -> {inv o f v v1 v2 == interpPred (Atom o f v) v1 v2} @-}
lemOp :: VOp -> Fld -> Val -> Val -> Val -> ()
lemOp Eq _ _ _ _ = ()
lemOp Le _ _ _ _ = ()
lemOp Ne _ _ _ _ = ()
lemOp Ge _ _ _ _ = ()

{-@ (&&:) :: s:_ -> q1:FilterS s -> q2:FilterS s -> FilterSP s (inv' And q1 q2) (polJoin q1 q2) @-}
(&&:) :: Spec -> Filter -> Filter -> Filter
(&&:) s f1 f2 = Filter s (BOp And (filterPred f1) (filterPred f2))
                {- ghost -} (inv' And f1 f2) (polJoin f1 f2) (lemBOp s And f1 f2)

{-@ (||:) :: t:_ -> FilterS t -> FilterS t -> FilterS t @-}
(||:) :: Spec -> Filter -> Filter -> Filter
(||:) s f1 f2 = Filter s (BOp Or (filterPred f1) (filterPred f2))
                {- ghost -} (inv' Or f1 f2) (polJoin f1 f2) (lemBOp s Or f1 f2)

{-@ lemBOp :: s:_ -> o:_ -> f1:FilterS s -> f2:FilterS s -> v1:_ -> v2:_ ->
               {inv' o f1 f2 v1 v2 == interpPred (BOp o (filterPred f1) (filterPred f2)) v1 v2 &&
                polJoin f1 f2 v1 v2 == predLabel s (BOp o (filterPred f1) (filterPred f2)) v1 v2
               }
  @-}
lemBOp :: Spec -> BOp -> Filter -> Filter -> Val -> Val -> ()
lemBOp _ And (Filter _ _ _ _ pf1) (Filter _ _ _ _ pf2) v1 v2 = pf1 v1 v2 `seq` pf2 v1 v2 `seq` ()
lemBOp _ Or  (Filter _ _ _ _ pf1) (Filter _ _ _ _ pf2) v1 v2 = pf1 v1 v2 `seq` pf2 v1 v2 `seq` ()

-------------------------------------------------------------------------------------------
-- | Evaluating a Predicate on a Row
-------------------------------------------------------------------------------------------
{-@ evalPred :: s:_ -> l:_ ->
                p:Pred ->
                r:{RowS s | approx (predLabel s p) r l} ->
                TIO {b:Bool | b = interpPred p (rVal1 r) (rVal2 r)} l S.empty
  @-}
evalPred :: Spec -> Label -> Pred -> Row -> LIO Bool
evalPred s l (Atom o fld val) r =
  lmap l S.empty
    (\fval -> vOp o fval val)
    (project s l fld r)

evalPred s l (BOp o f g) r =
  lmap2 l S.empty
    (bOp o)
    (evalPred s l f r)
    (evalPred s l g r)

{-@ eval :: s:_ ->
            l:_ ->
            q:(FilterS s) ->
            r:{RowS s | approx (filterPol q) r l} ->
            TIO {b:Bool | b = filterInv q (rVal1 r) (rVal2 r)} l S.empty
  @-}
eval :: Spec -> Label -> Filter -> Row -> LIO Bool
eval s l (Filter _ pred _ _ pf) r =
  evalPred s l pred (r ? (pf (rVal1 r) (rVal2 r)))

-------------------------------------------------------------------------------------------
-- | "Proofs" that a Policy `p` is approximated by a Label `l`
--   specify constraints of the form `forall v1, v2. (policy v1 v2) `leq` l
-------------------------------------------------------------------------------------------
type SubPL = Val -> Val -> ()


-----------------------------------------------------------------------------
-- | "Self-Referential" Select using downgrade / filterM''
-----------------------------------------------------------------------------
{-@ select' :: s:_ -> l:_ -> q:(FilterS s) ->
               (sv1:_ -> sv2:_ -> { (filterInv q sv1 sv2) => leq (filterPol q sv1 sv2) l }) ->
               [RowS s] ->
               TIO [ {r:RowS s | invFilterR q r } ] l S.empty
  @-}

-- TODO: the above signature FAILS with `invFilterR q r` ==> `filterInv q (rVal1 r) (rVal2 r)`
--       likely due to some strange ETA-expansion bug in PLE?

select' :: Spec -> Label -> Filter -> SubPL -> [Row] -> LIO [Row]
select' s l q pf rows =
  let cond = invFilterR q in
  filterM'' l S.empty
    cond  -- ghost
    (\r -> eval s (if cond r then l else S.empty) q (r ? pf (rVal1 r) (rVal2 r)))
    rows


------------------------------------------------------------------------------------------------------
-- | insert TODO: update ...
------------------------------------------------------------------------------------------------------

{-@ mkRow :: s:_ -> v1:_ -> v2:_
          -> { l: Label | leq l (sPol2 s v1 v2) }
          -> TIO (RowS s) {l} {meet (sPol1 s v1 v2) (sPol2 s v1 v2)} @-}
mkRow :: Spec -> Val -> Val -> Label -> LIO Row
mkRow s v1 v2 l =
  let p1 = sPol1 s
      p2 = sPol2 s
  in
    bind l (p1 v1 v2) l (p2 v1 v2) (label l (p1 v1 v2) v1) (\fld1 ->
      bind l (p2 v1 v2) l S.empty (label l (p2 v1 v2) v2) (\fld2 ->
        ret l (Row fld1 fld2)
      )
    )

{-@ insert :: s:_ -> v1:_ -> v2:_
           -> { l: Label | leq l (sPol2 s v1 v2) }
           -> TableS s
           -> TIO (TableS s) {l} {meet (sPol1 s v1 v2) (sPol2 s v1 v2)}
@-}
insert :: Spec -> Val -> Val -> Label -> Table -> LIO Table
insert s v1 v2 l (Table _ rows) =
  let p1 = sPol1 s
      p2 = sPol2 s
  in
    bind l (p1 v1 v2 `meet` p2 v1 v2) l S.empty (mkRow s v1 v2 l) (\r ->
      ret l (Table s (r : rows))
    )