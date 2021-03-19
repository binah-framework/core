{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--no-adt"     @-}   -- TODO: o.w. LH generates a malformed `Set Row` term
                                -- that Z3 rejects as ill-sorted due to the listElts measure
                                -- **** LIQUID: ERROR :1:1-1:1: Error
                                --  crash: SMTLIB2 respSat = Error "line 5263 column 1067: unknown function/constant smt_set_add"
                                -- The fix is to make the Set embedding properly polymorphic (if SMTLIB supports that now?)

module Storm where

import           ProofCombinators
import qualified Data.Set as S
import           Labels
import           LIO
import           LIOCombinators
import           Rows

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
-- | Field Projection ---------------------------------------------------------
-------------------------------------------------------------------------------

{-@ proj1 :: p1:_ -> p2:_ -> l:_ ->
             r:{RowP p1 p2 | approx (fldLabel F1 p1 p2) r l} ->
             TIO {v:Val | v = rVal1 r} l S.empty @-}
proj1 :: Policy -> Policy -> Label -> Row -> LIO Val
proj1 _ _ l r = unlabel l (rFld1 r)

{-@ proj2 :: p1:_ -> p2:_ -> l:_ ->
             r:{RowP p1 p2 | approx (fldLabel F2 p1 p2) r l} ->
             TIO {v:Val | v = rVal2 r} l S.empty
  @-}
proj2 :: Policy -> Policy -> Label -> Row -> LIO Val
proj2 _ p2 l r = unlabel l (rFld2 r)

-------------------------------------------------------------------------------
-- | A datatype to represent Filters ------------------------------------------
-------------------------------------------------------------------------------

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
-- | Denotation of Predicates
-------------------------------------------------------------------------------------------
{-@ reflect interpFld @-}
interpFld :: Fld -> Val -> Val -> Val
interpFld F1 v1 _  = v1
interpFld F2 _  v2 = v2

{-@ reflect interpPred @-}
interpPred :: Pred -> Val -> Val -> Bool
interpPred (Atom o fld val) v1 v2 = vOp o (interpFld  fld v1 v2) val
interpPred (BOp  o f   g)   v1 v2 = bOp o (interpPred f   v1 v2) (interpPred g v1 v2)

{-@ reflect interpPredR @-}
interpPredR :: Pred -> Row -> Bool
interpPredR pred r = interpPred pred (rVal1 r) (rVal2 r)

-------------------------------------------------------------------------------------------
-- | Evaluating a Predicate on a Row
-------------------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------------------
-- | "Proofs" that a Policy `p` is approximated by a Label `l`
--   specify constraints of the form `forall v1, v2. (policy v1 v2) `leq` l
-------------------------------------------------------------------------------------------
type SubPL = Val -> Val -> ()

-------------------------------------------------------------------------------------------
-- | Vanilla Select from a Table
-------------------------------------------------------------------------------------------

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
--       likely due to some strange ETA-expansion bug in PLE?

select' :: Policy -> Policy -> Label -> Pred -> SubPL -> Table -> LIO [Row]
select' p1 p2 l pred pf (Table _ _ rows) =
  let cond = interpPredR pred in
  filterM'' l S.empty
    cond  -- ghost
    (\r -> evalPred p1 p2 (if cond r then l else S.empty) pred (r ? pf (rVal1 r) (rVal2 r)))
    rows

------------------------------------------------------------------------------------------------------
-- | insert TODO: update ...
------------------------------------------------------------------------------------------------------

{-@ mkRow :: p1:_ -> p2:_ -> v1:_ -> v2:_
          -> { l: Label | leq l (p1 v1 v2) && leq l (p2 v1 v2) }
          -> TIO (RowP p1 p2) {l} {meet (p1 v1 v2) (p2 v1 v2)} @-}
mkRow :: Policy -> Policy -> Val -> Val -> Label -> LIO Row
mkRow p1 p2 v1 v2 l =
  bind l (p1 v1 v2) l (p2 v1 v2) (label l (p1 v1 v2) v1) (\fld1 ->
    bind l (p2 v1 v2) l S.empty (label l (p2 v1 v2) v2) (\fld2 ->
      ret l (Row fld1 fld2)
    )
  )

{-@ insert :: p1:_ -> p2:_ -> v1:_ -> v2:_
          -> { l: Label | leq l (p1 v1 v2) && leq l (p2 v1 v2) }
          -> TableP p1 p2
          -> TIO (TableP p1 p2) {l} {meet (p1 v1 v2) (p2 v1 v2)}
@-}
insert :: Policy -> Policy -> Val -> Val -> Label -> Table -> LIO Table
insert p1 p2 v1 v2 l (Table _ _ rows) =
  bind l (p1 v1 v2 `meet` p2 v1 v2) l S.empty (mkRow p1 p2 v1 v2 l) (\r ->
    ret l (Table p1 p2 (r : rows))
  )



