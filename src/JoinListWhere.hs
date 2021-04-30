{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--no-adt"     @-}

module JoinListWhere where

import           ProofCombinators
import qualified Data.Set as S
import           Labels
import           LIO
import           LIOCombinators
import           Rows
import           Storm2

-- This function takes a long time to verify and LH seems to hang forever if we put it
-- in Storm2.hs.

{-@ joinListWhere
      :: s1:_ -> s2:_ -> l:_
      -> q: (FilterS s1)
      -> f1: Fld
      -> f2: Fld
      -> (sv1:_ -> sv2:_ -> { (filterInv q sv1 sv2) => leq (filterPol q sv1 sv2) l })
      -> (v11:_ -> v12:_ -> v21:_ -> v22:_
           -> { joinCond f1 f2 v11 v12 v21 v22 => leq (fldPolicy s1 f1 v11 v12) l && leq (fldPolicy s2 f2 v21 v22) l})
      -> [RowS s1]
      -> [RowS s2]
      -> TIO [{r: (RowS s1, RowS s2) | joinCondR f1 f2 r}] l S.empty
@-}
joinListWhere :: Spec -> Spec -> Label -> Filter -> Fld -> Fld -> SubPL -> JoinPf -> [Row] -> [Row] -> LIO [(Row, Row)]
joinListWhere s1 s2 l q f1 f2 pf1 pf2 rows1 rows2 =
  bind l S.empty l S.empty (joinList s1 s2 l f1 f2 pf2 rows1 rows2) (\rows ->
      let cond = (\(r1, _) -> invFilterR q r1) in
      filterM'' l S.empty
        cond  -- ghost
        (\(r1, r2) -> eval s1 (if cond (r1, r2) then l else S.empty) q (r1 ? pf1 (rVal1 r1) (rVal2 r1)))
        rows
    )