{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--no-adt"     @-}   -- TODO: o.w. LH generates a malformed `Set Row` term
                                -- that Z3 rejects as ill-sorted due to the listElts measure
                                -- **** LIQUID: ERROR :1:1-1:1: Error
                                --  crash: SMTLIB2 respSat = Error "line 5263 column 1067: unknown function/constant smt_set_add"
                                -- The fix is to make the Set embedding properly polymorphic (if SMTLIB supports that now?)

module Rows where

import           ProofCombinators
import qualified Data.Set as S
import           Labels
import           LIO
import           LIOCombinators

-------------------------------------------------------------------------------
-- | Basic DB values
-------------------------------------------------------------------------------
type Val = Int

-- | Labeled DB Values --------------------------------------------------------

{-@ type LValV V = {v: Labeled Val | lvValue v == V } @-}
{-@ type LValL L = {v: Labeled Val | lvLabel v == L } @-}

-------------------------------------------------------------------------------

type Policy = Val -> Val -> Label
type RowInv = Val -> Val -> Bool 

-------------------------------------------------------------------------------
-- | DB Rows
-------------------------------------------------------------------------------
data Row = Row (Labeled Val) (Labeled Val)
-- data Row = Row Val Val Label (Val -> Label)

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

-------------------------------------------------------------------------------
-- | Policy-indexed Row -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ type RowP P1 P2 = {r: Row | okLabel P1 rFld1 r && okLabel P2 rFld2 r} @-}

{-@ reflect okLabel @-}
okLabel :: Policy -> (Row -> Labeled Val) -> Row -> Bool
okLabel p fld r = lvLabel (fld r) == policyLabel p r

{-@ reflect policyLabel @-}
policyLabel :: Policy -> Row -> Label
policyLabel p r = p (rVal1 r) (rVal2 r)

{-@ reflect approx @-}
approx :: Policy -> Row -> Label -> Bool
approx p r l = l `S.isSubsetOf` (p (rVal1 r) (rVal2 r)) -- p (rVal1 r) (rVal2 r) `leq` l TODO: LH inline bug

-------------------------------------------------------------------------------
-- | Value Operations ----------------------------------------------------------
-------------------------------------------------------------------------------

data VOp  = Eq | Le | Ne | Ge
data BOp  = And | Or

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

