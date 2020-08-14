{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Binah where

import qualified Data.Set as S
import           Labels 
import           LIO

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

{-@ type TableP P1 P2 = {t:Table | tPol1 t == P1 && tPol2 t = P2} @-}

{-@ type SubPL P L = (sv1:Val -> sv2:Val -> {pf:() | leq (P sv1 sv2) L}) @-}
type SubPL = Val -> Val -> () 

{-@ proj1 :: p1:_ -> p2:_ -> l:_ -> SubPL p1 l -> RowP p1 p2 -> TIO Val l S.empty @-}
proj1 :: Policy -> Policy -> Label -> SubPL -> Row -> LIO Val
proj1 = undefined 

{-@ proj2 :: p1:_ -> p2:_ -> l:_ -> SubPL p2 l -> RowP p1 p2 -> TIO Val l S.empty @-}
proj2 :: Policy -> Policy -> Label -> SubPL -> Row -> LIO Val
proj2 = undefined 

-------------------------------------------------------------------------------
data Op   = Eq | Le | Ne | Ge  
data Bop  = And | Or
data Fld  = F1 | F2
data Pred = Atom Op Fld Val | Op Bop Pred Pred 

-- fieldLabel :: Row -> Field -> Label
-- fieldLabel r F1 = lvLabel (rFld1 r)
-- fieldLabel r F2 = lvLabel (rFld2 r)

-- predLabel :: Row -> Pred -> Label
-- predLabel r (Atom _ f _) = fieldLabel r f
-- predLabel r (And p1 p2)  = (predLabel r p1) `join` (predLabel r p2)

{-@ reflect fldLabel @-}
fldLabel :: Fld -> Policy -> Policy -> Val -> Val -> Label

fldLabel F1 p _ v1 v2 = p v1 v2
fldLabel F2 _ p v1 v2 = p v1 v2

{-@ evalFld :: p1:_ -> p2:_ -> l:_ -> fld:_ 
            -> (sv1:_ -> sv2:_ -> { leq (fldLabel fld p1 p2 sv1 sv2) l }) 
            -> RowP p1 p2 -> TIO Val l S.empty
  @-}
evalFld :: Policy -> Policy -> Label -> Fld -> SubPL -> Row -> LIO Val
evalFld _ _ l F1 pf r = unlabel (l ? pf (rVal1 r) (rVal2 r)) (rFld1 r)
evalFld _ _ l F2 pf r = unlabel (l ? pf (rVal1 r) (rVal2 r)) (rFld2 r)

{-@ reflect predLabel @-}
predLabel :: Pred -> Policy -> Policy -> Val -> Val -> Label
predLabel (Atom _ f _) p1 p2 x1 x2 = fldLabel  f p1 p2 x1 x2
predLabel (Op _   f g) p1 p2 x1 x2 = (predLabel f p1 p2 x1 x2) `join` (predLabel g p1 p2 x1 x2)

-- evalPred :: 
-- evalP :: (forall r. funky r p `leq` l) => p:Pred -> r:Row P1 P2 -> LIO Bool l Bot 
-- evalPred :: l:Label -> p:Pred -> (r:_ -> leq (predLabel r p) l) -> Row -> LIO Bool l Bot 
-- evalPred :: Label -> Pred   


infixl 3 ?

{-@ (?) :: forall a b <pa :: a -> Bool, pb :: b -> Bool>. a<pa> -> b<pb> -> a<pa> @-}
(?) :: a -> b -> a
x ? _ = x
{-# INLINE (?)   #-}



-------------------------------------------------------------------------------
{- 

-------------------------------------------------------------------------------


   proj1 :: r:Row P1 P2 -> LIO Val (P1 (rVal1 r) (rVal2 r)) Bot

    Pred_1
    Pred_2
    Pred_1_2
   
    eval_1   :: (forall v1 v2. P1 v1 v2 <: l) => Pred_1 -> Row P1 P2 -> LIO Bool l Bot 
    eval_2   :: (forall v1 v2. P2 v1 v2 <: l) => Pred_1 -> Row P1 P2 -> LIO Bool l Bot 
    eval_1_2 :: (forall v1 v2. P1 v1 v2 \leq P2 v1 v2  <: l) => Pred_1 -> Row P1 P2 -> LIO Bool l Bot 

    ???

    eval_1   :: Pred_1 -> r:Row P1 P2 -> LIO Bool (rLabel1 r) Bot 
    eval_2   :: Pred_2 -> r:Row P1 P2 -> LIO Bool (rLabel2 r) Bot 
    eval_1_2 :: Pred_2 -> r:Row P1 P2 -> LIO Bool (rLabel1 r `join` rLabel2 r) Bot 

    eval     :: (forall r. funky r p `leq` l) => p:Pred -> r:Row P1 P2 -> LIO Bool l Bot 
    eval     :: p:Pred -> r:Row P1 P2 -> LIO Bool (funky r p) Bot 

    data Atom = Eq F1 Val | Eq F2 Val 
    data Pred = Atom Atom | And Pred Pred | Or Pred Pred

    funkyAtom :: Row -> Atom -> Label  
    funkyAtom r (Eq F1 Val) = rLabel1 r 
    funkyAtom r (Eq F2 Val) = rLabel2 r 

    funkyPred :: Row -> Pred -> Label  
    funkyPred (Atom a) = funkyAtom a
    funkyPred (Atom a) = funkyAtom a

    select :: (forall r. eval p r => funky p r `leq` l) => Table P1 P2 -> p:Pred -> LIO [Row P1 P2] l Bot 

 -}