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

data Row = Row Val Val (Labeled Val) (Labeled Val) 

{-@ data Row = Row { _rV1   :: Val
                   , _rV2   :: Val
                   , _rFld1 :: LValV _rV1
                   , _rFld2 :: LValV _rV2 
                   } 
  @-} 

{-@ measure rFld1 @-}
rFld1 :: Row -> Labeled Val
rFld1 (Row _ _ lv _) = lv 

{-@ measure rFld2 @-}
rFld2 :: Row -> Labeled Val
rFld2 (Row _ _ _ lv) = lv 

{-@ measure rV1 @-}
rV1 :: Row -> Val
rV1 (Row v _ _ _) = v 

{-@ measure rV2 @-}
rV2 :: Row -> Val
rV2 (Row _ v _ _) = v 

-------------------------------------------------------------------------------
-- | Policy-indexed Row -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ type RowP P1 P2 = {r: Row | okLabel P1 rFld1 r && okLabel P2 rFld2 r} @-}

{-@ inline okLabel @-}
okLabel :: Policy -> Field -> Row -> Bool
okLabel p fld r = lvLabel (fld r) == policyLabel p r

{-@ inline policyLabel @-}
policyLabel :: Policy -> Row -> Label
policyLabel p r = p (rV1 r) (rV2 r)

-- TODO: Does this need to be an LIO?
{-@ mkRow :: p1:_ -> p2:_ -> v1:_ -> v2:_ -> RowP p1 p2 @-}
mkRow :: Policy -> Policy -> Val -> Val -> Row
mkRow p1 p2 v1 v2 = Row v1 v2 (Labeled (p1 v1 v2) v1) (Labeled (p2 v1 v2) v2)

-------------------------------------------------------------------------------
-- | Tables ... ---------------------------------------------------------------
-------------------------------------------------------------------------------

{- style Tables 

1. Generalize Values and Store


    data LVal  = LVal { vLabel :: Label, vValue :: Val }  
    
    type LVal' V L = {v:LVal | vLabel v = L && vValue = V }

    type Policy = Val -> Val -> Label

    data Row = Row { _v1 :: Val
                   , _v2 :: Val, 
                   , fld1 :: LValV _v1 
                   , fld2 :: LValV _v2 
                   }
    
    type Row' P1 P2 = {r: Row | vLabel (fld1 r) == (P1 (_v1 r) (_v2 r)) && ... } 

    mkRow :: P1 -> P2 -> v1:Val -> v2:Val -> (Row' P1 P2)

    type Table P1 P2 = [Row P1 P2]
    
    selectAll :: Table P1 P2 -> [Row P1 P2]

    -- proj1 :: forall l. (v1:_ -> v2:_ -> {P1 v1 v2 `leq` l}) -> Row P1 P2 -> LIO Val l Bot
    -- proj1 :: r:Row P1 P2 -> LIO Val (P1 (rVal1 r) (rVal2 r)) Bot

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










2. Generalize Field into Table

    data Field = Field Addr Label

    data Table = Table { tAddr   :: Addr
                       , tLabel  :: Label             -- label to access the table itself (length?)
                       , tLabel1 :: Label             -- label to access first field
                       , tLabel2 :: Val -> Label      -- label to access second field
                       } 

3. Worlds as before 

    data World = World Store Label

4. TIO actions are 

    type TIO a = World -> (World, a)

 -}