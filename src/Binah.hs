module Binah where

import qualified Data.Set as S
import           Labels 

-------------------------------------------------------------------------------
-- | Stores -------------------------------------------------------------------
-------------------------------------------------------------------------------

-- | Addresses 
type Addr = Int

-- | Values
data Val = Val Int 

-- | Fields = Addresses + Labels
data Field = Field Addr Label

fAddr :: Field -> Addr
fAddr (Field a _) = a 

{-@ measure fLabel @-}
fLabel :: Field -> Label
fLabel (Field _ l) = l

-- | Labeled Fields

{-@ type FieldL L = {fld: Field | fLabel fld == L} @-}

-------------------------------------------------------------------------------
-- | Store API ----------------------------------------------------------------
-------------------------------------------------------------------------------
type Store = Addr -> Val

sel :: Store -> Addr -> Val
sel sto addr = sto addr

upd :: Store -> Addr -> Val -> Store 
upd sto addr val = \a -> if a == addr then val else sto a

-------------------------------------------------------------------------------
-- | World --------------------------------------------------------------------
-------------------------------------------------------------------------------
data World = World Store Label 
{-@ data World = World (Addr -> Val) Label @-}

{-@ measure wLabel @-}
wLabel :: World -> Label
wLabel (World _ l) = l

-------------------------------------------------------------------------------
-- | Tagged Computations ------------------------------------------------------
-------------------------------------------------------------------------------

type LIO a = World -> (World, a)
{-@ type TIO a In Out = 
      w:{World| leq (wLabel w) Out} 
      ->  ({w':World| leq (wLabel w') (join (wLabel w) In)}, a) 
  @-}

-------------------------------------------------------------------------------
-- | Lifty-S4 API -------------------------------------------------------------
-------------------------------------------------------------------------------

{-@ ret :: l:Label -> a -> TIO a l S.empty @-}
ret :: Label -> a -> LIO a
ret l x = \w -> (w, x)

{-@ bind :: l1:Label -> l1':Label -> l2:Label -> l2':{leq l1 l2'} 
        -> (TIO a l1 l1') 
        -> (a -> TIO b l2 l2')
        -> (TIO b {join l1 l2} {meet l1' l2'})  
 @-}
bind :: Label -> Label -> Label -> Label -> LIO a -> (a -> LIO b) -> LIO b
bind _ _ _ _ f1 k2 = \w ->
  let (w', v1) = f1 w
      f2       = k2 v1
  in f2 w'

{-@ get :: l:_ -> FieldL l -> TIO Val l S.empty @-}
get :: Label -> Field -> LIO Val
get _ (Field a l) = \(World sto lc) ->
  let lc' = lc `join` l 
      v   = sto a
  in
      (World sto lc', v)

{-@ set :: l0:Label -> f:Field -> Val -> TIO () {l0} {fLabel f} @-} 
set :: Label -> Field -> Val -> LIO ()
set _ (Field a l) v = \(World sto lc) -> 
  if lc `leq` l then 
    (World (upd sto a v) lc, ())
  else
    abort ()

{-@ downgrade :: lOut:Label -> l:Label 
              -> (w:{leq (wLabel w) lOut} -> (World, Bool)<{\w' b -> b => leq (wLabel w') (join l (wLabel w))}>) 
              -> TIO Bool l lOut 
  @-} 
downgrade :: Label -> Label -> LIO Bool -> LIO Bool  
downgrade _ l act = \w@(World sto lc) -> 
  let 
    llc                 = l `join` lc 
    (World sto' lc', b) = act w
  in 
    case b of
      True -> if lc' `leq` llc then
                (World sto' llc, b)
              else
                abort ()
      False -> (World sto' llc, b)

-------------------------------------------------------------------------------
-- | Tables ... ---------------------------------------------------------------
-------------------------------------------------------------------------------

{- style Tables 

1. Generalize Values and Store

    type Val   = Int

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