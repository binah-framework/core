-- | Formalization of S4 from "Liquid Information Flow Control" by Polikarpova et al., ICFP 2020.

module Lifty where

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
