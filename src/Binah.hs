module Binah () where

import qualified Data.Set as S

incr :: Int -> Int
incr x = x + 1

-- | Labels -------------------------------------------------------------------

-------------------------------------------------------------------------------
-- | Labels -------------------------------------------------------------------
-------------------------------------------------------------------------------
type User = Int

type Label = S.Set User

{-@ inline join @-}
join :: Label -> Label -> Label
join l1 l2 = S.intersection l1 l2 

{-@ inline meet @-}
meet :: Label -> Label -> Label
meet l1 l2 = S.union l1 l2 

{-@ inline leq @-}
leq :: Label -> Label -> Bool
leq l1 l2 = S.isSubsetOf l2 l1

-------------------------------------------------------------------------------
-- | Stores -------------------------------------------------------------------
-------------------------------------------------------------------------------

-- | Addresses 
type Addr = Int

-- | Values
data Val = Val Int | Addr Addr

-- | Fields = Addresses + Labels
data Field = Field Addr Label

fAddr :: Field -> Addr
fAddr (Field a _) = a 

{-@ measure fLabel @-}
fLabel :: Field -> Label
fLabel (Field _ l) = l

{-@ type FieldL L = {fld: Field | fLabel fld == L} @-}

-- | Store
sel :: (Addr -> Val) -> Addr -> Val
sel sto addr = sto addr

upd :: (Addr -> Val) -> Addr -> Val -> (Addr -> Val)
upd sto addr val = \a -> if a == addr then val else sto a

-------------------------------------------------------------------------------
-- | Tagged Computations ------------------------------------------------------
-------------------------------------------------------------------------------

-- | World 
data World = World (Addr -> Val) Label 
{-@ data World = World (Addr -> Val) Label @-}

{-@ measure wLabel @-}
wLabel :: World -> Label
wLabel (World _ l) = l

-- | Computations
type LIO a = World -> (World, a)
{-@ type TIO a Can Does = w:{World| leq (wLabel w) Does} -> ({w':World | leq (wLabel w') (join (wLabel w) Can)}, a) @-}

{-@ abort :: {v:_ | false} -> a @-}
abort :: () -> a
abort _ = error "abort"

-------------------------------------------------------------------------------
-- | API ----------------------------------------------------------------------
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

{-@ lAssert :: {b:_ | b} -> _ -> a @-}
lAssert :: Bool -> a -> a
lAssert True x = x
lAssert False _ = abort ()

-- downgrade???
