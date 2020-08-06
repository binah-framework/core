module Binah where

-------------------------------------------------------------------------------
-- | Labels -------------------------------------------------------------------
-------------------------------------------------------------------------------
-- CURRENTLY BOGUS: should be a "SET OF USERS"
data Label = Label

cup :: Label -> Label -> Label
cup = undefined

leq :: Label -> Label -> Bool
leq = undefined


-------------------------------------------------------------------------------
-- | Stores -------------------------------------------------------------------
-------------------------------------------------------------------------------

-- | Addresses 
type Addr = Int

-- | Values
data Val = Val Int | Addr Addr

-- | Fields = Addresses + Labels
data Field = Field Addr Label

-- | Store
type Store = Addr -> Val

sel :: Store -> Addr -> Val
sel sto addr = sto addr

upd :: Store -> Addr -> Val -> Store
upd sto addr val = \a -> if a == addr then val else sto a

-------------------------------------------------------------------------------
-- | Tagged Computations ------------------------------------------------------
-------------------------------------------------------------------------------

-- | World 
data World = World 
  { wStore :: Store 
  , wLabel :: Label 
  }

{-@ 
   data TIO <l_can, l_does> a = TIO 
     { 
        l:{Label | l_does \subseteq l} -> ( {l':Label | l \cap l_can \subseteq l'}, a )
     }
  @-}

-- | TIO Computations
data TIO a = TIO (World -> (World, a))

{-@ abort :: {v:_ | false} -> a @-}
abort :: () -> a
abort _ = error "abort"

-------------------------------------------------------------------------------
-- | API ----------------------------------------------------------------------
-------------------------------------------------------------------------------

-- ret :: a -> TIO <True,False> a 
ret :: a -> TIO a
ret x = TIO (\w -> (w, x))

-- bind :: forall l2' \subseteq l1. TIO<l1, l1'> a -> (a -> TIO <l2, l2'> b) -> TIO <l1 \cap l2, l2' \cup l2'> b
bind :: TIO a -> (a -> TIO b) -> TIO b
bind (TIO t1) t2 = TIO $ \w ->
  let (w', v1) = t1 w
      TIO f2   = t2 v1
  in  f2 w'

-- get :: Field <l> v -> TIO <l, False> a
get :: Field -> TIO Val
get (Field a l) = TIO $ \(World sto lc) ->
    let lc' = lc `cup` l 
        v   = sto a
    in (World sto lc', v)

-- set :: Field <l> v -> v -> TIO <True, l> () 
set :: Field -> Val -> TIO ()
set (Field a l) v = TIO $ \(World sto lc) -> 
  if lc `leq` l then 
    (World (upd sto a v) lc, ())
  else
    abort ()

-- downgrade???
