# Binah Core

An attempt to formalize a core version of the binah library.

I started with Nadia's S4 because I think I better understand the semantics and grasp what's going on.

There is a World which has a Store and a Label

```haskell
data Val = Val Int | Addr Addr
type Store = Addr -> Val
data World = World 
  { wStore :: Store 
  , wLabel :: Label 
  }
```

Now TIO is just a World-Transformer

data TIO a = TIO (World -> (World, a))

Actions are represented using Field
-- | Fields = Addresses + Labels
data Field = Field Addr Label
And  get , set  and bind and return are implemented thus -- the "types" are identical to S4 except they are hardwiring the Label = Set of (Users). (So lub = intersect, leq = superset etc.)
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
The KEY POINT is the refined data type for TIO  which looks like this:
   data TIO <l_can, l_does> a = TIO 
     { 
        l:{Label | l_does \subseteq l} -> ( {l':Label | l \cap l_can \subseteq l'}, a )
     }
That is, a TIO<l_can, l_does>  (the "meaning" of the label is the same as in S4, I'm just giving them names) is a function  that:
Requires that it be invoked in a world whose label l includes l_does
Ensures that the output world's label  l'  includes the intersection of l and l_can
On pencil-and-paper the above definition suffices to verify bind, return, set, get. What remains:
Downgrade I guess I just have to sit down and understand what's happening with it, don't yet follow (mostly because I haven't tried I confess!)
Representing Labels at the "type" level we'd want this to be abstract refinements (so we get refinement inference etc.) but at the "code" level we'd want it to be plain sets (so you can implement `leq`).
Both the above seem solvable though...
