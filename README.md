# Storm Core


A formalization of a core / reference version of the `storm` library, which shows a statically
typed API for manipulating DB tables with *data dependent* security policies of the form:

```haskell
type Policy = Val -> Val -> Label
```

* [Labels](src/Labels.hs) is an implementation of a lattice of `Labels` (as sets of users)
* [LIO](src/LIO.hs) is an implementation of the basic `LIO` computations (`return`, `bind`, `label`, `unlabel`, etc.)
* [LIOCombinators](src/LIOCombinators.hs) implements `lmap`, `lmap2`, `filterM` etc using the monadic interface
* [Storm](src/Storm.hs) implements `Policy` and `Table` and shows how to implement DB queries using `filterM`
* [Storm2](src/Storm2.hs) refactors `Storm` so that table is packaged with its `Spec` 

## DB API

Note the (verified) implementation of select with the signature:

https://github.com/storm-framework/core/blob/master/src/Storm.hs#L205-L209

which says the "effect" of select  overapproximates (only) the labels of the rows that the select-pred evaluates to True on:

```haskell
{-@ select' :: p1:_ -> p2:_ -> l:_ -> pred:_ -> 
               (sv1:_ -> sv2:_ -> { (interpPred pred sv1 sv2) => leq (predLabel pred p1 p2 sv1 sv2) l }) ->
               TableP p1 p2 -> 
               TIO [ {r:RowP p1 p2 | interpPredR pred r} ] l S.empty 
  @-}
```

## Non-interference

The `TIO` type corresponds to computations of the form

```haskell
type TIO a I O = tw:{Label| leq tw O} -> ({tw':Label| leq tw' (join tw I)}, a)
```

... the rest of the non-interference pops right out of classic LIO guarantees, 
e.g. via the LIFTY paper (S4) or LWEB.

## TODO

- Extend this with `update` 
- Replicate something like the above directly with abstract refinements bounds
