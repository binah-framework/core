# Binah Core

An attempt to formalize a core version of the binah library.

* [Labels](src/Labels.hs) is an implementation of a lattice of `Labels` (as sets of users)
* [LIO](src/LIO.hs) is an implementation of the basic `LIO` computations (`return`, `bind`, `label`, `unlabel`, etc.)
* [LIOCombinators](src/LIOCombinators.hs) implements `lmap`, `lmap2`, `filterM` etc using the monadic interface
* [Binah](src/Binah.hs) implements `Policy` and `Table` and shows how to implement DB queries using `filterM`
