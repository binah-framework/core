{-@ LIQUID "--reflection" @-}

module LIOCombinators where

import qualified Data.Set as S
import                       Labels
import                       LIO

-------------------------------------------------------------------------------
-- | LIO Combinators (TODO: export?) ------------------------------------------
-------------------------------------------------------------------------------

{-@ lmap :: l:_ -> l':_ -> (a -> b) -> TIO a l l' -> TIO b l l' @-}
lmap :: Label -> Label -> (a -> b) -> LIO a -> LIO b
lmap l l' f act = bind l l' l S.empty act (\x -> ret l (f x))

{-@ lmap2 :: l:_ -> l':{leq l l'} -> (a -> b -> c) -> TIO a l l' -> TIO b l l' -> TIO c l l' @-}
lmap2 :: Label -> Label -> (a -> b -> c) -> LIO a -> LIO b -> LIO c
lmap2 l l' f act1 act2 =
  bind l l' l l' act1 (\x ->
    bind l l' l S.empty act2 (\y ->
      ret l (f x y)
    )
  )

{-@ filterM :: l:_ -> l':{leq l l'} -> (a -> TIO Bool l l') -> [a] -> TIO [a] l l' @-}
filterM :: Label -> Label -> (a -> LIO Bool) -> [a] -> LIO [a]
filterM l _  _ []     = ret l []
filterM l l' p (x:xs) = bind l l' l l' (p x) (\b ->
                          bind l l' l l' (filterM l l' p xs) (\ys ->
                            ret l (if b then x:ys else ys)
                          )
                        )

{-@ filterM' :: any:_ -> i:_ -> o:{leq i o} -> cond:(a -> Bool) ->
                (x:_ -> TIO {b:Bool | b => cond x} {if (cond x) then i else any} o) ->
                [a] ->
                TIO [{v:a | cond v}] i o
  @-}
filterM' :: Label -> Label -> Label -> (a -> Bool) -> (a -> LIO Bool) -> [a] -> LIO [a]
filterM' _ i _ _    p [] =
  ret i []
filterM' any i o cond p (x:xs) =
  bind i o i o (downgrade (cond x) i o (p x)) (\b ->
    bind i o i o (filterM' any i o cond p xs) (\ys ->
      ret i (if b then x:ys else ys)
    )
  )

{-@ filterM'' :: i:_ -> o:{leq i o} -> cond:(a -> Bool) ->
                 (x:_ -> TIO {b:Bool | b => cond x} {if (cond x) then i else S.empty} o) ->
                 [a] ->
                 TIO [{v:a | cond v}] i o
  @-}
filterM'' :: Label -> Label -> (a -> Bool) -> (a -> LIO Bool) -> [a] -> LIO [a]
filterM'' i _ _    p [] =
  ret i []
filterM'' i o cond p (x:xs) =
  bind i o i o (downgrade (cond x) i o (p x)) (\b ->
    bind i o i o (filterM'' i o cond p xs) (\ys ->
      ret i (if b then x:ys else ys)
    )
  )

{-@ mapM' :: l:_ -> l':{leq l l'} -> (a -> TIO b l l') -> [a] -> TIO [b] l l' @-}
mapM' :: Label -> Label -> (a -> LIO b) -> [a] -> LIO [b]
mapM' l _  _  []     = ret l []
mapM' l l' f (a: as) =
  bind l l' l l' (f a) (\b ->
    bind l l' l l' (mapM' l l' f as) (\bs ->
      ret l (b : bs)
    )
  )