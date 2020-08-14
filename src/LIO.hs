{-@ LIQUID "--reflection" @-}
-------------------------------------------------------------------------------
-- | Formalization of $\lambda_{LIO}$ from "LWeb" by Vazou et al., POPL 2019.
-------------------------------------------------------------------------------

module LIO where

import qualified Data.Set as S
import                       Labels

-------------------------------------------------------------------------------
-- | Labeled Values -----------------------------------------------------------
-------------------------------------------------------------------------------

data Labeled a = Labeled Label a

{-@ measure lvLabel @-}
lvLabel :: Labeled a -> Label
lvLabel (Labeled l _) = l

{-@ measure lvValue @-}
lvValue :: Labeled a -> a 
lvValue (Labeled _ v) = v


{-@ type LabeledL a L = {v:Labeled a| lvLabel v == L} @-}

{- 
  TBind     ==> bind
  TReturn   ==> ret 
  TGetLabel ==> current
  TTLabel   ==> label   (aka set)
  TUnLabel  ==> unlabel (aka get) 

 -}
-------------------------------------------------------------------------------
-- | Computations
-------------------------------------------------------------------------------
type World = Label 

type LIO a = World -> (World, a)

{-@ type TIO a I O = tw:{World| leq tw O} -> ({tw':World| leq tw' (join tw I)}, a) @-}

-------------------------------------------------------------------------------
-- | LIO API ------------------------------------------------------------------
-------------------------------------------------------------------------------

{-@ current :: l:Label -> TIO Label l S.empty @-}
current :: Label -> LIO Label
current l = \w -> (w, w)

-- aka Lifty-S4 `set`
{-@ label :: l0:_ -> l:_ -> a -> TIO (Labeled a) l0 l @-}
label :: Label -> Label -> a -> LIO (Labeled a)
label _ l v = \lc -> 
  if lc `leq` l then 
    (lc, Labeled l v)
  else 
    abort ()

-- aka Lifty-S4 `get`
{-@ unlabel :: l:Label -> {lv:_ | leq (lvLabel lv) l} -> TIO {v:a | v = lvValue lv} l S.empty @-}
unlabel :: Label -> Labeled a -> LIO a 
unlabel _ (Labeled l v) = \lc -> 
  (lc `join` l, v)

-- a -> TIO a Top Bot 

-- forall l. a -> TIO a l Bot

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

-- {-@ downgrade :: lOut:Label -> l:Label 
--               -> (w:{leq w lOut} -> (World, Bool)<{\w' b -> b => leq w' (join l w)}>) 
--               -> TIO Bool l lOut 
--   @-} 

{-@ downgrade :: c:Bool -> i:_ -> o:_ -> 
                 TIO {v:Bool| v => c} {if c then i else S.empty} o -> 
                 TIO {v:Bool| v => c} i o 
  @-}
downgrade :: Bool -> Label -> Label -> LIO Bool -> LIO Bool  
downgrade _ l _ act = \lc -> 
  let 
    llc      = l `join` lc 
  in 
    case act lc of
      (lc', True)  -> lAssert (lc' `leq` llc) (llc, True) 
      (lc', False) -> (llc, False)

{- LIFTY paper implementation

downgrade f t = do 
  lc <- getLabel
  lb <- toLabeled ((labelOf f) ⊔ lc) t
  catchLIO (unlabel lb) (\_ -> return False)

-}

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



{- 
bot = S.full
top = S.empty
 -}