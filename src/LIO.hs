{-@ LIQUID "--reflection" @-}

-------------------------------------------------------------------------------
{- | Formalization of $\lambda_{LIO}$ from "LWeb" by Vazou et al., POPL 2019.
  TBind     ==> bind
  TReturn   ==> ret 
  TGetLabel ==> current
  TTLabel   ==> label   
  TUnLabel  ==> unlabel 
 -}
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

-------------------------------------------------------------------------------
-- | Computations
-------------------------------------------------------------------------------
type World = Label 
type LIO a = World -> (World, a)
{-@ type TIO a I O = tw:{World| leq tw O} -> ({tw':World| leq tw' (join tw I)}, a) @-}

-------------------------------------------------------------------------------
-- | LIO API ------------------------------------------------------------------
-------------------------------------------------------------------------------

-- aka Lifty-S4 `set`
{-@ current :: l:Label -> TIO Label l S.empty @-}
current :: Label -> LIO Label
current l = \w -> (w, w)

-------------------------------------------------------------------------------
{-@ label :: l0:_ -> l:_ -> a -> TIO (Labeled a) l0 l @-}
-------------------------------------------------------------------------------
label :: Label -> Label -> a -> LIO (Labeled a)
label _ l v = \lc -> 
  if lc `leq` l then 
    (lc, Labeled l v)
  else 
    abort ()

-------------------------------------------------------------------------------
{-@ unlabel :: l:Label -> {lv:_ | leq (lvLabel lv) l} -> 
               TIO {v:a | v = lvValue lv} l S.empty 
  @-}
-------------------------------------------------------------------------------
unlabel :: Label -> Labeled a -> LIO a 
unlabel _ (Labeled l v) = \lc -> 
  (lc `join` l, v)

-------------------------------------------------------------------------------
{-@ ret :: l:Label -> a -> TIO a l S.empty @-}
-------------------------------------------------------------------------------
ret :: Label -> a -> LIO a
ret l x = \w -> (w, x)

-------------------------------------------------------------------------------
{-@ bind :: l1:Label -> l1':Label -> l2:Label -> l2':{leq l1 l2'} 
        -> (TIO a l1 l1') 
        -> (a -> TIO b l2 l2')
        -> (TIO b {join l1 l2} {meet l1' l2'})  
 @-}
-------------------------------------------------------------------------------
bind :: Label -> Label -> Label -> Label -> LIO a -> (a -> LIO b) -> LIO b
bind _ _ _ _ f1 k2 = \w ->
  let (w', v1) = f1 w
      f2       = k2 v1
  in f2 w'

-------------------------------------------------------------------------------
{-@ downgrade :: c:Bool -> i:_ -> o:_ -> 
                 TIO {v:Bool| v => c} {if c then i else S.empty} o -> 
                 TIO {v:Bool| v => c} i o 
  @-}
-------------------------------------------------------------------------------
downgrade :: Bool -> Label -> Label -> LIO Bool -> LIO Bool  
downgrade _ l _ act = \lc -> 
  let 
    llc      = l `join` lc 
  in 
    case act lc of
      (lc', True)  -> lAssert (lc' `leq` llc) (llc, True) 
      (lc', False) -> (llc, False)

-- TODO: ideally, implement the above using `bind` and `current` ...

{- LIFTY paper implementation
downgrade f t = do 
  lc <- getLabel
  lb <- toLabeled ((labelOf f) ⊔ lc) t
  catchLIO (unlabel lb) (\_ -> return False)
-}