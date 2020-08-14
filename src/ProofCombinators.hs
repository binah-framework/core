module ProofCombinators where

infixl 3 ?

{-@ (?) :: forall a b <pa :: a -> Bool, pb :: b -> Bool>. x:a<pa> -> b<pb> -> {v:a<pa> | v = x} @-}
(?) :: a -> b -> a
x ? _ = x
{-# INLINE (?)   #-}

