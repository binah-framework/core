module ProofCombinators where

infixl 3 ?

{-@ (?) :: forall a b <pa :: a -> Bool, pb :: b -> Bool>. a<pa> -> b<pb> -> a<pa> @-}
(?) :: a -> b -> a
x ? _ = x
{-# INLINE (?)   #-}

