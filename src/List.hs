{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module List where

import qualified Data.Set as S

-------------------------------------------------------------------------------

data List = Cons Int List | Nil

{-@ reflect elems @-}
elems :: List -> S.Set Int
elems Nil        = S.empty
elems (Cons h t) = S.union (S.singleton h) (elems t) 

-------------------------------------------------------------------------------

{-@ reflect member @-}
member :: Int -> List -> Bool
member x Nil        = False
member x (Cons h t) = x == h || member x t 

{-@ thmMember :: x:_ -> l:_ -> { member x l = S.member x (elems l) } @-}
thmMember :: Int -> List -> () 
thmMember x Nil        = ()
thmMember x (Cons h t) = thmMember x t 

----------------------------------------------------------------------------------

{-@ reflect isOrd @-}
isOrd :: List -> Bool
isOrd (Cons h1 (Cons h2 t)) = h1 <= h2 && isOrd (Cons h2 t)
isOrd _                     = True

{-@ reflect member' @-}
member' :: Int -> List -> Bool
member' x Nil        = False
member' x (Cons h t) 
  | x == h           = True 
  | x <  h           = False
  | otherwise        = member' x t

----------------------------------------------------------------------------------

{-@ thmMember' :: x:_ -> l:{isOrd l} -> { member' x l = S.member x (elems l) } @-}
thmMember' :: Int -> List -> () 
thmMember' x (Cons h t) 
  | x == h       = ()
  | h <  x       = thmMember' x t 
  | otherwise    = lemMember' x h t
thmMember' x Nil = ()

{-@ lemMember' :: x:_ -> h:{x < h} -> t:{isOrd (Cons h t)} -> { not (S.member x (elems (Cons h t))) } @-}
lemMember' :: Int -> Int -> List -> ()
lemMember' x h Nil         = ()
lemMember' x h (Cons h1 t) = lemMember' x h1 t
