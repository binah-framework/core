-------------------------------------------------------------------------------
-- | Basic definitions of Users, Labels, Computations 
-------------------------------------------------------------------------------

module Labels where

import qualified Data.Set as S

-------------------------------------------------------------------------------
-- | Assertions ---------------------------------------------------------------
-------------------------------------------------------------------------------

{-@ abort :: {v:_ | false} -> a @-}
abort :: () -> a
abort _ = error "abort"

{-@ lAssert :: {b:_ | b} -> _ -> a @-}
lAssert :: Bool -> a -> a
lAssert True x = x
lAssert False _ = abort ()

-------------------------------------------------------------------------------
-- | Labels -------------------------------------------------------------------
-------------------------------------------------------------------------------
type User = Int

type Label = S.Set User

{-@ inline join @-}
join :: Label -> Label -> Label
join l1 l2 = S.intersection l1 l2 

{-@ inline meet @-}
meet :: Label -> Label -> Label
meet l1 l2 = S.union l1 l2 

{-@ inline leq @-}
leq :: Label -> Label -> Bool
leq l1 l2 = S.isSubsetOf l2 l1

