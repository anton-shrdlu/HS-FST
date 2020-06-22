module Fst
    ( GenTrans(S)
    , states
    , sigma
    , NFST
    , DFST
--    , gamma
    , start
    , delta
    , finals
    , transduce
-- , compose
    ) where

import Control.Monad
import Data.Monoid
import Data.List (nub)
import Data.Set

-- Epsilon transitions that leave the state unchanged are ignored. 
-- This is a restriction on automata that ensures we can actually compute a **finite** output.
deltaStar :: (Monoid m, MonadPlus w, Eq m, Eq q) => (q -> Maybe s -> w (q, m)) -> (q, m) -> [s] -> w (q, m)
deltaStar _ (q, m) [] = return (q, m)
deltaStar d (q, m) (b:bs) = do
    (q', m') <- d q (Just b)
    (q'', m'') <- d q Nothing
    deltaStar d (q', m `mappend` m') bs `mplus` 
        if q'' /= q
          then deltaStar d (q'', m `mappend` m'') (b:bs)
          else mzero

transduce :: (Monoid m, MonadPlus w, Eq m, Eq q) => GenTrans q s m w -> [s] -> w m
transduce t bs = do
    (q, m) <- deltaStar (delta t) (start t, mempty) bs
    guard (q `elem` finals t)
    return m

-- NFSTs dont have epsilon transitions.
type NFST q s o = GenTrans q s [o] []
type DFST q s o = GenTrans q s [o] Maybe

data GenTrans q s m w = 
    S { states :: [q] 
      , sigma :: [s]
      -- , gamma :: m
      -- There is no meaningful notion of an output alphabet
      -- when dealing with more general monoids (i.e. anything
      -- that is not the free monoid).
      , start :: q
      -- Note that Maybe s is required, as transitions on the empty
      -- string are possible.
      , delta :: q -> Maybe s -> w (q,m)
      , finals :: [q]
      }
