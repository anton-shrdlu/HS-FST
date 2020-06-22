-- HSfst
-- This module was inspired by Yiding Hao's "Finite-state Optimality Theory: non-rationality of Harmonic Serialism".
-- Gen and all Constrains are FSTs, the evaluation mechanism is a regular old function.

module HSfst
     ( State
     , GEN
     , Sequence(SQ)
     , Constraint
     , CON
     , mkGen
     , mkMax
     , mkDep
     , mkId
     , mkPreds
     , mkMark
     , converge
     , converge'
     ) where

import Data.Maybe (mapMaybe, fromJust)
import Data.List (nub, inits)
import Fst

inAlph :: [a] -> [(Maybe a, Maybe a)]
inAlph as = [(a,b) | a <- Nothing : map Just as, b <- Nothing : map Just as]

-- GEN:
-- Gen is a NFST, since it produces a set of candidates rather than one output.
-- Step will come in handy for markedness constraints.
data State x = Start | Wait | Stop | Step x | End x deriving (Eq, Show)
type GEN a = NFST (State [a]) a (Maybe a, Maybe a)

-- Gen may change, delete or insert one symbol at any position, or do nothing at all.
-- as = input alphabet
mkGen :: Eq a => [a] -> GEN a 
mkGen as = S [Start,Wait,Wait] as Start delta finals  -- what is the role of State []?
    where 
        delta q (Just a) 
         | q `elem` [Start,Wait] =
         [(Wait,[(Just a,Just a)])] ++                               -- not changing anything yet
         [(Stop,[(Just a, Just b)]) | b <- as, a /= b] ++            -- changing one segment
         [(Stop,[(Just a, Just a),(Nothing,Just b)]) | b <- as] ++   -- inserting one segment behind the current
         [(Stop,[(Just a, Nothing )])]                               -- deleting one segment
        delta Start Nothing = [(Stop,[(Nothing, Just a)]) | a <- as] -- inserting in inital position
        delta Stop (Just a) =  [(Stop,[(Just a, Just a)])]           -- already done
        delta q Nothing = [(q, [])]                                  -- do nothing
        finals = [Start,Stop,Wait]                                   -- not inserting anything
                                               
-- CON:
-- CON is a ranking (=list) of DFSTs that produce lists of violations (True).
-- Because the transducer can't know if it has just read the final symbol,
-- False can cancel a preceding True.
-- In the paper CON is just the set of constraints and EVAL specifies the ranking, I think.
type Constraint a = DFST (State [a]) (Maybe a, Maybe a) Bool
type CON a = [Constraint a]

-- Faithfulness constraints:
-- as = input alphabet, p = which segments must not be deleted?
mkMax :: Eq a => [a] -> (a -> Bool) -> Constraint a
mkMax as p = S [Start] (inAlph as) Start delta [Start]
       where
              delta _ (Just (Just a, Nothing)) | p a       = return (Start, [True])
                                               | otherwise = return (Start, mempty) 
              delta _ _ = return (Start,[])

-- as = input alphabet, p = which segments must not be inserted?
mkDep :: Eq a => [a] -> (a -> Bool) -> Constraint a
mkDep as p = S [Start] (inAlph as) Start delta [Start]
       where
              delta _ (Just (Nothing,Just a)) | p a       = return (Start, [True])
                                              | otherwise = return (Start, mempty) 
              delta _ _ = return (Start,[])

-- as = input alphabet, c = if not c a b then give one violation!
mkId :: Eq a => [a] -> (a -> a -> Bool) -> Constraint a
mkId as c = S [Start] (inAlph as) Start delta [Start]
       where
              delta _ (Just (Just a, Just b)) | c a b     = return (Start, mempty)
                                              | otherwise = return (Start,[True])
              delta _ _ = return (Start,[])

-- Markedness constraints:
-- The bookending Bools mark the boundaries of the string: True = boundary; False = no boundary.
data Sequence a = SQ Bool [a] Bool deriving (Eq, Show)

-- for turning a list of symbols into a list of predicates:
mkPreds :: Eq a => Sequence a -> Sequence (a -> Bool)
mkPreds (SQ begin xs end) = SQ begin (map (==) xs) end

-- One sequence per constraint for now; possibly composition for more complex ones.
-- Number/names of states is determined by the number and length of banned strings.
-- (SQ False [] False) bans strings that are empty/only consist of deleted symbols. Is that ok?

mkMark :: Eq a => [a] -> Sequence (a -> Bool) -> Constraint a
mkMark as (SQ begin sq end)  = S states (inAlph as) Start delta states
       where
              states = Start : Wait : steps ++ prefinals
              prefinals | end = map End $ nub bannedStrings
                        | otherwise = []
           -- If abc is banned: 
           -- steps = [Step [],Step abc,Step ab,Step a] -- Step [] should be removed.
              steps = nub $ bannedStrings >>= (map Step . inits)
              bannedStrings = foldr ((<*>) . map (:)) [[]] (zipWith filter sq (repeat as))
              delta q (Just (_,Nothing)) = Just (q,[]) -- (_) segment was deleted; stay in current state.
              delta Start (Just (_,Just a)) 
               | null sq && begin && not end  = Just (Wait,[True])    -- (>) input started; exit start; violation! 
               | null sq && end               = Just (End [],[True])  -- (<) input could end; go to end; tentative violation? 
               | [a] `perfectMatch` sq && end = Just (End [a],[True]) -- (>xs<,xs<) xs seen; go to end; tentative violation?
               | [a] `perfectMatch` sq        = Just (Wait,[True])    -- (>xs,xs) xs seen; wait; violation!
               | Step [a] `elem` states       = Just (Step [a],[])    -- (>xs,xs,xs<,>xs<) x seen; progress; no violation.
               | otherwise                    = Just (Wait,[])        -- (_) no x seen; wait; no violation.
              delta Wait (Just (_,Just a)) 
               | begin = Just (Wait,[])                               -- (>,>xs,>xs<); wait forever; no violation.
               | [a] `perfectMatch` sq && end = Just (End [a],[True]) -- (xs<) xs seen; tentative violation?
               | [a] `perfectMatch` sq        = Just (Wait,[True])    -- (xs) xs seen; violation!
               | Step [a] `elem` states       = Just (Step [a],[])    -- (xs, xs<) x seen; progress; no violation.
               | otherwise                    = Just (Wait,[])        -- (_) no x seen; wait; no violation.
              delta (End xs) (Just (_,Just a)) 
               | not begin && null sq                     = Just (End xs,[])                        -- (<); input could end; stay in end; already violated.
               | begin || null (match (drop 1 xs ++ [a])) = Just (Wait,[False])                     -- (><,>xs<,xs<); xs seen, begin or a doesn't belong; wait; cancel violation!
               | (drop 1 xs ++ [a]) `perfectMatch` sq     = Just (End (drop 1 xs ++ [a]),[])        -- (xs<); xs seen again; stay in end; already violated.
               | otherwise                                = Just (Step (match $ xs ++ [a]),[False]) -- (xs<); some of xs seen; progress; cancel violation!
              delta (Step xs) (Just (_,Just a)) 
               | (xs ++ [a]) `perfectMatch` sq && end          = Just (End (xs ++ [a]),[True])          -- (>xs,>xs<); xs seen; go to end; tentative violation?
               | (xs ++ [a]) `perfectMatch` sq
                 && (begin || null (match $ drop 1 xs ++ [a])) = Just (Wait,[True])                     -- (>xs,xs) xs seen, begin or a doesn't belong; wait; violation! 
               | (xs ++ [a]) `perfectMatch` sq && not begin    = Just (Step (match $ xs ++ [a]),[True]) -- (xs) xs seen, a does belong; progress; violation!
               | null (match (xs ++ [a])) || begin             = Just (Wait,[])                         -- (>xs,xs,xs<,>xs<) a doesn't belong; wait; no violation.
               | otherwise                                     = Just (Step (match $ xs ++ [a]),[])     -- (>xs,xs,xs<,>xs<) a does belong; progress; no violation.
              delta x Nothing = Just (x,[]) -- don't do anything in between inputs!
              match [] = []
              match current | Step current `elem` states = current
                            | otherwise = match $ tail current
              perfectMatch xs ps = and (zipWith ($) ps xs) && length xs == length ps

-- EVAL:
type Grammar a = (CON a, GEN a)

-- outputs an infinite stream of the most harmonic candidates
cycles :: (Eq a) => Grammar a -> [a] -> [[a]]
cycles (con, gen) = iterate (mapMaybe snd . bests con . transduce gen)
       where
             bests []     candidates = case candidates of
                                         (x:_) -> x
                                         _     -> error "some constraints may not be well-defined"
             bests _     [candidate] = candidate
             bests (c:cs) candidates = bests cs $ filter (or . fmap ((== bestValue) . balance) . transduce c) candidates
               where bestValue = minimum $ mapMaybe (fmap balance . transduce c) candidates
          -- Balance 'cancels' false violations:
             balance :: [Bool] -> [()] 
             balance [] = []
             balance (True:False:bs) = balance bs -- There is no instance for (False:bs) because False should always follow True
             balance (True:bs)       = ():balance bs 

-- outputs the final most harmonic candidate
converge :: Eq a => Grammar a -> [a] -> [a]
converge congen = dupl . cycles congen
       where dupl (x:y:ys) | x == y = x
                           | otherwise = dupl (y:ys)

-- outputs the most harmonic candidate at each step
converge' :: Eq a => Grammar a -> [a] -> [[a]]
converge' congen = dupl . cycles congen
       where dupl (x:y:ys) | x == y = [x]
                           | otherwise = x : dupl (y:ys)