module Example where
import Control.Monad (forM_)

noOfStates = 6

newtype S = S Int deriving (Eq, Show) -- 0 .. noOfStates-1
data C = L | A | R deriving (Eq, Enum, Show)
left, ahead, right :: S -> S
left  (S i) = S $ (i-1) `mod` noOfStates
ahead = id
right (S i) = S $ (i+1) `mod` noOfStates

type V = Int

next :: S -> C -> S
next x L = left  x
next x A = ahead x
next x R = right x

reward :: S -> C -> S -> V
reward x c (S i') = (if i' == 0 then 2 else 0) -- reward for finding column zero
                  - (if c  == A then 0 else 1) -- cost of moving

val :: S -> [C] -> V
val x []      = 0
val x (c:cs)  = v + val x' cs
  where  x'  = next x c
         v   = reward x c x'

opt :: [C] ->   [C] -> S -> Bool
opt cs = \cs' x -> val x cs' <= val x cs

optExt :: [C] -> S -> C  -- [C] -> C would not work - different states make different controls optimal
optExt [] (S 0) = A
optExt [] (S 1) = L
optExt [] (S i) | i == noOfStates-1  = R
                | otherwise          = A
optExt cs x = argMax (\c->val x (c:cs))
-- Not correct

argMax :: (C -> V) -> C
argMax rew = toEnum $ bestIndex $ map rew [L,A,R]

bestIndex :: Ord v => [v] -> Int
bestIndex (v:vs) = go 0 0 v vs
  where  go i ibest best [] = ibest
         go i ibest best (v:vs)
           | v <= best  = go (i+1) ibest best vs
           | otherwise  = go (i+1) i     v    vs

showPolicy :: Show c => (S -> c) -> String
showPolicy p = show $ map (p.S) [0..noOfStates-1]

test1 = optExt []

test2 = optExt [A]

test3 css = mapM_ putStrLn $ map showPolicy $ map (\cs x -> (cs, val x cs)) css

test31 = test3 allCtrls1
test32 = test3 allCtrls2

lar = [L,A,R]
allCtrls1 = map (:[]) lar
allCtrls2 = crossWith (:) lar allCtrls1

crossWith :: (a->b->c) -> [a] -> [b] -> [c]
crossWith op xs ys = [op x y | y <- ys, x <- xs]
