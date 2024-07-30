{-
    Fibonacci Heap
-}

module Fibonacci where

import qualified Data.Map as Map

-- WHEELS

-- Double linked circular lists
-- Implemented so all operations have amortized complexity O(1)

type Wheel a = ([a],[a])

{- A pair ([y1,..,yn],[z1,..,zm]) represents a circular lists
   with elements [y1,..,yn,zm,..,z1];
   the element to the right of z1 is y1, the element to the left of y1 is z1.
   The head element is y1
-}

-- read the head element
readW :: Wheel a -> a
readW ([], []) = error "Empty Wheel"
readW (x:_, _) = x
readW ([], ys) = last ys

-- wheel containing no elements
emptyW :: Wheel a
emptyW = ([], [])

-- test if a wheel is empty 
isEmptyW :: Wheel a -> Bool
isEmptyW ([], []) = True
isEmptyW _ = False

-- move the head to the next element clockwise
rightW :: Wheel a -> Wheel a
rightW ([], []) = emptyW
rightW ([x], []) = ([x], [])
rightW ([], [y]) = ([y], [])
rightW ([], ys) = rightW (reverse ys, [])
rightW (x:xs, ys) = (xs, x:ys)

-- move the head to the next element anti-clockwise
leftW :: Wheel a -> Wheel a
leftW ([], []) = emptyW
leftW ([x], []) = ([x], [])
leftW ([], [y]) = ([y], [])
leftW (xs, []) = (back:rest, [])
  where back = last xs
        rest = init xs
leftW (xs, y:ys) = (y:xs, ys)

-- insert a new element to the left of the head and set as new head
insertW :: a -> Wheel a -> Wheel a
insertW a ([], ys) = ([a], ys)
insertW a (xs, ys) = (a:xs, ys)

-- extract and delete the head, move the head to the next right
extractW :: Wheel a -> (a, Wheel a)
extractW ([], []) = error "Empty Wheel"
extractW ([x], []) = (x, ([], []))
extractW ([], [y]) = (y, ([], []))
extractW ([], ys) = extractW (reverse ys, [])
extractW (x:xs, ys) = (x, (xs, ys))

-- concatenate two wheels
--   the new head is the head of the first (if non-empty)
concatW :: Wheel a -> Wheel a -> Wheel a
concatW ([], []) ([], []) = emptyW
concatW (xs1, ys1) (xs2, ys2) = (wheel1, wheel2)
  where wheel1 = xs1 ++ xs2
        wheel2 = ys1 ++ ys2

-- FIBONACCI HEAP
{-
  A FH is a min-ordered tree consisting of
  a wheel of nodes each having a subtree
  Each node contains its degree
  We also keep track of the number of elements of the heap
-}

data FibHeap a = FHeap Int (Wheel (FHNode a))
  deriving Show

-- FHeap n w: a heap with n elements, consisting of a root wheel w

type FHNode a = (a, Int, FibHeap a)

-- (x,d,h) is an element with value x, degree d and sub-heap h


-- the Fibonacci heap with no elements
emptyFH :: FibHeap a
emptyFH = FHeap 0 emptyW

-- test if a heap is empty
isEmptyFH :: FibHeap a -> Bool
isEmptyFH (FHeap 0 emptyW) = True
isEmptyFH _ = False

-- Reading the minimum element
--  We assume that the head is heap-ordered,
--  so the minimum is the head of the root wheel
minimumFH :: FibHeap a -> a
minimumFH (FHeap _ w) = first (readW w)
  where first (x, _, _) = x

-- Inserting a new element into the heap
insertFH :: Ord a => a -> FibHeap a -> FibHeap a
insertFH x h@(FHeap n w)
  | isEmptyW w = FHeap (n+1) (insertW (x, 0, emptyFH) w)
  | x <= minimumFH h = FHeap (n+1) (insertW (x, 0, emptyFH) w)
  | otherwise = FHeap (n+1) (rightW (insertW (x, 0, emptyFH) w))

-- Merging two Fibonacci Heaps
unionFH :: Ord a => FibHeap a -> FibHeap a -> FibHeap a
unionFH h1@(FHeap n1 w1) h2@(FHeap n2 w2)
  | isEmptyFH h1 = h2
  | isEmptyFH h2 = h1
  | minimumFH h1 <= minimumFH h2 = FHeap (n1+n2) (concatW w1 w2)
  | otherwise = FHeap (n1+n2) (concatW w2 w1)

-- Extracting the minimum from a heap
extractFH :: Ord a => FibHeap a -> (a, FibHeap a)
extractFH (FHeap n w) =
  let ((x, d, FHeap _ wx), w') = extractW w
  in (x, consolidate (FHeap (n-1) (concatW wx w')))

link :: Ord a => FHNode a -> FHNode a -> FHNode a
link x@(kx, dx, hx) y@(ky, dy, hy)
  | kx <= ky = (kx, dx+1, insertN y hx)
  | otherwise = (ky, dy+1, insertN x hy)

insertN :: Ord a => FHNode a -> FibHeap a -> FibHeap a
insertN node@(k, d, h) heap@(FHeap n w)
  | isEmptyW w = FHeap (n+1) (insertW node w)
  | k <= minimumFH heap = FHeap (n+1) (insertW node w)
  | otherwise = FHeap (n+1) (rightW (insertW node w))

type NArray a = Map.Map Int (FHNode a)

insNA :: Ord a => FHNode a -> NArray a -> NArray a
insNA x@(kx, dx, hx) a =
  case Map.lookup dx a of
    Nothing -> Map.insert dx x a
    Just y -> insNA (link x y) (Map.delete dx a)

makeNA :: Ord a => Wheel (FHNode a) -> NArray a
makeNA w
  | isEmptyW w = Map.empty
  | otherwise = insNA x (makeNA w')
  where (x, w') = extractW w

toList :: NArray a -> [FHNode a]
toList = map snd.Map.toList

consolidate :: Ord a => FibHeap a -> FibHeap a
consolidate (FHeap n w) = FHeap n newWheel
  where
    nodes = toList (makeNA w)
    newWheel = foldr insNode emptyW nodes

    insNode x w
      | isEmptyW w = insertW x w
      | first x <= first (readW w) = insertW x w
      | otherwise = rightW (insertW x w)

    first (f, _, _) = f

-- main :: IO()
-- main = do
--   let wheel1 = ([1, 2, 3], [4, 5, 6])
--   let wheel2 = ([1, 2, 3], [])
--   let wheel3 = ([], [4, 5, 6])
--   let wheel4 = ([1, 2, 3], [4])
--   let wheel5 = ([3], [4, 5, 6])
--   let wheel6 = ([3], [4])
--   let wheel7 = ([1], [])
--   let wheel8 = ([], [6])
--   let wheel9 = ([], [])

--   putStrLn "Testing readW"
--   print (readW wheel1)
--   print (readW wheel3)

--   putStrLn "Testing isEmptyW"
--   print (isEmptyW wheel9)
--   print (isEmptyW wheel8)

--   putStrLn "Testing rightW"
--   print (rightW wheel8)
--   print (rightW wheel3)
--   print (rightW wheel7)
--   print (rightW wheel4)

--   putStrLn "Testing leftW"
--   print (leftW wheel2)
--   print (leftW wheel6)
--   print (leftW wheel3)

--   putStrLn "Testing insertW"
--   print (insertW 3 wheel3)
--   print (insertW 1 wheel9)

--   putStrLn "Testing extractW"
--   print (extractW wheel1)
--   print (extractW wheel3)

--   putStrLn "Testing concatW"
--   print (concatW wheel2 wheel3)
--   print (concatW wheel1 wheel4)

--   let fh = emptyFH

--   -- Inserting elements
--   let fh1 = insertFH 10 fh
--   let fh2 = insertFH 20 fh1
--   let fh3 = insertFH 5 fh2
--   let fh4 = insertFH 15 fh3
--   let fh5 = insertFH 25 fh4

--   putStrLn "Heap after insertions:"
--   print fh5

--   -- Extracting minimum
--   let (min1, fh6) = extractFH fh5
--   putStrLn "Extracted minimum:"
--   print min1
--   putStrLn "Heap after extracting minimum:"
--   print fh6

--   let (min2, fh7) = extractFH fh6
--   putStrLn "Extracted minimum:"
--   print min2
--   putStrLn "Heap after extracting minimum:"
--   print fh7

--   let (min3, fh8) = extractFH fh7
--   putStrLn "Extracted minimum:"
--   print min3
--   putStrLn "Heap after extracting minimum:"
--   print fh8

--   let (min4, fh9) = extractFH fh8
--   putStrLn "Extracted minimum:"
--   print min4
--   putStrLn "Heap after extracting minimum:"
--   print fh9

--   let (min5, fh10) = extractFH fh9
--   putStrLn "Extracted minimum:"
--   print min5
--   putStrLn "Heap after extracting minimum:"
--   print fh10