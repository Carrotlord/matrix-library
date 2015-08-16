-- Symbiotic - math library including linear algebra package, graphs package, and virtual database.
-- @author Jiangcheng Oliver Chu
module Symbiotic
( rref
, rrefi
, transpose
, countRows
, countCols
, mul
, mul'
, wellFormed
, add
, elemMul
, elementWise
, sub
, divide
, scale
, newMatrix
, newVector
, cross
, dot
) where

import Data.List
import Data.Maybe

follower [] = []
follower xs = tail xs

data MatrixHead = MatrixHead { pivotElems :: [Double], leftColumn :: [Double] }
matTail ms = map follower (follower ms)
matHead ms = MatrixHead (head ms) (map head (follower ms))
leftAugment :: (Fractional a) => [a] -> [[a]] -> [[a]]
leftAugment _ [] = []
leftAugment [] _ = []
leftAugment mv msh = (head mv : head msh) : leftAugment (follower mv) (follower msh)
(MatrixHead p c) `matCons` mt = p : leftAugment c mt

maxIndex xs = (length xs) - 1

toDoubleMatrix :: (Integral a) => [[a]] -> [[Double]]
toDoubleMatrix [] = []
toDoubleMatrix (m:ms) = (map fromIntegral m) : (toDoubleMatrix ms)

pivotRow :: (Fractional a, Eq a) => [[a]] -> [a]
pivotRow [] = []
pivotRow (m:ms) = if (head m) /= 0 then m else pivotRow ms

whereIsPivotRow :: (Fractional a, Eq a) => [[a]] -> Int
whereIsPivotRow [] = -1
whereIsPivotRow (m:ms) = if (head m) /= 0 then 0 else 1 + whereIsPivotRow ms

firstNonZero :: [Double] -> Double
firstNonZero [] = -1
firstNonZero (x:xs)
    | x /= 0.0  = x
    | otherwise = firstNonZero xs

isPivot :: (Fractional a, Eq a) => [a] -> Bool
isPivot [] = False
isPivot (m:ms)
    | m == 1.0  = True
    | m /= 0.0  = False
    | otherwise = isPivot ms

whereIsPivotRow' :: [[Double]] -> Int -> Int
whereIsPivotRow' [] _ = -1
whereIsPivotRow' ms edge
    | edge < (length ms) - 1 = whereIsPivotRow' (init ms) edge
    | otherwise = let m = last ms
                  in  if isPivot m then (length ms) - 1 else whereIsPivotRow' (init ms) edge

inverted :: (Eq a) => [a] -> Int -> Int -> Int -> a
inverted xs i j i'
    | i == i'   = xs !! j
    | j == i'   = xs !! i
    | otherwise = xs !! i'
swap :: (Eq a) => [a] -> Int -> Int -> [a]
swap xs i j = map (inverted xs i j) [0..(length xs - 1)]

scalePivot :: (Fractional a) => [a] -> [a]
scalePivot (m:ms) = 1.0 : let s = 1.0 / m in map (s*) ms

scaleHead :: (Fractional a) => [[a]] -> [[a]]
scaleHead [] = []
scaleHead (m:[]) = [scalePivot m]
scaleHead (m:ms) = (scalePivot m) : ms

scaleBy :: (Fractional a) => a -> [a] -> [a]
scaleBy s xs = map (s*) xs

subtractElements :: (Num a) => [a] -> [a] -> [a]
subtractElements upper lower = zipWith (-) upper lower

subtractPivot pivot other = let h = head other in subtractElements other (map (h*) pivot)
addPivotMultiples :: (Num a) => [[a]] -> [[a]]
addPivotMultiples [] = []
addPivotMultiples (m:ms) = m : [subtractPivot m n | n <- ms]

refOnce :: (Fractional a, Eq a) => [[a]] -> [[a]]
refOnce ms = addPivotMultiples (scaleHead (swap ms 0 (whereIsPivotRow ms)))

ref :: [[Double]] -> [[Double]]
ref ms = let r = refOnce ms
             ms' = (matHead r) `matCons` refOnce (matTail r)
             lastScale = (1.0 / firstNonZero (last ms'))
         in  init ms' ++ [scaleBy lastScale (last ms')]

rrefAt :: [[Double]] -> Int -> [[Double]]
rrefAt ms edge
    | edge >= length ms = ms
    | otherwise = let refm   = ref ms
                      i      = whereIsPivotRow' refm edge
                      pivot  = refm !! i
                      Just p = elemIndex 1.0 pivot
                  in  [subtractElements (refm !! j) (scaleBy ((refm !! j) !! p) pivot) | j <- [0..(i-1)]] ++
                      [refm !! k | k <- [i..(length ms) - 1]]

rref :: [[Double]] -> [[Double]]
rref ms = let maxedge = (length ms) - 1
          in  prettyZeros $ foldl rrefAt ms [maxedge, (maxedge - 1) .. 0]

refi = ref . toDoubleMatrix
rrefi = rref . toDoubleMatrix

prettyZeros :: [[Double]] -> [[Double]]
prettyZeros ys = [map (\x -> if x == -0.0 then 0.0 else x) y | y <- ys]

-- tranpose from Data.List

countRows ms = length ms
countCols [] = 0
countCols ms = length (head ms)

wellFormed :: [[Double]] -> Bool
wellFormed ms
    | null ms = True
    | null (head ms) = False
    | otherwise = all (\m -> (length m) == h) ms
    where h = length $ head $ ms

get ms i j = (ms !! i) !! j

summation f i n = sum [f j | j <- [i..n]]

mulEntry a b i j = summation (\k -> (get a i k) * (get b k j)) 0 ((countCols a) - 1)

mul :: [[Double]] -> [[Double]] -> Maybe [[Double]]
a `mul` b
    | countRows a /= countCols b = Nothing
    | otherwise = Just [[mulEntry a b i j | j <- [0..(countRows a) - 1]] | i <- [0..(countCols b) - 1]]

unjustify :: ([[Double]] -> [[Double]] -> Maybe [[Double]]) -> ([[Double]] -> [[Double]] -> [[Double]])
unjustify f = \a b -> fromMaybe [] (f a b)

mul' :: [[Double]] -> [[Double]] -> [[Double]]
a `mul'` b = unjustify mul a b

elementWise :: (Double -> Double -> Double) -> [[Double]] -> [[Double]] -> Maybe [[Double]]
elementWise f a b
    | countRows a /= countRows b || countCols a /= countCols b = Nothing
    | otherwise = Just [[(get a i j) `f` (get b i j) | j <- [0..((countCols a) - 1)]] | i <- [0..((countRows a) - 1)]]

add :: [[Double]] -> [[Double]] -> Maybe [[Double]]
a `add` b = elementWise (+) a b

elemMul :: [[Double]] -> [[Double]] -> Maybe [[Double]]
a `elemMul` b = elementWise (*) a b

sub :: [[Double]] -> [[Double]] -> Maybe [[Double]]
a `sub` b = elementWise (-) a b

divide :: [[Double]] -> [[Double]] -> Maybe [[Double]]
a `divide` b = elementWise (/) a b

newMatrix :: Double -> Int -> Int -> [[Double]]
newMatrix value rows cols = [[value | j <- [1..cols]] | i <- [1..rows]]

newVector :: Double -> Int -> [[Double]]
newVector value size = newMatrix value 1 size

scale :: Double -> [[Double]] -> [[Double]]
scale c ms = fromMaybe [] $ (newMatrix c (countRows ms) (countCols ms)) `elemMul` ms

cross :: [[Double]] -> [[Double]] -> [[Double]]
g `cross` h = let a = head g
                  b = head h
                  u = a !! 0
                  v = a !! 1
                  w = a !! 2
                  x = b !! 0
                  y = b !! 1
                  z = b !! 2
              in  [[v*z - w*y, w*x - u*z, u*y - v*x]]

dot :: [[Double]] -> [[Double]] -> Double
g `dot` h = let a = head g
                b = head h
                u = a !! 0
                v = a !! 1
                w = a !! 2
                x = b !! 0
                y = b !! 1
                z = b !! 2
            in  u*x + v*y + w*z

magnitude :: [[Double]] -> Double
magnitude b = sqrt $ sum $ map (\x -> x * x) (head b)

normalize :: [[Double]] -> [[Double]]
normalize b = scale (1 / (magnitude b)) b

-- http://en.wikipedia.org/wiki/Eigenvalue_algorithm
-- http://en.wikipedia.org/wiki/QR_algorithm
-- http://en.wikipedia.org/wiki/Jacobi_eigenvalue_algorithm
-- http://en.wikipedia.org/wiki/Divide-and-conquer_eigenvalue_algorithm
-- http://en.wikipedia.org/wiki/Power_iteration

initVector :: [[Double]] -> [[Double]]
initVector a = [[(fromIntegral ((17 * i) `mod` 61))::Double | i <- [1..(countRows a)]]]

powerIterationStep :: [[Double]] -> [[Double]] -> [[Double]]
powerIterationStep a b = normalize (fromMaybe [] (a `mul` b))

-- Composes a long list of functions together.
compose :: [a -> a] -> a -> a
compose fs v = foldl (flip (.)) id fs $ v

maxAbsEigenvalue a = (compose (replicate 1000 (powerIterationStep a))) (initVector a)
