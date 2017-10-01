module Hypothesis where

import Common (TermVar)
import qualified Data.IntSet as IS
import Control.Monad (unless, when)

-- Se obtiene la posición que ocupa la hipótesis dada por el 2º arg,
-- en el contexto de términos.
-- Argumentos:
-- 1. Conjunto de nombres conflictivos.
-- 2. Cantidad de hipótesis del contexto de términos.
-- 3. Número de la hipótesis.
getHypoPosition :: IS.IntSet -> Int -> Int -> Maybe Int
getHypoPosition h n i
  | IS.null h = return $ n - i - 1
  | otherwise = do let (pre, p , _) = IS.splitMember i h
                   when p Nothing
                   let r = n - 1 - i + IS.size pre
                   unless (r >= 0) Nothing
                   return r

hypothesis :: Int -> IS.IntSet -> TermVar
hypothesis i h = "H" ++ (show $ i + hypothesis' i h) 

hypothesis' :: Int -> IS.IntSet -> Int
hypothesis' i h
  | IS.null h = 0
  | otherwise = let (n, h') = count i h
                in if n == 0
                   then 0
                   else n + hypothesis' (i+n) h'

count :: Int -> IS.IntSet -> (Int, IS.IntSet)
count i h = (if p then n + 1 else n, post)
  where (pre,p,post) = IS.splitMember i h
        n = IS.size pre
