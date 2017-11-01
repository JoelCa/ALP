module Hypothesis where

import Common (TermVar, TermContext)
import qualified Data.IntSet as IS
import Control.Monad (unless, when)
import Parser (getHypothesisValue)
import Data.Sequence (findIndexL)

type ConflictNames = (IS.IntSet, Int)

emptyCN :: ConflictNames
emptyCN = (IS.empty, 0)

insertCN :: ConflictNames -> Int -> ConflictNames
insertCN (cn, n) x = (IS.insert x cn, n+1)

-- Retorma la cantidad de hipótesis menores a la
-- hipótesis del 2do. arg.
lessSize :: ConflictNames -> Int -> Maybe Int
lessSize (cn, _) x = IS.foldr (\c r -> if c < x
                                       then (+1) <$> r
                                       else
                                         if c == x
                                         then Nothing
                                         else r) (Just 0) cn
sizeCN :: ConflictNames -> Int
sizeCN (_, n) = n

nullCN :: ConflictNames -> Bool
nullCN (cn, _) = IS.null cn

-- Cuenta la cantidad de hipótesis menores a la hipótesis del 1er arg.
-- Retorna además el resto de hipótesis.
count :: Int -> ConflictNames -> (Int, ConflictNames)
count i (cn, _) = IS.foldr (\x (m, r) ->
                              if x <= i
                              then (m+1, r)
                              else (m, insertCN r x)) (0, emptyCN) cn


-- Se obtiene la posición que ocupa la hipótesis dada por el 2º arg,
-- en el contexto de términos.
-- Argumentos:
-- 1. Contexto de términos, junto con su tamaño.
-- 2. Conjunto de nombres conflictivos.
-- 3. Número de la hipótesis (positivo).
getHypoPosition :: (TermContext, Int) -> ConflictNames -> Int -> Maybe Int
getHypoPosition (tc, n) h i
  | n < sizeCN h = let h' = "H" ++ show i
                   in findIndexL (\(s,_,_,_) -> s == h') tc
  | nullCN h = if n > i
                then return $ n - i - 1
                else Nothing
  | otherwise = do m <- lessSize h i
                   let r = n - 1 - i + m
                   unless (r >= 0) Nothing
                   return r

hypothesis :: Int -> ConflictNames -> TermVar
hypothesis i h = "H" ++ (show $ i + hypothesis' i h) 

hypothesis' :: Int -> ConflictNames -> Int
hypothesis' i h
  | nullCN h = 0
  | otherwise = let (n, h') = count i h
                in if n == 0
                   then 0
                   else n + hypothesis' (i+n) h'

isHypothesis :: String -> Bool
isHypothesis s = case getHypothesisValue s of
                   Just _ -> True
                   Nothing -> False
