module Hypothesis where

import qualified Data.IntSet as IS


-- Se obtiene la posición que ocupa la hipótesis dada por el 2º arg,
-- en el contexto de términos.
-- Argumentos:
-- 1. Cantidad de hipótesis del contexto de términos.
-- 2. Número de la hipótesis.
getHypoPosition :: IS.IntSet -> Int -> Int -> Maybe Int
getHypoPosition c n h
  | IS.member n c = Nothing
  | (h >= 0) && (h < n + IS.size c) = return $ h - IS.fold (\x k -> if k < h then succ x else x) 0 c
  | otherwise = Nothing

printHypothesis :: Int -> String
printHypothesis n = "H" ++ show n
