module Hypothesis where

-- Se obtiene la posición que ocupa la hipótesis dada por el 2º arg,
-- en el contexto de términos.
-- Argumentos:
-- 1. Cantidad de hipótesis del contexto de términos.
-- 2. Número de la hipótesis.
getHypoPosition :: Int -> Int -> Maybe Int
getHypoPosition n h
  | (h >= 0) && (h < n) = return $ n - h - 1
  | otherwise = Nothing

printHypothesis :: Int -> String
printHypothesis n = "H" ++ show n
