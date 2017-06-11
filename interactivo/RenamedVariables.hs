module RenamedVariables where

import Common
import Data.List (stripPrefix)
import Parser (getInt)
import Data.Char (intToDigit)

-- Crea una variable en base al 1º arg. "v", que no está en ninguna de las listas de variables.
-- Sabemos que "v" ocurre en el 2º arg. "xs".
-- newVar :: String -> [String] -> [String] -> String
-- newVar v xs ys
--   | elem v' xs = newVar v' xs ys
--   | otherwise = if elem v' ys
--                 then newVar v' ys xs
--                 else v'
--   where v' = v++"0"

-- getRename :: String -> [String] -> [String] -> String
-- getRename v fv rv 
--   | elem v rv = newVar v rv fv
--   | otherwise = if elem v fv
--                 then newVar v fv rv
--                 else v

-- Crea una string, que no está en ninguna de las listas dadas por el 2º argumento.
getRename :: Foldable t => String -> [t String] -> String
getRename s xs = s ++ [intToDigit (foldr (\x n -> succ (posfix s x) `max` n) 0 xs)]

posfix :: Foldable t => String -> t String -> Int
posfix s xs = foldr (\x i -> maybe i (\n -> max n i) $ getIntPosfix s x) (-1) xs
                     
getIntPosfix :: String -> String -> Maybe Int
getIntPosfix x y = do posf <- stripPrefix x y
                      getInt posf
