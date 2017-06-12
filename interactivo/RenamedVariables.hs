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
getRename :: (Foldable t1, Foldable t2, Foldable t3) => String -> (a -> String, t1 a)
          -> (b -> String, t2 b) -> (c -> String, t3 c) -> String
getRename s (f,xs) (g,ys) (h,zs) = s ++ [ intToDigit (succ (posfix s f xs)
                                                      `max` succ (posfix s g ys)
                                                      `max` succ (posfix s h zs)) ]

posfix :: Foldable t => String -> (a -> String) -> t a -> Int
posfix s f xs = foldr (\x i -> maybe i (max i) $ getIntPosfix s $ f x) (-1) xs
                     
getIntPosfix :: String -> String -> Maybe Int
getIntPosfix x y = do posf <- stripPrefix x y
                      getInt posf
