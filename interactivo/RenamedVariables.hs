module RenamedVariables where

import Common
import Data.List (stripPrefix)
import Parser (getInt)
import Data.Char (intToDigit)

-- Crea una string, que no está en ninguna de las estructuras t1, t2, t3.
getRename :: (Foldable t1, Foldable t2, Foldable t3) => String -> (a -> String, t1 a)
          -> (b -> String, t2 b) -> (c -> String, t3 c) -> String
getRename s (f,xs) (g,ys) (h,zs) =
  if p < -1  then s else s ++ [ intToDigit (succ p) ]
  where p = posfix s f xs
            `max` posfix s g ys
            `max` posfix s h zs

posfix :: Foldable t => String -> (a -> String) -> t a -> Int
posfix s f xs = foldr (\x i -> maybe i (max i) $ getIntPosfix s $ f x) (-2) xs
                     
getIntPosfix :: String -> String -> Maybe Int
getIntPosfix x y = do posf <- stripPrefix x y
                      if null posf
                        then return (-1)
                        else getInt posf
