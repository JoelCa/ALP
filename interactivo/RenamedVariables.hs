module RenamedVariables where

import Data.List (stripPrefix)
import Parser (getInt, getHypothesisValue)

-- Renombra la string dada por el primer argumento, de modo tal de que no esté en ninguna de
-- las estructuras t1, t2, t3, t4, t5, ni tampoco en el espacio de nombre de las hipótesis.
getRename :: (Foldable t1, Foldable t2, Foldable t3, Foldable t4, Foldable t5)
          => String -> (a -> String, t1 a) -> (b -> String, t2 b) -> (c -> String, t3 c)
          -> (d -> String, t4 d) -> (e -> String, t5 e) -> String
getRename s (f,xs) (g,ys) (h,zs) (i, ws) (j, ts) =
  if p < -1  then s' else s' ++ show (succ p)
  where
    -- Hacemos este renombramiento para que "s" no
    -- este en el espacio de nombres de las hipótesis.
    s' = case getHypothesisValue s of
           Just _ ->
             (head s) : '_' : (tail s)
           Nothing ->
             s
    p = posfix s' f xs
        `max` posfix s' g ys
        `max` posfix s' h zs
        `max` posfix s' i ws
        `max` posfix s' j ts


posfix :: Foldable t => String -> (a -> String) -> t a -> Int
posfix s f xs = foldr (\x i -> maybe i (max i) $ getIntPosfix s $ f x) (-2) xs
                     
getIntPosfix :: String -> String -> Maybe Int
getIntPosfix x y = do posf <- stripPrefix x y
                      if null posf
                        then return (-1)
                        else getInt posf
