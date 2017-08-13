module LambdaTermsContext where

import Common

import qualified Data.Map.Strict as M

  -- Componete 1: tabla con los lambda términos definidos por el usuario.
  -- Clave: Nombre.
  -- Valor: Tupla que puede contener el lambda término, y su tipo.
  -- Componente 2: Nombres.
type Context = (M.Map String (Maybe LTerm2, DoubleType), [String])

size :: Context -> Int
size = M.size . fst

lookup :: String -> Context -> Maybe (Maybe LTerm2, DoubleType)
lookup k = M.lookup k . fst

insert :: String -> LTerm2 -> DoubleType -> Context -> Context
insert n x y (t, ns)= (M.insert n (Just x, y) t, n:ns)

fromList :: [(String, LTerm2, DoubleType)] -> Context
fromList xs = (foldr (\(s,l,t) r -> M.insert s (Just l, t) r) M.empty xs, foldr (\(x,_,_) r -> x:r) [] xs)

member :: String -> Context -> Bool
member k = M.member k . fst

(!) :: Context -> String -> (Maybe LTerm2, DoubleType)
(!) (t,_) x = t M.! x

getNames :: Context -> [String]
getNames = snd
