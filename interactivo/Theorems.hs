module Theorems where

import Common

import qualified Data.Map.Strict as M

  -- Componete 1: tabla de teoremas.
  -- Clave: Nombre del teorema.
  -- Valor: El lambda término de la prueba.
  -- Componente 2: Nombres de los teoremas.
type Theorems = (M.Map String Term, [String])

size :: Theorems -> Int
size = M.size . fst

lookup :: String -> Theorems -> Maybe Term
lookup k = M.lookup k . fst

insert :: String -> Term -> Theorems -> Theorems
insert n x (t, ns)= (M.insert n x t, n:ns)

fromList :: [(String, Term)] -> Theorems
fromList xs = (M.fromList xs, foldr (\(x,_) r -> x:r) [] xs)

member :: String -> Theorems -> Bool
member k = M.member k . fst

(!) :: Theorems -> String -> Term
(!) (t,_) x = t M.! x

theoremsNames :: Theorems -> [String]
theoremsNames = snd
