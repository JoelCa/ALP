module LambdaTermDefinition where

import Common

import qualified Data.Map.Strict as M

  -- Componete 1: tabla de los lambda términos definidos.
  -- Clave: Nombre.
  -- Valor: Tupla que puede contener el lambda término, y su tipo.
  -- Componente 2: Nombres de los lambda términos en la componente 1.
type LamDefs = (M.Map String (Maybe DoubleLTerm, DoubleType), [String])

empty :: LamDefs
empty = (M.empty, [])

size :: LamDefs -> Int
size = M.size . fst

lookup :: String -> LamDefs -> Maybe (Maybe DoubleLTerm, DoubleType)
lookup k = M.lookup k . fst

insertWithLamTerm :: String -> DoubleLTerm -> DoubleType -> LamDefs -> LamDefs
insertWithLamTerm n x y (t, ns)= (M.insert n (Just x, y) t, n:ns)

insertWithoutLamTerm :: String -> DoubleType -> LamDefs -> LamDefs
insertWithoutLamTerm n y (t, ns)= (M.insert n (Nothing, y) t, n:ns)

member :: String -> LamDefs -> Bool
member k = M.member k . fst

getType :: LamDefs -> String -> DoubleType
getType (t,_) x = snd $ t M.! x

getLamTerm :: LamDefs -> String -> Maybe DoubleLTerm
getLamTerm (t,_) x = fst $ t M.! x
  
getLamTable :: LamDefs -> [(String, (Maybe DoubleLTerm, DoubleType))]
getLamTable (t,_) = M.assocs t 

getNames :: LamDefs -> [String]
getNames = snd
