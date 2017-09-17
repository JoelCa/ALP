module LambdaTermDefinition where

import Common

import qualified Data.Map.Strict as M
import Data.Map.Internal.Debug (showTree)

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

fromList :: [(String, DoubleLTerm, DoubleType)] -> LamDefs
fromList xs = (foldr (\(s,l,t) r -> M.insert s (Just l, t) r) M.empty xs, foldr (\(x,_,_) r -> x:r) [] xs)

member :: String -> LamDefs -> Bool
member k = M.member k . fst

-- (!) :: LamDefs -> String -> (Maybe DoubleLTerm, DoubleType)
-- (!) (t,_) x = t M.! x

getType :: LamDefs -> String -> DoubleType
getType (t,_) x = snd $ t M.! x

getLamTerm :: LamDefs -> String -> Maybe DoubleLTerm
getLamTerm (t,_) x = fst $ t M.! x
  
getLamTable :: LamDefs -> [(String, (Maybe DoubleLTerm, DoubleType))]
getLamTable (t,_) = M.assocs t 

getNames :: LamDefs -> [String]
getNames = snd

showLamTable :: LamDefs -> String
showLamTable (t, _) = showTree t
