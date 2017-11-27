module TypeDefinition where

import Common
import qualified Data.Map.Strict as M

-- Entorno de tipos.
-- 1. Conjunto de tipos (con nombre y sin nombre) definidos.
-- 2. Nombre de los tipos en 1.
type TypeDefs = (M.Map String TypeDefNoName, [String])

member :: String -> TypeDefs -> Bool
member x = M.member x . fst

empty :: TypeDefs
empty = (M.empty, [])

insert :: String -> TypeDefNoName -> TypeDefs -> TypeDefs
insert x y (d, xs) = (M.insert x y d, x:xs)

getTypeData :: String -> TypeDefs -> Maybe TypeDefNoName 
getTypeData s (t, _) = t M.!? s

getNumArgs :: String -> TypeDefs -> Maybe Int
getNumArgs s (t, _) = (\(_,y,_) -> y) <$> t M.!? s

getTypesNames :: TypeDefs -> [String]
getTypesNames = snd
