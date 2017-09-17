module TypeDefinition where

import Common
import qualified Data.Map.Strict as M
import Data.Map.Internal.Debug (showTree)

type TypeDefs = (M.Map String TypeDefNoName, [String])

member :: String -> TypeDefs -> Bool
member x = M.member x . fst

empty :: TypeDefs
empty = (M.empty, [])

insert :: String -> TypeDefNoName -> TypeDefs -> TypeDefs
insert x y (d, xs) = (M.insert x y d, x:xs)

getTypeData :: String -> TypeDefs -> Maybe TypeDefNoName 
getTypeData s (t, _) = t M.!? s

-- CHEQUEAR
getNumArgs :: String -> TypeDefs -> Maybe Int
getNumArgs s (t, _) = (\(_,y,_) -> y) <$> t M.!? s

getTypesNames :: TypeDefs -> [String]
getTypesNames = snd

showTypeTable :: TypeDefs -> String
showTypeTable (t, _) = showTree t
