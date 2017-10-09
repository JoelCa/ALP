module GlobalState where

import Common
import qualified Data.IntSet as IS
import qualified LambdaTermDefinition as LTD
import qualified TypeDefinition as TD
import qualified Data.Sequence as S
import Parser (getHypothesisValue)
import Hypothesis

-- Definiciones globales.
data GlobalState = Global { fTypeContext :: FTypeContext
                          , lamDef :: LTD.LamDefs           -- Lambda términos definidos.
                          , typeDef :: TD.TypeDefs          -- Tipos definidos.
                          , conflict :: ConflictNames       -- Nombres de expresiones conflictivas
                                                            -- con los nombres de hipótesis.
                          }


addEmptyLamTerm :: String -> DoubleType -> GlobalState -> GlobalState
addEmptyLamTerm name t g = g {lamDef = LTD.insertWithoutLamTerm name t $ lamDef g}

addLamTerm :: String -> DoubleLTerm -> DoubleType -> GlobalState -> GlobalState
addLamTerm name lt t g = g {lamDef = LTD.insertWithLamTerm name lt t $ lamDef g}

addType :: String -> TypeDefNoName -> GlobalState -> GlobalState
addType s d g = g {typeDef = TD.insert s d $ typeDef g}

-- Añade un nombre conflicto, si lo es.
addConflictName :: String -> GlobalState -> GlobalState
addConflictName s g = g {conflict = addConflictName' s $ conflict g}
  where addConflictName' s c =
          case getHypothesisValue s of
            Just n -> insertCN c n
            Nothing -> c

addConflictNames :: [String] -> GlobalState -> GlobalState
addConflictNames xs g = foldr addConflictName g xs


initialGlobal :: GlobalState
initialGlobal = Global { fTypeContext = S.empty
                       , lamDef = LTD.empty
                       , typeDef = TD.empty
                       , conflict = emptyCN
                       }

isLamDef :: String -> GlobalState -> Bool
isLamDef name g = LTD.member name $ lamDef g

isFreeVar :: String -> GlobalState -> Bool
isFreeVar name g = elem name $ fTypeContext g

isType :: String -> GlobalState -> Bool
isType name g = TD.member name $ typeDef g

invalidName :: String -> GlobalState -> Bool
invalidName name g =  isLamDef name g
                      || isFreeVar name g
                      || isType name g
                                 
addFreeVars :: S.Seq TypeVar -> GlobalState -> GlobalState
addFreeVars vars g = g {fTypeContext = vars S.>< fTypeContext g}

getLamTerm :: String -> GlobalState -> Maybe DoubleLTerm
getLamTerm name (Global {lamDef = te}) = LTD.getLamTerm te name

getLamTermType :: String -> GlobalState -> DoubleType
getLamTermType name (Global {lamDef = te}) = LTD.getType te name
