module TypeInference where

import Common
import LambdaTermDefinition (LamDefs)
import TypeDefinition
import Transformers (positiveShift, negativeShift)
import TypeSubstitution
import qualified Data.Sequence as S
import qualified LambdaTermDefinition as LTD (lookup)

-- Algoritmo de inferencia de tipos de un lambda término.

basicTypeInference :: LamDefs -> TypeDefs -> DoubleLTerm
                   -> Either SemanticException DoubleType
basicTypeInference = typeInference 0 S.empty

-- Infiere el tipo de un lambda término.
-- Suponemos que ninguna de las pruebas de los teoremas son recursivas.
-- Es decir, que su lambda término es recursivo.
-- Argumentos:
-- 1. Indica la profundidad (respecto al cuantificador "para todo")
-- desde la que se quiere inferir.
-- 2. Contexto de variables de términos, desde el que se quiere inferir.
-- 3. Lambda términos definidos.
-- 4. Tipos definidos.
-- 5. Lambda término con y sin nombre, al que se le quiere inferir su tipo.
typeInference :: Int -> TermContext -> LamDefs -> TypeDefs
              -> DoubleLTerm -> Either SemanticException DoubleType
typeInference n c te op t = case typeInference' n c te op t of
                              Right r -> return r
                              Left e -> throw $ InferE t e

typeInference' :: Int -> TermContext -> LamDefs -> TypeDefs
               -> DoubleLTerm -> Either InferException DoubleType
typeInference' _ _ te _ (LVar (_, Free x)) =
  case LTD.lookup x te of
    Just (_, t) -> return t
    Nothing -> throw $ InferE1 x -- NO puede haber variables de términos libres que no sean teoremas.
typeInference' n c _ _ (LVar (_, Bound x)) =
  let (_,_,m,Just t) = S.index c x
  in return $ positiveShift (n-m) t
typeInference' n c te op (Abs _ t e) =
  do tt <- typeInference' n (("", 0, n, Just t) S.<| c) te op e
     return $ Fun t tt
typeInference' n c te op (e1 :@: e2) =
  do tt1 <- typeInference' n c te op e1
     case basicType tt1 op of
       Fun t1 t2 ->
         do tt2 <- typeInference' n c te op e2
            if fullEqualTypes op tt2 t1
              then return t2
              else throw $ InferE2 e2 t1
       _ -> throw $ InferE3 e1 "* -> *"
typeInference' n c te op (BAbs v e) =
  do t <- typeInference' (n+1) c te op e
     return $ ForAll v t
typeInference' n c te op (e :!: t) =
  do tt <- typeInference' n c te op e
     case basicType tt op of
       ForAll _ t1 ->
         return $ basicTypeSubs t1 t
       _ -> throw $ InferE3 e "forall *"
typeInference' n c te op (EPack t1 e t@(Exists _ t2)) =
  do tt1' <- typeInference' n c te op e
     let tt2 = basicTypeSubs t2 t1
     if fullEqualTypes op tt1' tt2
       then return t
       else throw $ InferE2 e tt2
typeInference' n c te op (EUnpack _ _ e1 e2) =
  do t1 <- typeInference' n c te op e1
     case basicType t1 op of
       Exists _ tt1 -> 
         do t2 <- typeInference' (n+1) (("", 0, n+1, Just tt1) S.<| c) te op e2
            case negativeShift 1 t2 of
              Just t2' -> return t2'
              Nothing -> throw $ InferE4 e2
       _ -> throw $ InferE3 e1 "exists *"
typeInference' n c te op (e ::: t) =
  do t' <- typeInference' n c te op e
     if fullEqualTypes op t' t
       then return t
       else throw $ InferE2 e t

-- Compara los tipos, extiende la definición de los tipos.
fullEqualTypes :: TypeDefs -> DoubleType -> DoubleType -> Bool
fullEqualTypes op (Fun t1 t2) (Fun t1' t2') = fullEqualTypes op t1 t1' && fullEqualTypes op t2 t2'
fullEqualTypes op (ForAll _ t) (ForAll _ t') = fullEqualTypes op t t'
fullEqualTypes op (Exists _ t) (Exists _ t') = fullEqualTypes op t t'
fullEqualTypes op (RenamedType s xs) t2@(RenamedType s' ys)
  | s == s' = aux xs ys
  | otherwise =
      case getTypeData s op of
        Just (tt,args,_)-> fullEqualTypes op (typeSubsNoRename args tt xs) t2
        Nothing -> error "error: fullEqualTypes, no debería pasar."
  where aux [] [] = True
        aux (a:as) (b:bs) = if fullEqualTypes op a b
                            then aux as bs
                            else False
        aux _ _ = False
        
fullEqualTypes op (RenamedType s xs) t =
  case getTypeData s op of
    Just (tt,args,_) -> fullEqualTypes op (typeSubsNoRename args tt xs) t
    Nothing -> error "error: fullEqualTypes, no debería pasar."
fullEqualTypes op t (RenamedType s ys) =
  case getTypeData s op of
    Just (tt,args,_)-> fullEqualTypes op t (typeSubsNoRename args tt ys)
    Nothing -> error "error: fullEqualTypes, no debería pasar."    
fullEqualTypes _ t1 t2 = t1 == t2


-- Obtiene el tipo básico.
basicType :: DoubleType -> TypeDefs -> DoubleType
basicType (RenamedType s xs) op =
  case getTypeData s op of
    Just (tt,args,_) -> basicType (typeSubsNoRename args tt xs) op
    Nothing -> error "error: basicType, no debería pasar."
basicType t _ = t
