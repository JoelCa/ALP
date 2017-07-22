module TypeInference where

import Common
import Theorems (Theorems)
import qualified Theorems as T (lookup)
import Transformers (positiveShift, negativeShift)
import TypeSubstitution
import qualified Data.Sequence as S
import Data.Foldable (find)

-- Algoritmo de inferencia de tipos de un lambda término.

basicTypeInference :: Theorems -> FOperations -> DoubleLTerm
                   -> Either ProofExceptions DoubleType
basicTypeInference = typeInference 0 S.empty

-- Infiere el tipo de un lambda término.
-- Suponemos que ninguna de las pruebas de los teoremas son recursivas.
-- Es decir, que su lambda término es recursivo.
-- Argumentos:
-- 1. Indica la profundidad (respecto al cuantificador "para todo")
-- desde la que se quiere inferir.
-- 2. Contexto de variables de términos, desde el que se quiere inferir.
-- 3. Teoremas.
-- 4. Operaciones "foldeables".
-- 5. Lambda término con y sin nombre, al que se le quiere inferir su tipo.
typeInference :: Int -> TermContext -> Theorems -> FOperations
              -> DoubleLTerm -> Either ProofExceptions DoubleType
typeInference n c te op t = case typeInference' n c te op t of
                          Right r -> return r
                          Left e -> throw $ InferE t e

typeInference' :: Int -> TermContext -> Theorems -> FOperations
               -> DoubleLTerm -> Either InferExceptions DoubleType
typeInference' n _ te _ (LVar (_, Free x)) =
  case T.lookup x te of
    Just (_ ::: t) -> return t
    Nothing -> throw $ InferE1 x -- NO puede haber variables de términos libres que no sean teoremas.
    _ -> error "error: typeInference', no debería pasar."
typeInference' n c te _ (LVar (_, Bound x)) =
  let (_,m,t) = S.index c x
  in return $ positiveShift (n-m) t
typeInference' n c te op (Abs _ t e) =
  do tt <- typeInference' n ((0,n,t) S.<| c) te op e
     return $ Fun t tt
typeInference' n c te op (e1 :@: e2) =
  do tt1 <- typeInference' n c te op e1
     case tt1 of
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
     case tt of
       (ForAll _ t1) ->
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
     case t1 of
       (Exists _ tt1) -> 
         do t2 <- typeInference' (n+1) ((0,n+1,tt1) S.<| c) te op e2
            case negativeShift 1 t2 of
              Just t2' -> return t2'
              Nothing -> throw $ InferE4 e2
       _ -> throw $ InferE3 e1 "exists *"
typeInference' n c te op (e ::: t) =
  do t' <- typeInference' n c te op e
     if fullEqualTypes op t' t
       then return t
       else throw $ InferE2 e t


-- Compara los tipos sin nombres, extiende las operaciones "foldeables".
fullEqualTypes :: FOperations -> DoubleType -> DoubleType -> Bool
fullEqualTypes op (Fun t1 t2) (Fun t1' t2') = fullEqualTypes op t1 t1' && fullEqualTypes op t2 t2'
fullEqualTypes op (ForAll _ t) (ForAll _ t') = fullEqualTypes op t t'
fullEqualTypes op (Exists _ t) (Exists _ t') = fullEqualTypes op t t'
fullEqualTypes op (RenamedType s xs) (RenamedType s' ys)
  | s == s' = aux xs ys
  | otherwise = False
  where aux [] [] = True
        aux (x:xs) (y:ys) = if fullEqualTypes op x y
                            then aux xs ys
                            else False
fullEqualTypes op (RenamedType s xs) t =
  case find (\(a,_,_,_) -> a == s) op of
    Just (_,tt,args,_)-> fullEqualTypes op (typeSubsNoRename args tt xs) t
    Nothing -> error "error: fullEqualTypes, no debería pasar."
fullEqualTypes op t (RenamedType s ys) =
  case find (\(a,_,_,_) -> a == s) op of
    Just (_,tt,args,_)-> fullEqualTypes op t (typeSubsNoRename args tt ys)
    Nothing -> error "error: fullEqualTypes, no debería pasar."    
fullEqualTypes _ t1 t2 = t1 == t2
