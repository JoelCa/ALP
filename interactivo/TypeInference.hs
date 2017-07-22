module TypeInference where

import Common
import Theorems (Theorems)
import qualified Theorems as T (lookup)
import Transformers (positiveShift, negativeShift)
import TypeSubstitution
import qualified Data.Sequence as S


-- Algoritmo de inferencia de tipos de un lambda término.

basicTypeInference :: Theorems -> FOperations -> DoubleLTerm
                   -> Either ProofExceptions DoubleType
basicTypeInference = typeInference 0 S.empty

-- TERMINAR!!
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
                          Left e -> throw $ InferE (fst t) e

typeInference' :: Int -> TermContext -> Theorems -> FOperations
               -> DoubleLTerm -> Either InferExceptions DoubleType
typeInference' n _ te _ (TVar (_, Free x)) =
  case T.lookup x te of
    Just (_ ::: t) -> return t
    Nothing -> throw $ InferE1 x -- NO puede haber variables de términos libres que no sean teoremas.
    _ -> error "error: typeInference', no debería pasar."
typeInference' n c te _ (TVar (_, Bound x)) =
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
            if compareTypes op tt2 t1
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
     if compareTypes op tt1' tt2
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
     if compareTypes op t' t
       then return t
       else throw $ InferE2 e t


-- Compara los tipos sin nombres, extendiente las operaciones "foldeables".
compareTTypes :: FOperations -> TType -> TType -> Bool
compareTTypes op t1 t2 = basicTType op t1 == basicTType op t2

basicTType :: FOperations -> TType -> TType
basicTType _ t@(TBound x) = t
basicTType _ t@(TFree x) = t
basicTType op (TFun t t') = TFun (basicTType op t) (basicTType op t')
basicTType op (TForAll t) = TForAll (basicTType op t)
basicTType op (TExists t) = TExists (basicTType op t)
basicTType op (RenameTTy n xs) =
  case S.lookup n op of
    Just (_, (_, t), args, _) ->
      ttypeSubs args (basicTType op t) basics
      --in error $ show t ++ "\n\n" ++ show (applyTTypes l t basics)
    Nothing -> RenameTTy n basics
  where basics = map (basicTType op) xs
