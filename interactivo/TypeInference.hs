module TypeInference where

import Common
import Transformers (positiveShift, negativeShift)
import TypeSubstitution
import qualified Data.Map as M (lookup)
import qualified Data.Sequence as S


-- Algoritmo de inferencia de tipos de un lambda término.

basicTypeInference :: Theorems -> FOperations -> (LamTerm, Term)
                   -> Either ProofExceptions (Type, TType)
basicTypeInference = typeInference 0 S.empty

-- Infiere el tipo de un lambda término.
-- Suponemos que ninguna de las pruebas de los teoremas son recursivas.
-- Es decir, que su lambda término es recursivo.
-- Argumentos:
-- 1. Indica la profundidad (respecto al cuantificador "para todo")
-- desde la que se quiere inferir.
-- 2. Contexto de variables de términos, desde el que se quiere inferir.
-- 3. Lista de teoremas.
-- 4. Operaciones "foldeables".
-- 5. Lambda término con y sin nombre, al que se le quiere inferir su tipo.
typeInference :: Int -> TermContext -> Theorems -> FOperations
              -> (LamTerm, Term) -> Either ProofExceptions (Type, TType)
typeInference n c te op t = case typeInference' n c te op t of
                          Right r -> return r
                          Left e -> throw $ InferE (fst t) e

typeInference' :: Int -> TermContext -> Theorems -> FOperations
          -> (LamTerm, Term) -> Either InferExceptions (Type, TType)
typeInference' n _ te _ (_, Free (NGlobal x)) =
  case M.lookup x te of
    Just (_ ::: t) -> return t
    Nothing -> throw $ InferE1 x -- NO puede haber variables de términos libres que no sean teoremas.
    _ -> error "error: typeInference', no debería pasar."
typeInference' n c te _ (_, Bound x) =
  let (_,m,t,t') = S.index c x
  in return (t,positiveShift (n-m) t')
typeInference' n c te op (Abs _ _ e, Lam (t,t') e') =
  do (tt,tt') <- typeInference' n ((0,n,t,t') S.<| c) te op (e,e')
     return (Fun t tt, TFun t' tt')
typeInference' n c te op (App e1 e2, e1' :@: e2') =
  do tt1 <- typeInference' n c te op (e1, e1')
     case tt1 of
       (Fun t1 t2, TFun t1' t2') ->
         do (tt2, tt2') <- typeInference' n c te op (e2, e2')
            if compareTTypes op tt2' t1'
              then return (t2, t2')
              else throw $ InferE2 e2 t1
       _ -> throw $ InferE3 e1 "* -> *"
typeInference' n c te op (BAbs _ e, BLam v e') =
  do (t,t') <- typeInference' (n+1) c te op (e, e')
     return (ForAll v t, TForAll t')
typeInference' n c te op (BApp e _, e' :!: (t,t')) =
  do tt <- typeInference' n c te op (e, e')
     case tt of
       (ForAll _ t1, TForAll t1') ->
         return $ basicTypeSubs (t1,t1') (t,t')
       _ -> throw $ InferE3 e "forall *"
typeInference' n c te op (EPack _ e _, Pack t1 e' t@(Exists _ t2 , TExists t2')) =
  do (_,tt1') <- typeInference' n c te op (e, e')
     let (tt2, tt2') = basicTypeSubs (t2,t2') t1
     if compareTTypes op tt1' tt2'
       then return t
       else throw $ InferE2 e tt2
typeInference' n c te op (EUnpack _ _ e1 e2, Unpack _ e1' e2') =
  do t1 <- typeInference' n c te op (e1, e1')
     case t1 of
       (Exists _ tt1, TExists tt1') -> 
         do t2 <- typeInference' (n+1) ((0,n+1,tt1,tt1') S.<| c) te op (e2, e2')
            case negativeShift 1 t2 of
              Just t2' -> return t2'
              Nothing -> throw $ InferE4 e2
       _ -> throw $ InferE3 e1 "exists *"
typeInference' n c te op (As e _, e' ::: t@(tt,tt')) =
  do (_, t1') <- typeInference' n c te op (e, e')
     if compareTTypes op t1' tt'
       then return t
       else throw $ InferE2 e tt


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
