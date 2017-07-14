module Transformers where

import Common
import Theorems (Theorems, theoremsNames)
import DefaultOperators
import Data.List (find)
import RenamedVariables
import Hypothesis
import Parser (getHypothesisValue)
import Data.IntSet (IntSet, empty)
import qualified Data.Sequence as S

-- Retorna el tipo con nombre, posiblemente renombrado, de su 3º arg.
-- A fin de respetar la Convención 1.
-- Además, genera el tipo sin nombre.
-- Argumentos:
-- 1. Varibles de tipo libres.
-- 2. Operaciones "foldeables".
-- 3. Tipo a procesar.
-- OBS: Utilizamos esta función sobre tipos que NO requieren del contexto de tipos "ligados".
renamedType1 :: FTypeContext -> FOperations -> Theorems -> Type
             -> Either ProofExceptions (Type, TType)
renamedType1 ftc op te = renamedType (id, id, S.empty, S.empty) ftc op (theoremsNames te)

-- Retorna el tipo con nombre (renombrado), y sin nombre, del tipo dado
-- por el 4º argumento.
-- El renombramiento se realiza de modo tal que se respete la Convención 1.
-- OBS: Utilizamos esta función sobre tipos que requieren del contexto de tipos "ligados".
renamedType2 :: BTypeContext -> FTypeContext ->  FOperations -> Theorems
             -> Type -> Either ProofExceptions (Type, TType)
renamedType2 bs ftc op te = renamedType (snd, bTypeVar, bs, bs) ftc op (theoremsNames te)

-- Retorna el tipo con nombre (renombrado), y sin nombre, del tipo dado
-- por el 4º argumento.
-- El renombramiento se realiza de modo tal que se respete la Convención 1.
-- OBS: Solo la utilizamos en el renombramiento del cuerpo de una operación.
renamedType3 :: S.Seq TypeVar -> FTypeContext ->  FOperations -> Theorems
             -> Type -> Either ProofExceptions (Type, TType)
renamedType3 bs ftc op te = renamedType (id, id, bs, bs) ftc op (theoremsNames te)


-- Obtiene el tipo renombrado, y sin nombre, de su 4º arg.
renamedType :: (a -> TypeVar, TypeVar -> a, S.Seq a, S.Seq a) -> S.Seq TypeVar
            -> FOperations -> [String] -> Type -> Either ProofExceptions (Type, TType)
renamedType (f, _, rs, bs) fs op _ (B x) =
  getVarType (\_ zs m -> f $ S.index zs m) (f, rs, bs) fs op x
renamedType (f, f', rs, bs) fs op tn (ForAll x t) =
  do let v = getRename x (f, rs) (id, fs) (fst4, op) (id, tn)
     (tt,tt') <- renamedType (f, f', (f' v S.<| rs), (f' x S.<| bs)) fs op tn t
     return (ForAll v tt, TForAll tt')
renamedType (f, f', rs, bs) fs op tn (Exists x t) =
  do let v = getRename x (f, rs) (id, fs) (fst4, op) (id, tn)
     (tt,tt') <- renamedType (f, f', (f' v S.<| rs), (f' x S.<| bs)) fs op tn t
     return (Exists v tt, TExists tt')
renamedType frbs fs op tn (Fun t1 t2) =
  do (tt1, tt1') <- renamedType frbs fs op tn t1
     (tt2, tt2') <- renamedType frbs fs op tn t2
     return (Fun tt1 tt2, TFun tt1' tt2')
renamedType frbs fs op tn (RenameTy s args ts) =
  getOpType op s args ts $ renamedType frbs fs op tn

-- Obtiene el tipo sin nombre de su 4º arg.
typeWithoutName :: (a -> TypeVar, TypeVar -> a, S.Seq a) -> S.Seq TypeVar
                -> FOperations -> Type -> Either ProofExceptions TType
typeWithoutName (f, _, bs) fs op (B x) =
  case S.findIndexL (\w -> f w == x) bs of
    Just n -> return $ TBound n
    Nothing -> case getElemIndex (\w -> fst4 w == x) op of
                 Just (n, a) -> if getNumArgs a == 0
                                then return $ RenameTTy n []
                                else throw $ OpE1 x
                 Nothing -> if elem x fs
                            then return $ TFree x
                            else throw $ TypeE x
typeWithoutName (f, f', bs) fs op (ForAll x t) =
  do tt <- typeWithoutName (f, f', f' x S.<| bs) fs op t
     return $ TForAll tt
typeWithoutName (f, f', bs) fs op (Exists x t) =
  do tt <- typeWithoutName (f, f', f' x S.<| bs) fs op t
     return $ TExists tt
typeWithoutName fbs fs op (Fun t1 t2) =
  do tt1 <- typeWithoutName fbs fs op t1
     tt2 <- typeWithoutName fbs fs op t2
     return $ TFun tt1 tt2
typeWithoutName fbs fs op (RenameTy s args ts) =
  case find (\(x,_,_) -> x == s) notFoldeableOps of
    Just (_,n,args') ->
      if args' == args
      then do tt <- sequence $ map (typeWithoutName fbs fs op) ts
              return $ RenameTTy n tt
      else throw $ OpE1 s
    Nothing ->
      do (m, a) <- maybeToEither (OpE2 s) $ getElemIndex (\x -> fst4 x == s) op
         if getNumArgs a == args
           then do tt <- sequence $ map (typeWithoutName fbs fs op) ts
                   return $ RenameTTy m tt
           else throw $ OpE1 s


renamedValidType :: BTypeContext -> FTypeContext ->  FOperations -> Theorems
                 -> Type -> Type
renamedValidType bs ftc op te = renamedValidType' bs bs ftc op (theoremsNames te) 
  
-- Renombra las variables de tipo ligadas de un tipo con nombre válido.
-- Se asume que el tipo dado por el 5º arg. está bien formado. Es decir que,
-- NO tiene variables escapadas que no han sido declaradas en el contexto.
-- Argumentos:
-- 1. Conjunto de variables de tipo ligadas renombradas.
-- 2. Conjunto de variables de tipo ligadas no renombradas.
-- 3. Conjunto de variables de tipos libres.
-- 4. Operaciones.
-- 5. Nombres de teorems.
-- 6. Tipo sobre el que se realiza el renombramiento.
renamedValidType' :: BTypeContext -> BTypeContext -> FTypeContext
                  -> FOperations -> [String] -> Type -> Type
renamedValidType' rs bs fs op _ (B x) =
  case S.findIndexL (\(_,w) -> w == x) bs of
    Just n -> B $ snd $ S.index rs n
    Nothing -> B x
renamedValidType' rs bs fs op tn (ForAll x t) =
  let v = getRename x (snd, rs) (id, fs) (fst4, op) (id, tn)
  in ForAll v $ renamedValidType' (bTypeVar v S.<| rs) (bTypeVar x S.<| bs) fs op tn t
renamedValidType' rs bs fs op tn (Exists x t) =
  let v = getRename x (snd, rs) (id, fs) (fst4, op) (id, tn)
  in Exists v $ renamedValidType' (bTypeVar v S.<| rs) (bTypeVar x S.<| bs) fs op tn t
renamedValidType' rs bs fs op tn (Fun t1 t2) =
  Fun (renamedValidType' rs bs fs op tn t1) (renamedValidType' rs bs fs op tn t2)
renamedValidType' rs bs fs op tn (RenameTy s args ts) =
  RenameTy s args $ map (renamedValidType' rs bs fs op tn) ts

----------------------------------------------------------------------------------------------------------------------
-- Trasformadores de lambda términos: Se pasa de un lambda término con nombre, a uno renombrado y al equivalente sin nombre.

basicWithoutName :: FOperations -> FTypeContext -> Theorems -> LamTerm
                 -> Either ProofExceptions (LamTerm, Term)
basicWithoutName op fs = withoutName op fs (S.empty) (empty, 0)
  

-- ARREGLAR: hacer renombre de tipos.
-- Genera el lambda término con renombre de variables de tipo, y el lambda término sin nombre.
-- Chequea que las variables de tipo sean válidas de acuerdo a los contexto de tipos
-- dados por 2º y 3º arg. En caso de ser necesario renombra las variables de tipo "ligadas".
-- Además, chequea que las variables de términos también sean válidas, de
-- acuerdo la longitud del contexto de variables de términos "iniciales", dado por el 4º arg.
-- Se asume que el 4º argumento es mayor o igual a cero.
-- El 1º argumento, es la tabla de operaciones "foldeables".
-- Obs: es util generar el lambda término con nombres renombramos para imprimir mejor los errores.
-- Se usa en el algoritmo de inferencia, y el comando exact.
withoutName :: FOperations -> FTypeContext -> BTypeContext -> (IntSet, Int) -> Theorems
            -> LamTerm -> Either ProofExceptions (LamTerm, Term)
withoutName op fs bs cnn te = withoutName' S.empty S.empty bs bs fs op cnn (theoremsNames te)

withoutName' :: S.Seq TermVar -> S.Seq TermVar -> BTypeContext -> BTypeContext -> FTypeContext
             -> FOperations -> (IntSet, Int) -> [String] -> LamTerm -> Either ProofExceptions (LamTerm, Term)
withoutName' ters tebs _ _ _ _ cnn _ w@(LVar x) =
  case S.elemIndexL x tebs of
    Just m -> return (LVar $ S.index ters m, Bound m)
    Nothing -> return (w, getTermVar x cnn)
withoutName' ters tebs tyrs tybs fs op cnn tn (Abs x t e) =
  do let h = getRename x (id, ters) (id, S.empty) (id, S.empty) (id, [])
     t' <- renamedType (snd, \x -> (0, x), tyrs, tybs) fs op tn t
     (ee, ee') <- withoutName' (h S.<| ters)(x S.<| tebs) tyrs tybs fs op cnn tn e
     return (Abs h (fst t') ee, Lam t' ee')
withoutName' ters tebs tyrs tybs fs op cnn tn (App e1 e2) =
  do (ee1, ee1') <- withoutName' ters tebs tyrs tybs fs op cnn tn e1
     (ee2, ee2') <- withoutName' ters tebs tyrs tybs fs op cnn tn e2
     return (App ee1 ee2, ee1' :@: ee2')
withoutName' ters tebs tyrs tybs fs op cnn tn (BAbs x e) =
  do let v = getRename x (snd, tyrs) (id, fs) (fst4, op) (id, [])
     (ee, ee') <- withoutName' ters tebs (bTypeVar v S.<| tyrs) (bTypeVar x S.<| tybs) fs op cnn tn e
     return (BAbs v ee, BLam v ee')
withoutName' ters tebs tyrs tybs fs op cnn tn (BApp e t) =
  do (ee, ee') <- withoutName' ters tebs tyrs tybs fs op cnn tn e
     t' <- renamedType (snd, \x -> (0, x), tyrs, tybs) fs op tn t
     return (BApp ee (fst t'), ee' :!: t')
withoutName' ters tebs tyrs tybs fs op cnn tn (EPack t e t') =
  do tt <- renamedType (snd, \x -> (0, x), tyrs, tybs) fs op tn t
     (ee, ee') <- withoutName' ters tebs tyrs tybs fs op cnn tn e
     tt' <- renamedType (snd, \x -> (0, x), tyrs, tybs) fs op tn t'
     return (EPack (fst tt) ee (fst tt'), Pack tt ee' tt')
withoutName' ters tebs tyrs tybs fs op cnn tn (EUnpack x y e1 e2) =
  do (ee1, ee1') <- withoutName' ters tebs tyrs tybs fs op cnn tn e1
     let v = getRename x (snd, tyrs) (id, fs) (fst4, op) (id, [])
         h = getRename y (id, ters) (id, S.empty) (id, S.empty) (id, [])
     (ee2, ee2') <- withoutName' (h S.<| ters) (y S.<| tebs) (bTypeVar v S.<| tyrs) (bTypeVar x S.<| tybs) fs op cnn tn e2
     return (EUnpack v h ee1 ee2, Unpack v ee1' ee2')
withoutName' ters tebs tyrs tybs fs op cnn tn (As e t) =
  do (ee, ee') <- withoutName' ters tebs tyrs tybs fs op cnn tn e
     t' <- typeWithoutName (snd, \x -> (0, x), tybs) fs op t
     return (As ee t, ee' ::: (t, t'))

----------------------------------------------------------------------------------------------------------------------
-- Transformadores para aplicaciones ambiguas.

basicDisambiguatedTerm :: FTypeContext ->  FOperations -> GenTree String
                       -> Either ProofExceptions (Either (Type, TType) (LamTerm, Term))
basicDisambiguatedTerm ftc op = disambiguatedTerm S.empty ftc op (empty, 0)

-- Convierte a una aplicacion ambigua en una aplicación de tipos, o en una aplicación de lambda términos.
disambiguatedTerm :: BTypeContext -> FTypeContext ->  FOperations -> (IntSet, Int)
                  -> GenTree String -> Either ProofExceptions (Either (Type, TType) (LamTerm, Term))
disambiguatedTerm btc ftc op cnn t =
  case disambiguatedType btc ftc op t of
    Left (TypeE _) -> return $ Right $ disambiguatedLTerm cnn t
    Left e -> throw e
    Right ty -> return $ Left ty


disambiguatedType :: BTypeContext -> FTypeContext -> FOperations
                  -> GenTree String -> Either ProofExceptions (Type, TType)
disambiguatedType bs fs op (Node x []) =
  getVarType (\w _ _ -> w) (snd, S.empty, bs) fs op x -- NO es necesario rs
disambiguatedType bs fs op (Node x xs) =
  getOpType op x (length xs) xs $ disambiguatedType bs fs op


getVarType :: (TypeVar -> S.Seq a -> Int -> TypeVar)
           -> (a -> TypeVar, S.Seq a, S.Seq a) -> S.Seq String
           -> FOperations
           -> String -> Either ProofExceptions (Type, TType)
getVarType fvar frbs@(f, rs, bs) fs op x =
  case S.findIndexL (\w -> f w == x) bs of
    Just n -> return (B $ fvar x rs n, TBound n)
    Nothing -> case getElemIndex (\w -> fst4 w == x) op of
                 Just (n, a) -> if getNumArgs a == 0
                                then return (RenameTy x 0 [], RenameTTy n [])
                                else throw $ OpE1 x
                 Nothing -> if elem x fs
                            then return (B x, TFree x)
                            else throw $ TypeE x

getOpType :: FOperations -> String -> Int -> [a]
          -> (a -> Either ProofExceptions (Type, TType))
          -> Either ProofExceptions (Type, TType)
getOpType op s args ts f =
  case find (\(x,_,_) -> x == s) notFoldeableOps of
    Just (_,n,args') ->
      if args' == args
      then do rs <- sequence $ map f ts
              let (tt, tt') = unzip rs
              return (RenameTy s args tt, RenameTTy n tt')
      else throw $ OpE1 s
    Nothing ->
      do (m, a) <- maybeToEither (OpE2 s) $ getElemIndex (\x -> fst4 x == s) op
         if getNumArgs a == args
           then do rs <- sequence $ map f ts
                   let (tt, tt') = unzip rs
                   return (RenameTy s args tt, RenameTTy m tt')
           else throw $ OpE1 s

-- Convierte una aplicacion en una aplicación de lambda términos, si es posible.
disambiguatedLTerm :: (IntSet, Int) -> GenTree String -> (LamTerm, Term)
disambiguatedLTerm cnn (Node x xs) =
  foldl (\r node ->
            let (t,t') = disambiguatedLTerm cnn node
                (tt,tt') = r
            in (App tt t, tt' :@: t')
        )
  (LVar x, getTermVar x cnn) xs
disambiguatedLTerm _ Nil = error "error: disambiguatedLTerm, no debería pasar."

getTermVar :: String -> (IntSet, Int) -> Term
getTermVar x (cn, n) =
  case getHypothesisValue x of
    Just h -> case getHypoPosition cn n h of
                Just i -> Bound i
                _ -> Free $ NGlobal x       --Probable teorema
    Nothing -> Free $ NGlobal x

bTypeVar :: TypeVar -> BTypeVar
bTypeVar x = (0, x)


-- Obtiene la substitución para la unificación, de acuerdo a la profundidad dada por el 1º argumento.
-- Realiza un corrimiento "negativo" de las variables de tipo escapadas.
-- Argumentos:
-- 1. Número de corrimiento.
-- 2. Tipo, con y sin nombre, sobre el que se realiza el corrimiento.
negativeShift :: Int -> (Type, TType) -> Maybe (Type, TType)
negativeShift = negativeShift' 0

negativeShift' :: Int -> Int -> (Type, TType) -> Maybe (Type, TType)
negativeShift' m n (t,t'@(TBound x))
  | x < m = return (t,t')
  | (m <= x) && (x < n) = Nothing
  | otherwise = return (t, TBound $ x - n + m)
negativeShift' _ _ (t, t'@(TFree f)) = return (t,t')
negativeShift' m n (Fun t1 t2,TFun t1' t2') =
  do (x,x') <- negativeShift' m n (t1,t1')
     (y,y') <- negativeShift' m n (t2,t2')
     return (Fun x y, TFun x' y')
negativeShift' m n (RenameTy s args ts, RenameTTy op ts') =
  do rs <- sequence $ map (negativeShift' m n) $ zip ts ts'
     let (xs,ys) =  unzip rs
     return (RenameTy s args xs, RenameTTy op ys)
negativeShift' m n (ForAll v t, TForAll t') =
  do (x,x') <- negativeShift' (m+1) (n+1) (t,t')
     return (ForAll v x, TForAll x')
negativeShift' m n (Exists v t, TExists t') =
  do (x,x') <- negativeShift' (m+1) (n+1) (t,t')
     return (Exists v x, TExists x')


-- Realiza un corrimiento "positivo" sobre las variables de tipo ligadas "escapadas".
-- Argumentos:
-- 1. Número de corrimiento.
-- 2. Tipo sin nombre sobre el que se realiza el corrimiento.
positiveShift :: Int -> TType -> TType
positiveShift 0 = id
positiveShift n = positiveShift' 0 n

positiveShift' :: Int -> Int -> TType -> TType
positiveShift' n r t@(TBound x)
  | x < n = t
  | otherwise = TBound (x+r)
positiveShift' _ _ t@(TFree x) = t
positiveShift' n r (TForAll t) = TForAll $ positiveShift' (n+1) r t
positiveShift' n r (TExists t) = TExists $ positiveShift' (n+1) r t
positiveShift' n r (TFun t1 t2) = TFun (positiveShift' n r t1) (positiveShift' n r t2)
positiveShift' n r (RenameTTy op ts) = RenameTTy op $ map (positiveShift' n r) ts
