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
-- 3. Teoremas.
-- 4. Tipo a procesar.
-- OBS: Utilizamos esta función sobre tipos que NO requieren del contexto de tipos "ligados".
renamedType1 :: FTypeContext -> FOperations -> Theorems -> Type1
             -> Either ProofException DoubleType
renamedType1 ftc op te = renamedType (id, id, S.empty, S.empty) ftc op (theoremsNames te)

-- Retorna el tipo con nombre (renombrado), y sin nombre, del tipo dado
-- por el 5º argumento.
-- El renombramiento se realiza de modo tal que se respete la Convención 1.
-- OBS: Utilizamos esta función sobre tipos que requieren del contexto de tipos "ligados".
renamedType2 :: BTypeContext -> FTypeContext ->  FOperations -> Theorems
             -> Type1 -> Either ProofException DoubleType
renamedType2 bs ftc op te = renamedType (snd, bTypeVar, bs, bs) ftc op (theoremsNames te)

-- Retorna el tipo con nombre (renombrado), y sin nombre, del tipo dado
-- por el 5º argumento.
-- El renombramiento se realiza de modo tal que se respete la Convención 1.
-- OBS: Solo la utilizamos en el renombramiento del cuerpo de una operación.
renamedType3 :: S.Seq TypeVar -> FTypeContext ->  FOperations -> Theorems
             -> Type1 -> Either ProofException DoubleType
renamedType3 bs ftc op te = renamedType (id, id, bs, bs) ftc op (theoremsNames te)


-- Obtiene el tipo renombrado, y sin nombre, de su 5º arg.
renamedType :: (a -> TypeVar, TypeVar -> a, S.Seq a, S.Seq a) -> FTypeContext
            -> FOperations -> [String] -> Type1 -> Either ProofException DoubleType
renamedType (f, _, rs, bs) fs op _ (TVar x) =
  getVarType (\_ zs m -> f $ S.index zs m) (f, rs, bs) fs op x
renamedType (f, f', rs, bs) fs op tn (ForAll x t) =
  do let v = getRename x (f, rs) (id, fs) (fst4, op) (id, tn)
     tt <- renamedType (f, f', (f' v S.<| rs), (f' x S.<| bs)) fs op tn t
     return $ ForAll v tt
renamedType (f, f', rs, bs) fs op tn (Exists x t) =
  do let v = getRename x (f, rs) (id, fs) (fst4, op) (id, tn)
     tt <- renamedType (f, f', (f' v S.<| rs), (f' x S.<| bs)) fs op tn t
     return $ Exists v tt
renamedType frbs fs op tn (Fun t1 t2) =
  do tt1 <- renamedType frbs fs op tn t1
     tt2 <- renamedType frbs fs op tn t2
     return $ Fun tt1 tt2
renamedType frbs fs op tn (RenamedType s ts) =
  getOpType op s ts $ renamedType frbs fs op tn

basicTypeWithoutName :: FTypeContext -> FOperations -> Type1
                     -> Either ProofException DoubleType
basicTypeWithoutName = typeWithoutName (id, id, S.empty)

-- Obtiene el tipo sin nombre de su 4º arg.
typeWithoutName :: (a -> TypeVar, TypeVar -> a, S.Seq a) -> FTypeContext
                -> FOperations -> Type1 -> Either ProofException DoubleType
typeWithoutName (f, _, bs) fs op (TVar x) =
  case S.findIndexL (\w -> f w == x) bs of
    Just n -> return $ TVar (x, Bound n)
    Nothing -> case find (\w -> fst4 w == x) op of
                 Just a -> if getNumArgs a == 0
                           then return $ RenamedType x []
                           else throw $ OpE1 x
                 Nothing -> if elem x fs
                            then return $ TVar (x, Free x)
                            else throw $ TypeE x
typeWithoutName (f, f', bs) fs op (ForAll x t) =
  do tt <- typeWithoutName (f, f', f' x S.<| bs) fs op t
     return $ ForAll x tt
typeWithoutName (f, f', bs) fs op (Exists x t) =
  do tt <- typeWithoutName (f, f', f' x S.<| bs) fs op t
     return $ Exists x tt
typeWithoutName fbs fs op (Fun t1 t2) =
  do tt1 <- typeWithoutName fbs fs op t1
     tt2 <- typeWithoutName fbs fs op t2
     return $ Fun tt1 tt2
typeWithoutName fbs fs op (RenamedType s ts) =
  case find (\(x,_) -> x == s) notFoldeableOps of
    Just (_, args') ->
      if args' == args
      then do tt <- sequence $ map (typeWithoutName fbs fs op) ts
              return $ RenamedType s tt
      else throw $ OpE1 s
    Nothing ->
      do a <- maybeToEither (OpE2 s) $ find (\x -> fst4 x == s) op
         if getNumArgs a == args
           then do tt <- sequence $ map (typeWithoutName fbs fs op) ts
                   return $ RenamedType s tt
           else throw $ OpE1 s
  where args = length ts


renamedValidType1 :: Int -> BTypeContext -> FTypeContext
                  -> FOperations -> Theorems
                  -> DoubleType -> DoubleType
renamedValidType1 n bs ftc op te = positiveShiftAndRename n bs bs ftc op (theoremsNames te) 

renamedValidType2 :: Int -> BTypeContext -> FTypeContext
                  -> FOperations -> [String]
                  -> DoubleType -> DoubleType
renamedValidType2 n bs = positiveShiftAndRename n bs bs
  
-- Renombra las variables de tipo ligadas de un tipo válido.
-- Se asume que el tipo dado por el 7º arg. está bien formado. Es decir que,
-- NO tiene variables escapadas que no han sido declaradas en el contexto.
-- Argumentos:
-- 1. Corrimiento positivo.
-- 2. Conjunto de variables de tipo ligadas renombradas.
-- 3. Conjunto de variables de tipo ligadas no renombradas.
-- 4. Conjunto de variables de tipos libres.
-- 5. Operaciones.
-- 6. Nombres de teoremas.
-- 7. Tipo sobre el que se realiza el renombramiento.
positiveShiftAndRename :: Int -> BTypeContext -> BTypeContext
                       -> FTypeContext -> FOperations
                       -> [String] -> DoubleType -> DoubleType
positiveShiftAndRename 0 = \_ _ _ _ _ t -> t
positiveShiftAndRename n = positiveShiftAndRename' 0 n

positiveShiftAndRename' :: Int -> Int -> BTypeContext -> BTypeContext
                        -> FTypeContext -> FOperations
                        -> [String] -> DoubleType -> DoubleType
positiveShiftAndRename' m n rs bs fs op _ (TVar (a, b@(Bound x)))
  | x < m = case S.findIndexL (\(_,w) -> w == a) bs of
              Just i -> TVar (snd $ S.index rs i, b)
              Nothing -> error "error: positiveShiftAndRename', no debería pasar."
  | otherwise = TVar (a, Bound (x+n)) 
positiveShiftAndRename' _ _ _ _ _ _ _ (TVar (a, b@(Free x))) =
  TVar (a, b)
positiveShiftAndRename' m n rs bs fs op tn (ForAll x t) =
  let v = getRename x (snd, rs) (id, fs) (fst4, op) (id, tn)
  in ForAll v $ positiveShiftAndRename' (m+1) n (bTypeVar v S.<| rs) (bTypeVar x S.<| bs) fs op tn t
positiveShiftAndRename' m n rs bs fs op tn (Exists x t) =
  let v = getRename x (snd, rs) (id, fs) (fst4, op) (id, tn)
  in Exists v $ positiveShiftAndRename' (m+1) n (bTypeVar v S.<| rs) (bTypeVar x S.<| bs) fs op tn t
positiveShiftAndRename' m n rs bs fs op tn (Fun t1 t2) =
  Fun (positiveShiftAndRename' m n rs bs fs op tn t1) (positiveShiftAndRename' m n rs bs fs op tn t2)
positiveShiftAndRename' m n rs bs fs op tn (RenamedType s ts) =
  RenamedType s $ map (positiveShiftAndRename' m n rs bs fs op tn) ts

----------------------------------------------------------------------------------------------------------------------
-- Trasformadores de lambda términos: Se pasa de un lambda término con nombre, a uno renombrado y al equivalente sin nombre.

basicWithoutName :: FOperations -> FTypeContext -> Theorems -> LTerm1
                 -> Either ProofException DoubleLTerm
basicWithoutName op fs = withoutName op fs (S.empty) (empty, 0)
  

-- Genera el lambda término con renombre de variables de tipo, y el lambda término sin nombre.
-- Chequea que las variables de tipo sean válidas de acuerdo a los contexto de tipos
-- dados por 2º y 3º arg. En caso de ser necesario renombra las variables de tipo "ligadas".
-- Además, chequea que las variables de términos también sean válidas, de
-- acuerdo la longitud del contexto de variables de términos "iniciales", dado por el 4º arg.
-- Se asume que el 4º argumento es mayor o igual a cero.
-- El 1º argumento, es la tabla de operaciones "foldeables".
-- Obs: es util generar el lambda término con nombres renombrados para imprimir mejor los errores.
-- Se usa en el algoritmo de inferencia, y el comando exact.
withoutName :: FOperations -> FTypeContext -> BTypeContext -> (IntSet, Int) -> Theorems
            -> LTerm1 -> Either ProofException DoubleLTerm
withoutName op fs bs cnn te = withoutName' S.empty S.empty bs bs fs op cnn (theoremsNames te)

withoutName' :: S.Seq TermVar -> S.Seq TermVar -> BTypeContext -> BTypeContext -> FTypeContext
             -> FOperations -> (IntSet, Int) -> [String] -> LTerm1 -> Either ProofException DoubleLTerm
withoutName' ters tebs _ _ _ _ cnn _ w@(LVar x) =
  case S.elemIndexL x tebs of
    Just m -> return $ LVar (S.index ters m, Bound m)
    Nothing -> return $ LVar (x, getTermVar x cnn)
withoutName' ters tebs tyrs tybs fs op cnn tn (Abs x t e) =
  do let h = getRename x (id, ters) (id, S.empty) (id, S.empty) (id, [])
     t' <- renamedType (snd, \x -> (0, x), tyrs, tybs) fs op tn t
     ee <- withoutName' (h S.<| ters)(x S.<| tebs) tyrs tybs fs op cnn tn e
     return $ Abs h t' ee
withoutName' ters tebs tyrs tybs fs op cnn tn (e1 :@: e2) =
  do ee1 <- withoutName' ters tebs tyrs tybs fs op cnn tn e1
     ee2 <- withoutName' ters tebs tyrs tybs fs op cnn tn e2
     return $ ee1 :@: ee2
withoutName' ters tebs tyrs tybs fs op cnn tn (BAbs x e) =
  do let v = getRename x (snd, tyrs) (id, fs) (fst4, op) (id, [])
     ee <- withoutName' ters tebs (bTypeVar v S.<| tyrs) (bTypeVar x S.<| tybs) fs op cnn tn e
     return $ BAbs v ee
withoutName' ters tebs tyrs tybs fs op cnn tn (e :!: t) =
  do ee <- withoutName' ters tebs tyrs tybs fs op cnn tn e
     t' <- renamedType (snd, \x -> (0, x), tyrs, tybs) fs op tn t
     return $ ee :!: t'
withoutName' ters tebs tyrs tybs fs op cnn tn (EPack t e t') =
  do tt <- renamedType (snd, \x -> (0, x), tyrs, tybs) fs op tn t
     ee <- withoutName' ters tebs tyrs tybs fs op cnn tn e
     tt' <- renamedType (snd, \x -> (0, x), tyrs, tybs) fs op tn t'
     return $ EPack tt ee tt
withoutName' ters tebs tyrs tybs fs op cnn tn (EUnpack x y e1 e2) =
  do ee1 <- withoutName' ters tebs tyrs tybs fs op cnn tn e1
     let v = getRename x (snd, tyrs) (id, fs) (fst4, op) (id, [])
         h = getRename y (id, ters) (id, S.empty) (id, S.empty) (id, [])
     ee2 <- withoutName' (h S.<| ters) (y S.<| tebs) (bTypeVar v S.<| tyrs) (bTypeVar x S.<| tybs) fs op cnn tn e2
     return $ EUnpack h v ee1 ee2
withoutName' ters tebs tyrs tybs fs op cnn tn (e ::: t) =
  do ee <- withoutName' ters tebs tyrs tybs fs op cnn tn e
     t' <- typeWithoutName (snd, \x -> (0, x), tybs) fs op t
     return $ ee ::: t'

----------------------------------------------------------------------------------------------------------------------
-- Transformadores para aplicaciones ambiguas.

basicDisambiguatedTerm :: FTypeContext ->  FOperations -> GenTree String
                       -> Either ProofException (Either DoubleType DoubleLTerm)
basicDisambiguatedTerm ftc op = disambiguatedTerm S.empty ftc op (empty, 0)

-- Convierte a una aplicacion ambigua en una aplicación de tipos, o en una aplicación de lambda términos.
disambiguatedTerm :: BTypeContext -> FTypeContext ->  FOperations -> (IntSet, Int)
                  -> GenTree String -> Either ProofException (Either DoubleType DoubleLTerm)
disambiguatedTerm btc ftc op cnn t =
  case disambiguatedType btc ftc op t of
    Left (TypeE _) -> return $ Right $ disambiguatedLTerm cnn t
    Left e -> throw e
    Right ty -> return $ Left ty


disambiguatedType :: BTypeContext -> FTypeContext -> FOperations
                  -> GenTree String -> Either ProofException DoubleType
disambiguatedType bs fs op (Node x []) =
  getVarType (\w _ _ -> w) (snd, S.empty, bs) fs op x -- NO es necesario rs
disambiguatedType bs fs op (Node x xs) =
  getOpType op x xs $ disambiguatedType bs fs op


getVarType :: (TypeVar -> S.Seq a -> Int -> TypeVar)
           -> (a -> TypeVar, S.Seq a, S.Seq a) -> S.Seq String
           -> FOperations
           -> String -> Either ProofException DoubleType
getVarType fvar frbs@(f, rs, bs) fs op x =
  case S.findIndexL (\w -> f w == x) bs of
    Just n -> return $ TVar (fvar x rs n, Bound n)
    Nothing -> case find (\w -> fst4 w == x) op of
                 Just a -> if getNumArgs a == 0
                           then return $ RenamedType x []
                           else throw $ OpE1 x
                 Nothing -> if elem x fs
                            then return $ TVar (x, Free x)
                            else throw $ TypeE x

getOpType :: FOperations -> String -> [a]
          -> (a -> Either ProofException DoubleType)
          -> Either ProofException DoubleType
getOpType op s ts f =
  case find (\(x,_) -> x == s) notFoldeableOps of
    Just (_, args') ->
      if args' == args
      then do tt <- sequence $ map f ts
              return $ RenamedType s tt
      else throw $ OpE1 s
    Nothing ->
      do a <- maybeToEither (OpE2 s) $ find (\x -> fst4 x == s) op
         if getNumArgs a == args
           then do tt <- sequence $ map f ts
                   return $ RenamedType s tt
           else throw $ OpE1 s
  where args = length ts

-- Convierte una aplicacion en una aplicación de lambda términos, si es posible.
disambiguatedLTerm :: (IntSet, Int) -> GenTree String -> DoubleLTerm
disambiguatedLTerm cnn (Node x xs) =
  foldl (\r node ->
            let t = disambiguatedLTerm cnn node
            in r :@: t
        )
  (LVar (x, getTermVar x cnn)) xs
disambiguatedLTerm _ Nil = error "error: disambiguatedLTerm, no debería pasar."

getTermVar :: String -> (IntSet, Int) -> VarName TermVar
getTermVar x (cn, n) =
  case getHypothesisValue x of
    Just h  -> case getHypoPosition cn n h of
                 Just i -> Bound i
                 _      -> Free x       --Probable teorema
    Nothing -> Free x

bTypeVar :: TypeVar -> BTypeVar
bTypeVar x = (0, x)


-- Obtiene la substitución para la unificación, de acuerdo a la profundidad dada por el 1º argumento.
-- Realiza un corrimiento "negativo" de las variables de tipo escapadas.
-- Argumentos:
-- 1. Número de corrimiento.
-- 2. Tipo, con y sin nombre, sobre el que se realiza el corrimiento.
negativeShift :: Int -> DoubleType -> Maybe DoubleType
negativeShift = negativeShift' 0

negativeShift' :: Int -> Int -> DoubleType -> Maybe DoubleType
negativeShift' m n (TVar (t,t'@(Bound x)))
  | x < m = return $ TVar (t,t')
  | (m <= x) && (x < n) = Nothing
  | otherwise = return $ TVar (t, Bound $ x - n + m)
negativeShift' _ _ (TVar (t, t'@(Free f))) = return $ TVar (t,t')
negativeShift' m n (Fun t1 t2) =
  do x  <- negativeShift' m n t1
     y <- negativeShift' m n t2
     return $ Fun x y
negativeShift' m n (RenamedType s ts) =
  do ts' <- sequence $ map (negativeShift' m n) ts 
     return $ RenamedType s ts'
negativeShift' m n (ForAll v t) =
  do x <- negativeShift' (m+1) (n+1) t
     return $ ForAll v x
negativeShift' m n (Exists v t) =
  do x <- negativeShift' (m+1) (n+1) t
     return $ Exists v x


-- Realiza un corrimiento "positivo" sobre las variables de tipo ligadas "escapadas".
-- Argumentos:
-- 1. Número de corrimiento.
-- 2. Tipo sobre el que se realiza el corrimiento.
positiveShift :: Int -> DoubleType -> DoubleType
positiveShift 0 = id
positiveShift n = positiveShift' 0 n

positiveShift' :: Int -> Int -> DoubleType -> DoubleType
positiveShift' m n t@(TVar (x, Bound y))
  | y < m = t
  | otherwise = TVar (x, Bound (y+n))
positiveShift' _ _ t@(TVar (_, Free _)) = t
positiveShift' m n (ForAll v t) = ForAll v $ positiveShift' (m+1) n t
positiveShift' m n (Exists v t) = Exists v $ positiveShift' (m+1) n t
positiveShift' m n (Fun t1 t2) = Fun (positiveShift' m n t1) (positiveShift' m n t2)
positiveShift' m n (RenamedType op ts) = RenamedType op $ map (positiveShift' m n) ts

toNoName :: DoubleLTerm -> LTerm2
toNoName (LVar (_, x)) = LVar x
toNoName (Abs _ t e) = Abs () t (toNoName e)
toNoName (BAbs t e) = BAbs t (toNoName e)
toNoName (x :@: y) = toNoName x :@: toNoName y
toNoName (e :!: t) = toNoName e :!: t
toNoName (EPack t1 e t2) = EPack t1 (toNoName e) t1
toNoName (EUnpack v _ e1 e2) = EUnpack v () (toNoName e1) (toNoName e2)
toNoName (e ::: t) = toNoName e ::: t
