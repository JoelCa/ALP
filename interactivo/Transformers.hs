module Transformers where

import Common
import RenamedVariables
import TypeDefinition hiding (empty)
import LambdaTermDefinition (LamDefs, getNames)
import Control.Monad (when)
import Data.Maybe (isJust)
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
renamedType1 :: FTypeContext -> TypeDefs -> LamDefs -> Type1
             -> Either SemanticException DoubleType
renamedType1 ftc op te = renamedType S.empty S.empty S.empty ftc op (getNames te)

-- Retorna el tipo con nombre (renombrado), y sin nombre, del tipo dado
-- por el 6º argumento.
-- El renombramiento se realiza de modo tal que se respete la Convención 1.
-- OBS: Utilizamos esta función sobre tipos que requieren del contexto de tipos "ligados".
renamedType2 :: BTypeContext -> TermContext -> FTypeContext ->  TypeDefs
             -> LamDefs -> Type1 -> Either SemanticException DoubleType
renamedType2 bs tc ftc op te = renamedType bs bs tc ftc op (getNames te)

-- Retorna el tipo con nombre (renombrado), y sin nombre, del tipo dado
-- por el 5º argumento.
-- El renombramiento se realiza de modo tal que se respete la Convención 1.
-- OBS: Solo la utilizamos en el renombramiento del cuerpo de una operación.
renamedType3 :: S.Seq TypeVar -> FTypeContext ->  TypeDefs -> LamDefs
             -> Type1 -> Either SemanticException DoubleType
renamedType3 bs ftc op te = renamedType bs' bs' S.empty ftc op (getNames te)
  where bs' = fmap typeVar0 bs


-- Obtiene el tipo renombrado, y sin nombre, de su 5º arg.
renamedType :: BTypeContext -> BTypeContext -> TermContext
            -> FTypeContext -> TypeDefs -> [String] -> Type1
            -> Either SemanticException DoubleType
renamedType rs bs tc fs op _ (TVar x) =
  transformTypeVar (\_ zs m -> fst $ S.index zs m) rs bs tc fs op x
renamedType rs bs tc fs op tn (ForAll x t) =
  do let v = getRename x (fst, rs) (id, fs) (id, getTypesNames op) (id, tn) (id, [])
     tt <- renamedType (typeVar0 v S.<| rs) (typeVar0 x S.<| bs) tc fs op tn t
     return $ ForAll v tt
renamedType rs bs tc fs op tn (Exists x t) =
  do let v = getRename x (fst, rs) (id, fs) (id, getTypesNames op) (id, tn) (id, [])
     tt <- renamedType (typeVar0 v S.<| rs) (typeVar0 x S.<| bs) tc fs op tn t
     return $ Exists v tt
renamedType rs bs tc fs op tn (Fun t1 t2) =
  do tt1 <- renamedType rs bs tc fs op tn t1
     tt2 <- renamedType rs bs tc fs op tn t2
     return $ Fun tt1 tt2
renamedType rs bs tc fs op tn (RenamedType s ts) =
  transformType op s ts $ renamedType rs bs tc fs op tn

basicTypeWithoutName :: FTypeContext -> TypeDefs -> Type1
                     -> Either SemanticException DoubleType
basicTypeWithoutName = typeWithoutName S.empty S.empty

-- Obtiene el tipo sin nombre de su 4º arg. No se realiza renombramientos.
typeWithoutName :: BTypeContext -> TermContext -> FTypeContext -> TypeDefs
                -> Type1 -> Either SemanticException DoubleType
typeWithoutName bs tc fs op (TVar x) =
  transformTypeVar (\w _ _ -> w) S.empty bs tc fs op x
typeWithoutName bs tc fs op (ForAll x t) =
  do tt <- typeWithoutName (typeVar0 x S.<| bs) tc fs op t
     return $ ForAll x tt
typeWithoutName bs tc fs op (Exists x t) =
  do tt <- typeWithoutName (typeVar0 x S.<| bs) tc fs op t
     return $ Exists x tt
typeWithoutName bs tc fs op (Fun t1 t2) =
  do tt1 <- typeWithoutName bs tc fs op t1
     tt2 <- typeWithoutName bs tc fs op t2
     return $ Fun tt1 tt2
typeWithoutName bs tc fs op (RenamedType s ts) =
  transformType op s ts $ typeWithoutName bs tc fs op


renamedValidType1 :: Int -> BTypeContext -> FTypeContext
                  -> TypeDefs -> LamDefs
                  -> DoubleType -> DoubleType
renamedValidType1 n bs ftc op te = positiveShiftAndRename n bs bs ftc (getTypesNames op) (getNames te) 

renamedValidType2 :: Int -> BTypeContext -> FTypeContext
                  -> [String] -> [String]
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
-- 5. Nombres de los tipos definidos.
-- 6. Nombres de los lambda términos definidos.
-- 7. Tipo sobre el que se realiza el renombramiento.
positiveShiftAndRename :: Int -> BTypeContext -> BTypeContext
                       -> FTypeContext -> [String]
                       -> [String] -> DoubleType -> DoubleType
positiveShiftAndRename 0 = \_ _ _ _ _ t -> t
positiveShiftAndRename n = positiveShiftAndRename' 0 n 

positiveShiftAndRename' :: Int -> Int -> BTypeContext -> BTypeContext
                        -> FTypeContext -> [String]
                        -> [String] -> DoubleType -> DoubleType
positiveShiftAndRename' m n rs bs _ _ _ (TVar (a, b@(Bound x)))
  | x < m = case S.findIndexL (\w -> fst w == a) bs of
              Just i -> TVar (fst $ S.index rs i, b)
              Nothing -> error "error: positiveShiftAndRename', no debería pasar."
  | otherwise = TVar (a, Bound (x+n)) 
positiveShiftAndRename' _ _ _ _ _ _ _ (TVar (a, b@(Free _))) =
  TVar (a, b)
positiveShiftAndRename' m n rs bs fs op tn (ForAll x t) =
  let v = getRename x (fst, rs) (id, fs) (id, op) (id, tn) (id, [])
  in ForAll v $ positiveShiftAndRename' (m+1) n (typeVar0 v S.<| rs) (typeVar0 x S.<| bs) fs op tn t
positiveShiftAndRename' m n rs bs fs op tn (Exists x t) =
  let v = getRename x (fst, rs) (id, fs) (id, op) (id, tn) (id, [])
  in Exists v $ positiveShiftAndRename' (m+1) n (typeVar0 v S.<| rs) (typeVar0 x S.<| bs) fs op tn t
positiveShiftAndRename' m n rs bs fs op tn (Fun t1 t2) =
  Fun (positiveShiftAndRename' m n rs bs fs op tn t1) (positiveShiftAndRename' m n rs bs fs op tn t2)
positiveShiftAndRename' m n rs bs fs op tn (RenamedType s ts) =
  RenamedType s $ map (positiveShiftAndRename' m n rs bs fs op tn) ts

----------------------------------------------------------------------------------------------------------------------
-- Trasformadores de lambda términos: Se pasa de un lambda término con nombre, a uno renombrado y al equivalente sin nombre.

basicWithoutName :: TypeDefs -> FTypeContext -> LamDefs -> LTerm1
                 -> Either SemanticException DoubleLTerm
basicWithoutName op fs = withoutName 0 S.empty S.empty op fs


-- Genera el lambda término con renombre de variables de tipo, y variables de término.
-- Chequea que las variables de tipo sean válidas de acuerdo al contexto de tipo.
-- En caso de ser necesario renombra las variables de tipo "ligadas".
-- Además, chequea que las variables de términos también sean válidas.
-- Se asume que el 1º argumento es mayor o igual a cero.
-- Obs: es util generar el lambda término con nombres renombrados para imprimir mejor los errores.
-- Se usa en el algoritmo de inferencia, y en el comando exact.
withoutName :: Int -> BTypeContext -> TermContext -> TypeDefs -> FTypeContext
            -> LamDefs -> LTerm1 -> Either SemanticException DoubleLTerm
withoutName i bs tc op fs te = withoutName' i tc tc bs bs fs op (getNames te)


withoutName' :: Int -> TermContext -> TermContext -> BTypeContext -> BTypeContext -> FTypeContext
             -> TypeDefs -> [String] -> LTerm1 -> Either SemanticException DoubleLTerm
withoutName' _ ters tebs _ tybs _ _ _ (LVar x) =
  do v <- getTermVar x tebs tybs
     case v of
       Just m -> return $ LVar (fst4 $ S.index ters m, Bound m)
       Nothing -> return $ LVar (x, Free x)
withoutName' i ters tebs tyrs tybs fs op tn (Abs x t e) =
  do let h = getRename x (fst4, ters) (fst, tyrs) (id, fs) (id, getTypesNames op) (id, tn)
     t' <- renamedType tyrs tybs tebs fs op tn t
     ee <- withoutName' (i+1) (termVar0 h S.<| ters) (termVar x i S.<| tebs) tyrs tybs fs op tn e
     return $ Abs h t' ee
withoutName' i ters tebs tyrs tybs fs op tn (e1 :@: e2) =
  do ee1 <- withoutName' i ters tebs tyrs tybs fs op tn e1
     ee2 <- withoutName' i ters tebs tyrs tybs fs op tn e2
     return $ ee1 :@: ee2
withoutName' i ters tebs tyrs tybs fs op tn (BAbs x e) =
  do let v = getRename x (fst4, ters) (fst, tyrs) (id, fs) (id, getTypesNames op) (id, tn)
     ee <- withoutName' i ters tebs (typeVar0 v S.<| tyrs) (typeVar x i S.<| tybs) fs op tn e
     return $ BAbs v ee
withoutName' i ters tebs tyrs tybs fs op tn (e :!: t) =
  do ee <- withoutName' i ters tebs tyrs tybs fs op tn e
     t' <- renamedType tyrs tybs tebs fs op tn t
     return $ ee :!: t'
withoutName' i ters tebs tyrs tybs fs op tn (EPack t e t') =
  do tt <- renamedType tyrs tybs tebs fs op tn t
     ee <- withoutName' i ters tebs tyrs tybs fs op tn e
     tt' <- renamedType tyrs tybs tebs fs op tn t'
     return $ EPack tt ee tt'
withoutName' i ters tebs tyrs tybs fs op tn (EUnpack x y e1 e2) =
  do ee1 <- withoutName' i ters tebs tyrs tybs fs op tn e1
     let v = getRename x (fst4, ters) (fst, tyrs) (id, fs) (id, getTypesNames op) (id, tn)
         h = getRename y (fst4, ters) (fst, tyrs) (id, fs) (id, getTypesNames op) (id, tn)
         -- CHEQUEAR indices i.
     ee2 <- withoutName' (i+2) (termVar0 h S.<| ters) (termVar y (i+1) S.<| tebs) (typeVar0 v S.<| tyrs) (typeVar x i S.<| tybs) fs op tn e2
     return $ EUnpack v h ee1 ee2
withoutName' i ters tebs tyrs tybs fs op tn (e ::: t) =
  do ee <- withoutName' i ters tebs tyrs tybs fs op tn e
     t' <- typeWithoutName tybs tebs fs op t
     return $ ee ::: t'

----------------------------------------------------------------------------------------------------------------------
-- Transformadores para aplicaciones ambiguas.

basicDisambiguatedTerm :: FTypeContext -> TypeDefs -> GenTree String
                       -> Either SemanticException (Either DoubleType DoubleLTerm)
basicDisambiguatedTerm ftc op = disambiguatedTerm S.empty S.empty ftc op

-- Convierte a una aplicacion ambigua en una aplicación de tipos, o en una aplicación de lambda términos.
disambiguatedTerm :: TermContext -> BTypeContext -> FTypeContext -> TypeDefs
                  -> GenTree String -> Either SemanticException (Either DoubleType DoubleLTerm)
disambiguatedTerm tc btc ftc op t =
  case disambiguatedType btc ftc op t of
    Right ty -> return $ Left ty
    Left (TypeE _) -> return $ Right $ disambiguatedLTerm tc t
    Left (TypeVarE _) -> return $ Right $ disambiguatedLTerm tc t
    Left (OpE2 _) -> return $ Right $ disambiguatedLTerm tc t
    Left e -> throw e
    
-- Convierte la aplicación ambigua, en una aplicación de tipos.
-- Si no puede, falla.
disambiguatedType :: BTypeContext -> FTypeContext -> TypeDefs
                  -> GenTree String -> Either SemanticException DoubleType
disambiguatedType bs fs op (Node x []) =
  -- NO es necesario rs, ni el contexto de términos.
  transformTypeVar (\w _ _ -> w) S.empty bs S.empty fs op x 
disambiguatedType bs fs op (Node x xs) =
  transformType op x xs $ disambiguatedType bs fs op

-- Convierte una aplicacion en una aplicación de lambda términos, si es posible.
-- Se asume que los espacios de nombres entre las variables de tipo y términos
-- son disyuntos.
disambiguatedLTerm :: TermContext -> GenTree String -> DoubleLTerm
disambiguatedLTerm tc (Node x xs) =
  foldl (\r node ->
            let t = disambiguatedLTerm tc node
            in r :@: t
        ) var xs
  where var =  case getTermVar x tc S.empty of
                 Right (Just m) -> LVar (x, Bound m)
                 Right Nothing -> LVar (x, Free x)
                 Left _ -> error "error: disambiguatedLTerm, no debería pasar."
disambiguatedLTerm _ Nil = error "error: disambiguatedLTerm, no debería pasar."


transformType :: TypeDefs -> String -> [a]
              -> (a -> Either SemanticException DoubleType)
              -> Either SemanticException DoubleType
transformType op s ts f =
  do a <- maybeToEither (OpE2 s) $ getNumArgs s op
     if a == length ts
       then do tt <- sequence $ map f ts
               return $ RenamedType s tt
       else throw $ OpE1 s

transformTypeVar :: (TypeVar -> BTypeContext -> Int -> TypeVar)
                 -> BTypeContext -> BTypeContext
                 -> TermContext -> FTypeContext -> TypeDefs
                 -> String -> Either SemanticException DoubleType
transformTypeVar fvar rs bs tc fs op x =
  do v <- getTypeVar x bs tc
     case v of
       Just n -> return $ TVar (fvar x rs n, Bound n)
       Nothing -> case getNumArgs x op of
                    Just a -> if a == 0
                              then return $ RenamedType x []
                              else throw $ OpE1 x
                    Nothing -> if elem x fs
                               then return $ TVar (x, Free x)
                               else throw $ TypeE x

getTypeVar :: String -> BTypeContext -> TermContext
           -> Either SemanticException (Maybe Int)
getTypeVar = getTypeVar' 0

getTypeVar' :: Int -> String -> BTypeContext -> TermContext
            -> Either SemanticException (Maybe Int)
getTypeVar' i s tyc tec
  | S.null tyc =
    do when (isJust $ S.findIndexL (\w -> fst4 w == s) tec) (throw $ TypeVarE s)
       return Nothing
  | S.null tec =
    case S.findIndexL (\w -> fst w == s) tyc of
      Just x -> return $ return $ i + x
      Nothing -> return Nothing
  | otherwise =
      let x = S.index tyc 0
          y = S.index tec 0
      in if fromType x
         then if (fst x == s)
              then return $ return i
              else getTypeVar' (i+1) s (S.drop 1 tyc) tec
         else if snd x > snd4 y
         then if (fst x == s)
              then return $ return i
              else do when (fst4 y == s) (throw $ TypeVarE s)
                      getTypeVar' (i+1) s  (S.drop 1 tyc) (S.drop 1 tec)
         else do when (fst4 y == s) (throw $ TypeVarE s)
                 if (fst x == s)
                   then return $ return i
                   else getTypeVar' (i+1) s  (S.drop 1 tyc) (S.drop 1 tec)


getTermVar :: String -> TermContext -> BTypeContext -> Either SemanticException (Maybe Int)
getTermVar = getTermVar' 0

getTermVar' :: Int -> String -> TermContext -> BTypeContext -> Either SemanticException (Maybe Int)
getTermVar' i s tec tyc
  | S.null tec =
      do when (isJust $ S.findIndexL (\w -> fst w == s) tyc) (throw $ TermVarE s) 
         return Nothing
  | S.null tyc =
      case S.findIndexL (\w -> fst4 w == s) tec of
        Just x -> return $ return $ i + x
        Nothing -> return Nothing
  | otherwise =
      let x = S.index tyc 0
          y = S.index tec 0
      in if snd x > snd4 y
         then do when (fst x == s) (throw $ TermVarE s)
                 if (fst4 y == s)
                   then return $ return i
                   else getTermVar' (i+1) s (S.drop 1 tec) (S.drop 1 tyc)
         else if (fst4 y == s)
              then return $ return i
              else do when (fst x == s) (throw $ TermVarE s)
                      getTermVar' (i+1) s (S.drop 1 tec) (S.drop 1 tyc)
  
typeVar :: TypeVar -> Int -> BTypeVar
typeVar x i = (x, i)

-- Genera una variable de tipo para un contexto donde
-- se analiza un tipo.
typeVar0 :: TypeVar -> BTypeVar
typeVar0 x = typeVar x (-1)

-- Indica si la variable de tipo corresponde a un "tipo".
-- Es decir que, no corresponde a un lambda término "\x.".
fromType :: BTypeVar -> Bool
fromType (_, -1) = True
fromType _ = False

termVar :: TermVar -> Int -> TermVarWithType
termVar x i = (x, i, 0, Nothing)

-- Genera una variable de término, donde solo nos
-- interesa su nombre.
termVar0 :: TermVar -> TermVarWithType
termVar0 x = termVar x 0


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
negativeShift' _ _ (TVar (t, t'@(Free _))) = return $ TVar (t,t')
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

snd4 :: (a,b,c,d) -> b
snd4 (_,y,_,_) = y
