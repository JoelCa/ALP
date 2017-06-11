module Transformers where

import Common
import Data.List (findIndex, elemIndex, find)
import RenamedVariables
import Hypothesis
import Parser (getHypothesisValue)
import Data.IntSet (IntSet)
import qualified Data.Sequence as S

-- Retorna el tipo con nombre, posiblemente renombrado, de su 3º arg.
-- A fin de respetar la Convención 1.
-- Además, genera el tipo sin nombre.
-- Argumentos:
-- 1. Varibles de tipo libres.
-- 2. Operaciones "foldeables".
-- 3. Tipo a procesar.
-- OBS: Utilizamos esta función sobre tipos que NO requieren del contexto de tipos "ligados".
renamedType :: FTypeContext -> FOperations -> Type -> Either ProofExceptions (Type, TType)
renamedType ftc op = typeWithoutName S.empty S.empty ftc (map (\(x,_,_,_) -> x) op)  op

-- Retorna el tipo con nombre (renombrado), y sin nombre, del tipo dado
-- por el 4º argumento.
-- El renombramiento se realiza de modo tal que se respete la Convención 1.
-- OBS: Utilizamos esta función sobre tipos que requieren del contexto de tipos "ligados".
renamedType2 :: BTypeContext -> FTypeContext ->  FOperations
             -> Type -> Either ProofExceptions (Type, TType)
renamedType2 bs ftc op = let bs' = foldr (\(_,x) xs -> x : xs) [] bs
                             op' = foldr (\(x,_,_,_) xs -> x : xs) [] op
                         in typeWithoutName bs' bs' ftc (op' ++ ftc) op

-- Retorna el tipo con nombre (renombrado), y sin nombre, del tipo dado
-- por el 4º argumento.
-- El renombramiento se realiza de modo tal que se respete la Convención 1.
-- OBS: Solo la utilizamos en el renombramiento del cuerpo de una operación.
renamedType3 :: [String] -> FTypeContext ->  FOperations
             -> Type -> Either ProofExceptions (Type, TType)
renamedType3 bs ftc op = let op' = foldr (\(x,_,_,_) xs -> x : xs) [] op
                         in typeWithoutName bs bs ftc (op' ++ ftc) op


typeWithoutName :: S.Seq String -> S.Seq String -> S.Seq String -> S.Seq String
                -> FOperations -> Type -> Either ProofExceptions (Type, TType)
typeWithoutName rs bs fs _ op (B x) =
  getVarType (\_ zs m -> S.index zs m) rs bs fs op x
typeWithoutName rs bs fs on op (ForAll x t) =
  do let v = getRename x [fs, rs, on]
     (tt,tt') <- typeWithoutName (v S.<| rs) (x S.<| bs) on fs op t
     return (ForAll v tt, TForAll tt')
typeWithoutName rs bs fs on op (Exists x t) =
  do let v = getRename x [fs, rs, on]
     (tt,tt') <- typeWithoutName (v S.<| rs) (x S.<| bs) on fs op t
     return (Exists v tt, TExists tt')
typeWithoutName rs bs fs ofs on (Fun t1 t2) =
  do (tt1, tt1') <- typeWithoutName rs bs fs on op t1
     (tt2, tt2') <- typeWithoutName rs bs fs on op t2
     return (Fun tt1 tt2, TFun tt1' tt2')
typeWithoutName rs bs fs on op (RenameTy s args ts) =
  getOpType op s args ts $ typeWithoutName rs bs fs on op

----------------------------------------------------------------------------------------------------------------------
-- Trasformadores de lambda términos: Se pasa de un lambda término con nombre, al equivalente sin nombre.

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
withoutName :: FOperations -> FTypeContext -> BTypeContext -> (IntSet, Int)
            -> LamTerm -> Either ProofExceptions (LamTerm, Term)
withoutName op fs bs = let bs' = foldr (\(_,x) xs -> x : xs) [] bs
                           op' = foldr (\(x,_,_,_) xs -> x : xs) [] op
                       in withoutName' [] [] bs' bs' fs (op' ++ fs) op

withoutName' :: [String] -> [String] -> [String] -> [String] -> FTypeContext -> [String] -> FOperations -> (IntSet, Int)
             -> LamTerm -> Either ProofExceptions (LamTerm, Term)
withoutName' ters tebs _ _ _ _ _ cnn w@(LVar x) =
  case elemIndex x tebs of
    Just m -> return (LVar $ ters !! m, Bound m)
    Nothing -> return (w, getTermVar x cnn)
withoutName' ters tebs tyrs tybs fs ofs op cnn (Abs x t e) =
  do let h = getRename x [] ters
     t' <- typeWithoutName tyrs tybs fs ofs op t
     (ee, ee') <- withoutName' (h:ters)(x:tebs) tyrs tybs fs ofs op cnn e
     return (Abs h (fst t') ee, Lam t' ee')
withoutName' ters tebs tyrs tybs fs ofs op cnn (App e1 e2) =
  do (ee1, ee1') <- withoutName' ters tebs tyrs tybs fs ofs op cnn e1
     (ee2, ee2') <- withoutName' ters tebs tyrs tybs fs ofs op cnn e2
     return (App ee1 ee2, ee1' :@: ee2')
withoutName' ters tebs tyrs tybs fs ofs op cnn (BAbs x e) =
  do let v = getRename x ofs tyrs
     (ee, ee') <- withoutName' ters tebs (v:tyrs) (x:tybs) fs ofs op cnn e
     return (BAbs v ee, BLam v ee')
withoutName' ters tebs tyrs tybs fs ofs op cnn (BApp e t) =
  do (ee, ee') <- withoutName' ters tebs tyrs tybs fs ofs op cnn e
     t' <- typeWithoutName tyrs tybs fs ofs op t
     return (BApp ee (fst t'), ee' :!: t')
withoutName' ters tebs tyrs tybs fs ofs op cnn (EPack t e t') =
  do tt <- typeWithoutName tyrs tybs fs ofs op t
     (ee, ee') <- withoutName' ters tebs tyrs tybs fs ofs op cnn e
     tt' <- typeWithoutName tyrs tybs fs ofs op t'
     return (EPack (fst tt) ee (fst tt'), Pack tt ee' tt')
withoutName' ters tebs tyrs tybs fs ofs op cnn (EUnpack x y e1 e2) =
  do (ee1, ee1') <- withoutName' ters tebs tyrs tybs fs ofs op cnn e1
     let v = getRename x ofs tyrs
         h = getRename y [] ters
     (ee2, ee2') <- withoutName' (h:ters) (y:tebs) (v:tyrs) (x:tybs) fs ofs op cnn e2
     return (EUnpack v h ee1 ee2, Unpack v ee1' ee2')
withoutName' ters tebs tyrs tybs fs ofs op cnn (As e t) =
  do (ee, ee') <- withoutName' ters tebs tyrs tybs fs ofs op cnn e
     t' <- typeWithoutName tyrs tybs fs ofs op t
     return (As ee (fst t'), ee' ::: t')

----------------------------------------------------------------------------------------------------------------------
-- Transformadores para aplicaciones ambiguas.

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
disambiguatedType bs = disambiguatedType' (foldr (\(_,x) xs -> x : xs) [] bs)


disambiguatedType' :: [String] -> [String] -> FOperations
                   -> GenTree String -> Either ProofExceptions (Type, TType)
disambiguatedType' bs fs op (Node x []) =
  getVarType (\w _ _ -> w) [] bs fs op x
disambiguatedType' bs fs op (Node x xs) =
  getOpType op x (length xs) xs $ disambiguatedType' bs fs op


getVarType :: (String -> S.Seq String -> Int -> String) -> S.Seq String -> S.Seq String -> S.Seq String
           -> FOperations -> String -> Either ProofExceptions (Type, TType)
getVarType f rs bs fs op x =
  case S.elemIndexL x bs of
    Just n -> return (B $ f x rs n, TBound n)
    Nothing -> case getElemIndex (\(w,_,_,_) -> w == x) op of
                 Just (n, (_, _, args, _)) -> if args == 0
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
      do (m, (_,_,args',_)) <- maybeToEither (OpE2 s) $ getElemIndex (\(x,_,_,_) -> x == s) op
         if args' == args
           then do rs <- sequence $ map f ts
                   let (tt, tt') = unzip rs
                   return (RenameTy s args tt, RenameTTy m tt')
           else throw $ OpE1 s

-- Convierte una aplicacion en una aplicación de lambda términos, si es posible.
disambiguatedLTerm :: (IntSet, Int) -> GenTree String -> (LamTerm, Term)
disambiguatedLTerm cnn@(cn,n) (Node x xs) =
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
                _ -> Free $ Global x       --Probable teorema
    Nothing -> Free $ Global x
