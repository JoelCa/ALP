module Transformers where

import Common
import Data.List (findIndex, elemIndex, find)
import RenamedVariables
import Hypothesis
import Parser (getHypothesisValue)

-- Retorna el tipo con nombre, posiblemente renombrado, de su 3º arg.
-- A fin de respetar la Convención 1.
-- Además, genera el tipo sin nombre.
-- Argumentos:
-- 1. Varibles de tipo libres.
-- 2. Operaciones "foldeables".
-- 3. Tipo a procesar.
-- OBS: Utilizamos esta función sobre tipos que NO requieren del contexto de tipos "ligados".
renamedType :: FTypeContext -> FOperations -> Type -> Either ProofExceptions (Type, TType)
renamedType = typeWithoutName [] []

-- Retorna el tipo con nombre (renombrado), y sin nombre, del tipo dado
-- por el 4º argumento.
-- El renombramiento se realiza de modo tal que se respete la Convención 1.
-- OBS: Utilizamos esta función sobre tipos que requieren del contexto de tipos "ligados".
renamedType2 :: BTypeContext -> FTypeContext ->  FOperations
             -> Type -> Either ProofExceptions (Type, TType)
renamedType2 bs = let bs' = foldr (\(_,x) xs -> x : xs) [] bs
                  in typeWithoutName bs' bs'

-- Retorna el tipo con nombre (renombrado), y sin nombre, del tipo dado
-- por el 4º argumento.
-- El renombramiento se realiza de modo tal que se respete la Convención 1.
-- OBS: Solo la utilizamos en el renombramiento del cuerpo de una operación.
renamedType3 :: [String] -> FTypeContext ->  FOperations
             -> Type -> Either ProofExceptions (Type, TType)
renamedType3 bs = typeWithoutName bs bs


typeWithoutName :: [String] -> [String] -> FTypeContext -> FOperations
                -> Type -> Either ProofExceptions (Type, TType)
typeWithoutName rs bs fs op (B x) =
  case x `elemIndex` bs of
    Just n -> return (B $ rs !! n, TBound n)
    Nothing -> case getElemIndex (\(w,_,_,_) -> w == x) op of
                 Just (n, (_, _, args, _)) -> if args == 0
                                              then return (RenameTy x 0 [], RenameTTy n [])
                                              else throw $ OpE1 x
                 Nothing -> if elem x fs
                            then return (B x, TFree x)
                            else throw $ TypeE x
typeWithoutName rs bs fs op (ForAll x t) =
  do let v = getRename x fs rs
     (tt,tt') <- typeWithoutName (v:rs) (x:bs) fs op t
     return (ForAll v tt, TForAll tt')
typeWithoutName rs bs fs op (Exists x t) =
  do let v = getRename x fs rs
     (tt,tt') <- typeWithoutName (v:rs) (x:bs) fs op t
     return (Exists v tt, TExists tt')
typeWithoutName rs bs fs op (Fun t1 t2) =
  do (tt1, tt1') <- typeWithoutName rs bs fs op t1
     (tt2, tt2') <- typeWithoutName rs bs fs op t2
     return (Fun tt1 tt2, TFun tt1' tt2')
typeWithoutName rs bs fs op (RenameTy s args ts) =
  case find (\(x,_,_) -> x == s) notFoldeableOps of
    Just (_,n,args') ->
      if args' == args
      then do rs <- sequence $ map (typeWithoutName rs bs fs op) ts
              let (tt, tt') = unzip rs
              return (RenameTy s args tt, RenameTTy n tt')
      else throw $ OpE1 s
    Nothing ->
      do (m, (_,_,args',_)) <- maybeToEither (OpE2 s) $ getElemIndex (\(x,_,_,_) -> x == s) op
         if args' == args
           then do rs <- sequence $ map (typeWithoutName rs bs fs op) ts
                   let (tt, tt') = unzip rs
                   return (RenameTy s args tt, RenameTTy m tt')
           else throw $ OpE1 s

----------------------------------------------------------------------------------------------------------------------
-- Trasformadores de lambda términos: Se pasa de un lambda término con nombre, al equivalente sin nombre.

-- Genera el lambda término con renombre de variables de tipo, y el lambda término sin nombre.
-- Chequea que las variables de tipo sean válidas de acuerdo a los contexto de tipos
-- dados por 2º y 3º arg. En caso de ser necesario renombra las variables de tipo "ligadas".
-- Además, chequea que las variables de términos también sean válidas, de
-- acuerdo la longitud del contexto de variables de términos "iniciales", dado por el 4º arg.
-- Se asume que el 4º argumento es mayor o igual a cero.
-- El 1º argumento, es la tabla de operaciones "foldeables".
-- Obs: es util generar el lambda término con nombres renombramos para imprimir mejor los errores.
-- Se usa en el algoritmo de inferencia, y el comando exact.
withoutName :: FOperations -> FTypeContext -> BTypeContext -> Int
            -> LamTerm -> Either ProofExceptions (LamTerm, Term)
withoutName op fs bs = let bs' = foldr (\(_,x) xs -> x : xs) [] bs
                       in withoutName' [] bs' bs' fs op

withoutName' :: [String] -> [String] -> [String] -> FTypeContext -> FOperations -> Int
             -> LamTerm -> Either ProofExceptions (LamTerm, Term)
withoutName' teb _ _ _ _ n w@(LVar x) =
  case elemIndex x teb of
    Just m -> return (w, Bound m)
    Nothing -> let r = case getHypothesisValue x of
                         Just h -> case getHypoPosition n h of
                                     Just i -> Bound i
                                     _ -> Free $ Global x
                         Nothing -> Free $ Global x
               in return (w, r)
withoutName' teb rs bs fs op n (Abs x t e) =
  do t' <- typeWithoutName rs bs fs op t
     (ee, ee') <- withoutName' (x:teb) rs bs fs op n e
     return (Abs x (fst t') ee, Lam t' ee')
withoutName' teb rs bs fs op n (App e1 e2) =
  do (ee1, ee1') <- withoutName' teb rs bs fs op n e1
     (ee2, ee2') <- withoutName' teb rs bs fs op n e2
     return (App ee1 ee2, ee1' :@: ee2')
withoutName' teb rs bs fs op n (BAbs x e) =
  do let v = getRename x fs rs
     (ee, ee') <- withoutName' teb (v:rs) (x:bs) fs op n e
     return (BAbs v ee, BLam v ee')
withoutName' teb rs bs fs op n (BApp e t) =
  do (ee, ee') <- withoutName' teb rs bs fs op n e
     t' <- typeWithoutName rs bs fs op t
     return (BApp ee (fst t'), ee' :!: t')
withoutName' teb rs bs fs op n (EPack t e t') =
  do tt <- typeWithoutName rs bs fs op t
     (ee, ee') <- withoutName' teb rs bs fs op n e
     tt' <- typeWithoutName rs bs fs op t'
     return (EPack (fst tt) ee (fst tt'), Pack tt ee' tt')
withoutName' teb rs bs fs op n (EUnpack x y e1 e2) =
  do (ee1, ee1') <- withoutName' teb rs bs fs op n e1
     let v = getRename x fs rs
     (ee2, ee2') <- withoutName' (y:teb) (v:rs) (x:bs) fs op n e2
     return (EUnpack v y ee1 ee2, Unpack v ee1' ee2')
withoutName' teb rs bs fs op n (As e t) =
  do (ee, ee') <- withoutName' teb rs bs fs op n e
     t' <- typeWithoutName rs bs fs op t
     return (As ee (fst t'), ee' ::: t')


-- TERMINAR
-- recognize :: BTypeContext -> FTypeContext -> FOperations -> Int
--           -> [String] -> Either ProofExceptions (Either (Type, TType) (LamTerm, Term))
-- recognize = undefined


-- recognizeType :: BTypeContext -> FTypeContext -> FOperations
--               -> [String] -> Maybe (Type, TType)
-- recognizeType bs fs op [v]
--   | elem v fs = return (B v, TFree v)
--   | otherwise = case getElemIndex (\(_,x) -> x == v) bs of
--                   Just (i, _) -> return (B $ bs ! i, TBound i)
--                   Nothing -> undefined

-- recognizeLam :: Int -> [String] -> Either ProofExceptions ((LamTerm, Term) -> (LamTerm, Term))
-- recognizeLam n [] = return id
-- recognizeLam n (x:xs) = do maybeToEither $ getTermVar x


-- Identifica una variable de término.
getTermVar :: Int -> String -> (LamTerm, Term)
getTermVar n x = case getHypothesisValue x of
                   Just h -> case getHypoPosition n h of
                               Just i -> (LVar x, Bound i)
                               _ -> (LVar x, Free $ Global x)
                   Nothing -> (LVar x, Free $ Global x)
