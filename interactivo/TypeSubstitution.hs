module TypeSubstitution where

import Common
import Theorems (Theorems, theoremsNames)
import qualified Data.Sequence as S
import Transformers
import RenamedVariables


-- Realiza la sustitución de tipos: (((t [T1]) [T2])..) [Tn].
-- Para ello, hace dos cosas:
-- 1. Renombra todas las variables de tipo ligadas "escapadas" (sin nombres),
-- nos referimos a aquellas variables cuyo cuantificador no figura en el tipo
-- (sin nombre) del 3º arg.
-- 2. Renombra las variables de tipo ligadas (con nombres) del 3º arg., de modo tal que no halla
-- dos var. de tipo ligadas con el mismo nombre, una más anidada que la otra.
-- Argumentos:
-- 1. Cantidad de sustituciones a realizar.
-- 2. Conjunto de variables de tipo de libres.
-- 3. Conjunto de variables de tipo ligadas (con nombres), del contexto.
-- 4. Operaciones foldeables.
-- 5. Teoremas.
-- 6. Tipo (con nombres y sin nombres), sobre el que se realiza la sust.
-- 7. Tipos T1,..,Tn.
typeSubs :: Int -> BTypeContext -> FTypeContext -> FOperations -> Theorems
         -> DoubleType -> [DoubleType] -> DoubleType
typeSubs l bs fs op te = typeSubs' 0 l fs bs bs op (theoremsNames te)

-- Realiza la sust. de tipos.
-- 1. Profundidad ("para todos"), procesados.
-- 2. Cantidad de tipos a reemplazar (podemos pensarlo como el número de corrimientos).
-- 3. Contexto de variables de tipo libres.
-- 4. Contexto de variables de tipo ligadas (con nombres) procesadas.
-- 5. Contexto de los renombres de las variables de tipo ligadas (con nombres) del 4º arg.
--    Incluye además las var. de tipo ligadas del contexto.
-- 6. Operaciones foldeables.
-- 7. Nombres de los teoremas.
-- 8. Tipo sobre el que se hace la sust. Sin los "para todos" que se van a sustituir.
-- 9. Tipos que se sustituyen.
typeSubs' :: Int -> Int -> FTypeContext -> BTypeContext -> BTypeContext -> FOperations
          -> [String] -> DoubleType -> [DoubleType] -> DoubleType
typeSubs' n l fs bs rs op tn (TVar (v, Bound x)) ts
  | x < n = case S.findIndexL (\(_,x) -> x == v) bs of
              Just i -> TVar (snd $ S.index rs i, Bound x)
              Nothing -> error "error: typeSubs', no debería pasar."
  | (n <= x) && (x < l) =
      let ty = ts !! (l - x - 1)
      in renamedValidType2 n rs fs op tn ty
  | otherwise = TVar (v, Bound $ x - l + n)
typeSubs' _ _ _ _ _ _ _ x@(TVar (_, Free _)) _ = x
typeSubs' n l fs bs rs op tn (ForAll v t1) ts =
  let v' = getRename v (snd, rs) (id, fs) (fst4, op) (id, tn)
      tt = typeSubs' (n+1) (l+1) fs (bTypeVar v S.<| bs) (bTypeVar v' S.<| rs) op tn t1 ts
  in ForAll v' tt
typeSubs' n l fs bs rs op tn (Exists v t1) ts =
  let v' = getRename v (snd, rs) (id, fs) (fst4, op) (id, tn) 
      tt = typeSubs' (n+1) (l+1) fs (bTypeVar v S.<| bs) (bTypeVar v' S.<| rs) op tn t1 ts
  in Exists v' tt
typeSubs' n l fs bs rs op tn (Fun t1 t2) ts =
  let tt1 = typeSubs' n l fs bs rs op tn t1 ts
      tt2 = typeSubs' n l fs bs rs op tn t2 ts
  in Fun tt1 tt2
typeSubs' n l fs bs rs op tn (RenamedType s xs) ts =
  let r = map (\x -> typeSubs' n l fs bs rs op tn x ts) xs
  in RenamedType s r


-- Realiza la sust. de tipos. sin nombre.
-- ttypeSubs :: Int -> TType -> [TType] -> TType
-- ttypeSubs _ t [] = t
-- ttypeSubs l t xs = ttypeSubs' 0 l t xs

-- -- Realiza la sust. de tipos sin nombre.
-- -- 1. Profundidad ("para todos"), procesados.
-- -- 2. Cantidad de tipos a reemplazar (podemos pensarlo como el número de corrimientos).
-- -- 3. Tipo sin nombre, sobre el que se hace la sust. Sin los "para todos" que se van a sustituir.
-- -- 4. Tipos sin nombre que se sustituyen.
-- ttypeSubs' :: Int -> Int -> TType -> [TType] -> TType
-- ttypeSubs' n l (TBound x) ts
--   | x < n = TBound x
--   | (n <= x) && (x < l) =
--       positiveShift n $ ts !! (l - x - 1)
--   | otherwise = TBound $ x - l + n
-- ttypeSubs' _ _ t@(TFree f) _ = t
-- ttypeSubs' n l (TForAll t1) ts =
--   TForAll $ ttypeSubs' (n+1) (l+1) t1 ts
-- ttypeSubs' n l (TExists t1) ts =
--   TExists $ ttypeSubs' (n+1) (l+1) t1 ts
-- ttypeSubs' n l (TFun t1 t2) ts =
--   TFun (ttypeSubs' n l t1 ts) (ttypeSubs' n l t2 ts)
-- ttypeSubs' n l (RenamedType op xs) ts =
--   RenamedType op $ map (\x -> ttypeSubs' n l x ts) xs

-- Consideramos que el 1º argumento corresponde al cuerpo de una cuantificación ("para todo", "existe").
-- Se reemplaza la variable ligada más "externa" por el 2º argumento.
-- Además, se corrigen las varibles ligadas escapadas sin nombre. No se renombran las variables ligadas
-- con nombre.
basicTypeSubs :: DoubleType -> DoubleType -> DoubleType
basicTypeSubs = basicTypeSubs' 0

basicTypeSubs' :: Int -> DoubleType -> DoubleType -> DoubleType
basicTypeSubs' n x@(TVar (tt, Bound m)) t
  | n == m = positiveShift n t
  | m > n = TVar (tt, Bound (m-1))
  | otherwise = x
basicTypeSubs' n x@(TVar (_, Free _)) _ = x
basicTypeSubs' n (ForAll v t1) t =
  let tt = basicTypeSubs' (n+1) t1 t
  in ForAll v tt
basicTypeSubs' n (Exists v t1) t =
  let tt = basicTypeSubs' (n+1) t1 t
  in Exists v tt
basicTypeSubs' n (Fun t1 t2) t =
  let tt1 = basicTypeSubs' n t1 t
      tt2 = basicTypeSubs' n t2 t
  in Fun tt1 tt2
basicTypeSubs' n (RenamedType s ts) t =
  let xs = map (\x -> basicTypeSubs' n x t) ts
  in RenamedType s xs
