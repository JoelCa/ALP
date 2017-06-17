module TypeSubstitution where

import Common
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
-- 4. Tipo (con nombres y sin nombres), sobre el que se realiza la sust.
-- 5. Tipos T1,..,Tn.
typeSubs :: Int -> BTypeContext -> FTypeContext -> FOperations -> (Type, TType)
         -> [(Type, TType)] -> (Type, TType)
typeSubs l bs fs op t xs = typeSubs' 0 l fs bs bs op t xs

-- Realiza la sust. de tipos.
-- 1. Profundidad ("para todos"), procesados.
-- 2. Cantidad de tipos a reemplazar (podemos pensarlo como el número de corrimientos).
-- 3. Contexto de variables de tipo libres.
-- 4. Contexto de variables de tipo ligadas (con nombres) procesadas.
-- 5. Contexto de los renombres de las variables de tipo ligadas (con nombres) del 4º arg.
--    Incluye además las var. de tipo ligadas del contexto.
-- 6. Tipo sobre el que se hace la sust. Sin los "para todos" que se van a sustituir.
-- 7. Tipos que se sustituyen.
typeSubs' :: Int -> Int -> FTypeContext -> BTypeContext -> BTypeContext -> FOperations
          -> (Type, TType) -> [(Type, TType)] -> (Type, TType)
typeSubs' n l fs bs rs op (B v, TBound x) ts
  | x < n = case S.findIndexL (\(_,x) -> x == v) bs of
              Just i -> (B $ snd $ S.index rs i, TBound x)
              Nothing -> error "error: typeSubs', no debería pasar."
  | (n <= x) && (x < l) =
      let (ty,ty') = ts !! (l - x - 1)
      in (renamedTypeWithName rs fs op ty, positiveShift n ty')
  | otherwise = (B v, TBound $ x - l + n)
typeSubs' _ _ _ _ _ _ x@(_, TFree f) _ = x
typeSubs' n l fs bs rs op (ForAll v t1, TForAll t1') ts =
  let v' = getRename v (snd, rs) (id, fs) (fst4, op) 
      (tt, tt') = typeSubs' (n+1) (l+1) fs (bTypeVar v S.<| bs) (bTypeVar v' S.<| rs) op (t1,t1') ts
  in (ForAll v' tt, TForAll tt')
typeSubs' n l fs bs rs op (Exists v t1, TExists t1') ts =
  let v' = getRename v (snd, rs) (id, fs) (fst4, op) 
      (tt, tt') = typeSubs' (n+1) (l+1) fs (bTypeVar v S.<| bs) (bTypeVar v' S.<| rs) op (t1,t1') ts
  in (Exists v' tt, TExists tt')
typeSubs' n l fs bs rs op (Fun t1 t2, TFun t1' t2') ts =
  let (tt1, tt1') = typeSubs' n l fs bs rs op (t1,t1') ts
      (tt2, tt2') = typeSubs' n l fs bs rs op (t2,t2') ts
  in (Fun tt1 tt2, TFun tt1' tt2')
typeSubs' n l fs bs rs op (RenameTy s args xs, RenameTTy m xs') ts =
  let (r, r') = unzip $ map (\x -> typeSubs' n l fs bs rs op x ts) $ zip xs xs'
  in (RenameTy s args r, RenameTTy m r')


-- Realiza la sust. de tipos. sin nombre.
ttypeSubs :: Int -> TType -> [TType] -> TType
ttypeSubs _ t [] = t
ttypeSubs l t xs = ttypeSubs' 0 l t xs

-- Realiza la sust. de tipos sin nombre.
-- 1. Profundidad ("para todos"), procesados.
-- 2. Cantidad de tipos a reemplazar (podemos pensarlo como el número de corrimientos).
-- 3. Tipo sin nombre, sobre el que se hace la sust. Sin los "para todos" que se van a sustituir.
-- 4. Tipos sin nombre que se sustituyen.
ttypeSubs' :: Int -> Int -> TType -> [TType] -> TType
ttypeSubs' n l (TBound x) ts
  | x < n = TBound x
  | (n <= x) && (x < l) =
      positiveShift n $ ts !! (l - x - 1)
  | otherwise = TBound $ x - l + n
ttypeSubs' _ _ t@(TFree f) _ = t
ttypeSubs' n l (TForAll t1) ts =
  TForAll $ ttypeSubs' (n+1) (l+1) t1 ts
ttypeSubs' n l (TExists t1) ts =
  TExists $ ttypeSubs' (n+1) (l+1) t1 ts
ttypeSubs' n l (TFun t1 t2) ts =
  TFun (ttypeSubs' n l t1 ts) (ttypeSubs' n l t2 ts)
ttypeSubs' n l (RenameTTy op xs) ts =
  RenameTTy op $ map (\x -> ttypeSubs' n l x ts) xs

-- Consideramos que el 1º argumento corresponde al cuerpo de una cuantificación ("para todo", "existe").
-- Se reemplaza la variable ligada más "externa" por el 2º argumento.
-- Además, se corrigen las varibles ligadas escapadas sin nombre. No se renombran las variables ligadas
-- con nombre.
basicTypeSubs :: (Type, TType) -> (Type, TType) -> (Type, TType)
basicTypeSubs = basicTypeSubs' 0

basicTypeSubs' :: Int -> (Type, TType) -> (Type, TType) -> (Type, TType)
basicTypeSubs' n x@(tt, TBound m) (t, t')
  | n == m = (t, positiveShift n t')
  | m > n = (tt, TBound (m-1))
  | otherwise = x
basicTypeSubs' n x@(tt, TFree f) _ = x
basicTypeSubs' n (ForAll v t1, TForAll t1') t =
  let (tt, tt') = basicTypeSubs' (n+1) (t1,t1') t
  in (ForAll v tt, TForAll tt')
basicTypeSubs' n (Exists v t1, TExists t1') t =
  let (tt, tt') = basicTypeSubs' (n+1) (t1,t1') t
  in (Exists v tt, TExists tt')
basicTypeSubs' n (Fun t1 t2, TFun t1' t2') t =
  let (tt1, tt1') = basicTypeSubs' n (t1,t1') t
      (tt2, tt2') = basicTypeSubs' n (t2,t2') t
  in (Fun tt1 tt2, TFun tt1' tt2')
basicTypeSubs' n (RenameTy s args ts, RenameTTy op ts') t =
  let (xs, ys) = unzip $ map (\x -> basicTypeSubs' n x t) $ zip ts ts'
  in (RenameTy s args xs, RenameTTy op ys)
