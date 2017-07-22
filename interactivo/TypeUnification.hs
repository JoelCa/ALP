module TypeUnification where

import Common
import Transformers (positiveShift, negativeShift)
import qualified Data.Map.Strict as M (Map, lookup, insert, empty, size)
import TypeInference (basicEqualTypes)

-- Algoritmo de unificación para el comando APPLY.
unification :: Bool -> Int -> DoubleType -> DoubleType
            -> Either ProofExceptions (M.Map Int DoubleType)
unification True _ = \_ _ -> return M.empty
unification False n = unif 0 n M.empty

-- Se obtiene el conjunto de sustituciones que hacen que los tipos unifiquen.
-- Argumentos:
-- 1. Cantidad de "para todos" analizados.
-- 2. Cantidad de instancias a generar.
-- 3. Sustituciones encontradas. La clave indica la posición de la sustitucición (el valor), desde la izquierda.
-- Osea, si c1 < c2 => [t1/v1]..[t2/v2] (donde v1 y v2, son las variables con nombres de las variables sin nombres).
-- 4. El tipo al que se le halla la unificación (sin los "para todos" externos).
-- 5. El tipo con el debe unificar el tipo dado en el 4º arg.
unif :: Int -> Int -> M.Map Int DoubleType -> DoubleType -> DoubleType ->
  Either ProofExceptions (M.Map Int DoubleType)
unif pos n sust t@(TVar (_, Bound i)) tt
  | (pos <= i) && (i < n) =
    let k = n - 1 - i
    in case M.lookup k sust of
         Nothing -> maybe (throw Unif1)
                    (\s -> return $ M.insert k s sust)
                    (negativeShift pos tt)
         Just s -> if basicEqualTypes (positiveShift pos s) tt
                   then return sust
                   else throw Unif1
  | i < pos = if basicEqualTypes t tt
              then return sust
              else throw Unif2
  | otherwise = maybe (throw Unif1)
                (\t' -> if basicEqualTypes t' tt
                        then return sust
                        else throw Unif2)
                (negativeShift n t)  -- Probar este caso
unif _ _ sust (TVar (_,Free x)) (TVar (_, Free y))
  | x == y = return sust
  | otherwise = throw Unif3
unif pos n sust (Fun t1 t2) (Fun tt1 tt2) =
  do res <- unif pos n sust t1 tt1
     unif pos n res t2 tt2
unif pos n sust (ForAll _ t) (ForAll _ tt) =
  unif (pos+1) (n+1) sust t tt
unif pos n sust (Exists _ t) (Exists _ tt) =
  unif (pos+1) (n+1) sust t tt
unif pos n sust (RenamedType x ts) (RenamedType y tts)
  | x == y = unifRename pos n sust ts tts
  | otherwise = throw Unif4
  where unifRename pos n sust [] [] = return sust
        unifRename pos n sust (t:ts) (tt:tts) =
          do res <- unif pos n sust t tt
             unifRename pos n res ts tts 
unif _ _ _ _ _ = throw Unif4
