module Commands where

import Common
import Data.Char (isDigit)
import Data.List (findIndex, elemIndex, find)
import Control.Monad (unless, when)
import qualified Data.Map as M (Map, lookup, insert, empty, size)
import Data.Maybe (fromJust, isJust)
import qualified Data.Vector as V
import ProofState
import EmptyTerms
import RenamedVariables
import Hypothesis
import Transformers

-- Contruye la prueba.
habitar :: Tactic -> Proof ()
habitar Assumption =
  do x <- getType
     (_,tw) <- maybeToProof EmptyType x 
     c <- getTermContext
     q <- getTBTypeVars
     i <- maybeToProof AssuE $ V.findIndex (\(_,p,_,t) -> renameTType (q - p) t == tw) c
     endSubProof
     modifyTerm $ simplify $ Bound i
habitar Intro =
  do x <- getType
     introComm x
habitar Intros =
  introsComm
habitar (Apply h) =
  do x <- getType
     (t,t') <- maybeToProof EmptyType x
     n <- getTTermVars
     cn <- getConflictNames
     i <- maybeToProof (HypoE h) $ getHypoPosition cn n h
     c <- getTermContext
     q <- getTBTypeVars
     applyComm i (t,t') (getTypeVar q $ c V.! i)
habitar (Elim h) =
  do x <- getType
     (t,t') <- maybeToProof EmptyType x
     n <- getTTermVars
     cn <- getConflictNames
     i <- maybeToProof (HypoE h) $ getHypoPosition cn n h
     c <- getTermContext
     q <- getTBTypeVars
     elimComm i (t,t') (getTypeVar q $ c V.! i)
habitar CLeft =
  do x <- getType
     case x of
       Just (RenameTy _ 2 [t1,t2] , RenameTTy n [t1',t2']) ->
         if n == or_code
         then do replaceType (t1,t1')
                 modifyTerm $ addHT (\x -> ((Free $ Global "intro_or1")
                                             :!: (t1,t1') :!: (t2,t2'))
                                           :@: x)
         else throw CommandInvalid
       _ -> throw CommandInvalid
habitar CRight =
  do x <- getType
     case x of
       Just (RenameTy _ 2 [t1,t2] , RenameTTy n [t1',t2']) ->
         if n == or_code
         then do replaceType (t2,t2')
                 modifyTerm $ addHT (\x -> ((Free $ Global "intro_or2")
                                             :!: (t1,t1') :!: (t2,t2'))
                                           :@: x)
         else throw CommandInvalid
       _ -> throw CommandInvalid
habitar Split =
  do x <- getType
     case x of
       Just (RenameTy _ 2 [t1,t2], RenameTTy n [t1',t2']) ->
         if n == and_code
         then do newSubProofs 2 [Just (t1,t1'), Just (t2,t2')]
                 modifyTerm $ addDHT (\x y -> ((Free $ Global "intro_and")
                                                :!: (t1,t1') :!: (t2,t2'))
                                              :@: x :@: y)
         else throw CommandInvalid
       _ -> throw CommandInvalid
habitar (Exact (LamT te)) =
  do op <- getUsrOpers
     n <- getTTermVars
     cn <- getConflictNames
     btc <- getBTypeContext
     ftc <- getFTypeContext
     te' <- eitherToProof $ withoutName op ftc btc (cn,n) te
     exactTerm te'  
habitar (Exact (T ty)) =
  do x <- getType
     when (isJust x) $ throw $ ExactE2 $ fst $ fromJust x
     op <- getUsrOpers
     btc <- getBTypeContext
     ftc <- getFTypeContext
     ty' <- eitherToProof $ renamedType2 btc ftc op ty
     exactType ty'     
habitar (Exact (Appl aps)) =
  do op <- getUsrOpers
     btc <- getBTypeContext
     ftc <- getFTypeContext
     n <- getTTermVars
     cn <- getConflictNames
     t <- eitherToProof $ disambiguatedTerm btc ftc op (cn,n) aps
     case t of
       Right te -> exactTerm te
       Left ty -> exactType ty
habitar (Unfold s Nothing) =
  do x <- getType
     (t,t') <- maybeToProof EmptyType x
     op <- getUsrOpers
     (m, (_, (tt,tt'), _, _)) <- maybeToProof (UnfoldE1 s) $ getElemIndex (\(x,_,_,_) -> x == s) op
     btc <- getBTypeContext
     ftc <- getFTypeContext
     replaceType $ unfoldComm btc ftc m (t,t') (tt,tt')
habitar (Unfold s (Just h)) =
  do op <- getUsrOpers
     (m, (_, (tt,tt'), _, _)) <- maybeToProof (UnfoldE1 s) $ getElemIndex (\(x,_,_,_) -> x == s) op
     n <- getTTermVars
     cn <- getConflictNames
     i <- maybeToProof (HypoE h) $ getHypoPosition cn n h
     c <- getTermContext
     let (x,y,t,t') = c V.! i
     btc <- getBTypeContext
     ftc <- getFTypeContext
     let (r,r') = unfoldComm btc ftc m (t,t') (tt,tt')
     updateTermContext i (x,y,r,r')
habitar (Absurd ty) =
  do x <- getType
     case x of
       Just (RenameTy _ 0 [] , RenameTTy n []) ->
         if n == bottom_code
         then do op <- getUsrOpers
                 btc <- getBTypeContext
                 ftc <- getFTypeContext
                 (tty, tty') <- eitherToProof $ renamedType2 btc ftc op ty
                 newSubProofs 2 [ Just (tty, tty')
                                , Just (RenameTy not_text 1 [tty], RenameTTy not_code [tty']) ]
                 modifyTerm $ addDHT (\x y -> ((Free $ Global "intro_bottom")
                                                :!: (tty, tty'))
                                              :@: x :@: y)
         else throw CommandInvalid
       _ -> throw CommandInvalid
habitar (CExists ty) =
  do x <- getType
     case x of
       Just tt@(Exists v t, TExists t') ->
         do op <- getUsrOpers
            btc <- getBTypeContext
            ftc <- getFTypeContext
            ty' <- eitherToProof $ renamedType2 btc ftc op ty
            replaceType $ applyTypes 1 ftc (foldr (\(_,x) xs -> x : xs) [] btc) (t,t') [ty']
            modifyTerm $ addHT (\x -> Pack ty' x tt)
       _ -> throw CommandInvalid
habitar (Cut ty) =
  do x <- getType
     (t,t') <- maybeToProof EmptyType x
     op <- getUsrOpers
     btc <- getBTypeContext
     ftc <- getFTypeContext
     (tty, tty') <- eitherToProof $ renamedType2 btc ftc op ty
     newSubProofs 2 [ Just (Fun tty t, TFun tty' t')
                    , Just (tty, tty') ]
     modifyTerm $ addDHT (\x y -> x :@: y)

----------------------------------------------------------------------------------------------------------------------
-- Comando INTRO e INTROS

introComm :: Maybe (Type, TType) -> Proof ()
introComm (Just (Fun t1 t2, TFun t1' t2')) =
  do modifyTVars (+1)
     q <- getTBTypeVars
     tv <- getTVars
     addTermContext (tv, q, t1, t1')
     replaceType (t2, t2')
     modifyTerm $ addHT (\x -> Lam (t1,t1') x)
introComm (Just (ForAll v t, TForAll t')) =
  do modifyTVars (+1)
     tv <- getTVars
     addBTypeContext (tv, v)
     replaceType (t, t')
     modifyTerm $ addHT (\x -> BLam v x)
introComm Nothing = throw EmptyType
introComm _ = throw IntroE1

-- Implementamos el comando INTROS, como una secuencia de comandos INTRO.
-- Cuando falla el último INTRO, se recupera el estado previo al error mediante catch.
introsComm :: Proof ()
introsComm = catch (do habitar Intro
                       introsComm)
             ((\e -> return ()) :: ProofExceptions -> Proof ())

----------------------------------------------------------------------------------------------------------------------
-- Comando ELIM

-- Asumimos que las tuplas del 2º arg. , tienen la forma correcta.
elimComm :: Int -> (Type, TType) -> (Type, TType) -> Proof ()
elimComm i (t,t') (Exists v tt, TExists tt') =
  do modifyTVars (+1)
     tv <- getTVars
     addBTypeContext (tv, v)
     modifyTVars (+1)
     q <- getTBTypeVars
     tv <- getTVars
     addTermContext (tv, q, tt, tt')
     btc <- getBTypeContext
     ftc <- getFTypeContext
     replaceType (renameType ftc (v:foldr (\(_,x) xs -> x : xs) [] btc) t, renameTType 1 t')
     modifyTerm $ addHT (\x -> Unpack v (Bound i) x)
elimComm i (t,t') (RenameTy _ _ [t1,t2], RenameTTy n [t1',t2'])
  | n == and_code =
      do replaceType (Fun t1 (Fun t2 t), TFun t1' (TFun t2' t'))
         modifyTerm $ addHT (\x -> ((Free $ Global "elim_and")
                                     :!: (t1,t1') :!: (t2,t2') :!: (t,t'))
                                   :@: (Bound i) :@: x)
  | n == or_code =
      do newSubProofs 2 [ Just (Fun t1 t, TFun t1' t')
                        , Just (Fun t2 t, TFun t2' t') ]
         modifyTerm $ addDHT (\x y -> ((Free $ Global "elim_or")
                                        :!: (t1,t1') :!: (t2,t2') :!: (t,t'))
                                      :@: (Bound i) :@: x :@: y)
  | otherwise =
      throw ElimE1
elimComm i t (RenameTy _ _ [], RenameTTy n [])
  | n == bottom_code =
      do endSubProof
         modifyTerm $ simplify $ (Free $ Global "elim_bottom") :!: t :@: (Bound i)
  | otherwise =
      throw ElimE1
elimComm _ _ _ = throw ElimE1

----------------------------------------------------------------------------------------------------------------------
-- Comando APPLY

applyComm :: Int -> (Type, TType) -> (Type, TType) -> Proof ()
applyComm i x ht@(Fun _ _, TFun _ _) = 
  do n <- compareTypes ht x
     evaluateSubProof n $ getTypesFun n ht
     modifyTerm $ getApplyTermFun n i
applyComm i x ht@(ForAll _ _, TForAll _) =
  do let equal = snd ht == snd x
     let (ft, n) = getNestedTypeForAll equal (snd ht)
     r <- eitherToProof $ unification equal n ft x
     let m = n - M.size r
     evaluateSubProof m $ getTypesForAll m
     modifyTerm $ getApplyTermForAll n r (Bound i)
applyComm i (t1, t1') (t, t')
  | t' == t1' = do evaluateSubProof 0 []
                   modifyTerm $ simplify (Bound i)
  | otherwise = throw $ ApplyE1 t t1
  

-- Funciones auxiliares para la función applyComm'

compareTypes :: (Type, TType) -> (Type, TType) -> Proof Int
compareTypes x@(_,t') y@(_,t)
 | t' == t = return 0
 | otherwise =  compareTypes' x y

compareTypes' :: (Type, TType) -> (Type, TType) -> Proof Int
compareTypes' (Fun _ y1, TFun _ y1') t
  | y1' == snd t = return 1
  | otherwise = do n <- compareTypes' (y1, y1') t
                   return $ n + 1
compareTypes' (x, _) (y, _) = throw $ ApplyE1 x y


getTypesFun :: Int -> (Type, TType) -> [Maybe (Type, TType)]
getTypesFun n (Fun t1 t2, TFun t1' t2')
  | n > 0 = Just (t1,t1') : getTypesFun (n-1) (t2, t2')
  | otherwise = error "error: getTypesFun, no debería pasar 1."
getTypesFun 0 _ = []
getTypesFun _ _ = error $ "error: getTypesFun, no debería pasar 2."


getNestedTypeForAll :: Bool -> TType -> (TType, Int)
getNestedTypeForAll flag x
  | flag = (x, 0)
  | otherwise = getNestedTypeForAll' x

getNestedTypeForAll' :: TType -> (TType, Int)
getNestedTypeForAll' (TForAll x) = let (f, n) = getNestedTypeForAll' x
                                   in (f, n+1)
getNestedTypeForAll' x = (x,0)

getApplyTermFun :: Int -> Int -> [SpecialTerm] -> [SpecialTerm]
getApplyTermFun 0 i ts = simplify (Bound i) ts
getApplyTermFun 1 i ts = addHT (\x -> (Bound i) :@: x) ts
getApplyTermFun 2 i ts = addDHT (\x y -> ((Bound i) :@: x) :@: y) ts
getApplyTermFun n i ts = getApplyTermFun (n-1) i $ addDHT (\x y -> x :@: y) ts


repeatElem :: Int -> a -> [a]
repeatElem n x
  | n == 0 = []
  | n > 0 = x : repeatElem (n-1) x
  | otherwise = error "error: repeatElem, no debería pasar."

getTypesForAll :: Int -> [Maybe (Type, TType)]
getTypesForAll m = repeatElem m Nothing

getApplyTermForAll :: Int -> M.Map Int (Type, TType) -> Term -> [SpecialTerm] -> [SpecialTerm]
getApplyTermForAll n sust t ts = case termForAll n t sust of
                                  Term x -> simplify x ts
                                  TypeH x -> TypeH x : ts
                                  _ -> error "error: getApplyTermForAll, no debería pasar"


termForAll :: Int -> Term -> M.Map Int (Type, TType) -> SpecialTerm
termForAll n t sust
  | n == 0 = Term t
  | n > 0 = termForAll' 0 (n-1) (Term t) sust
  | otherwise = error "error: termForAll, no deberia pasar."

termForAll' :: Int -> Int -> SpecialTerm -> M.Map Int (Type, TType)  -> SpecialTerm
termForAll' n m t sust
  | n < 0 = error "error: termForAll', no deberia pasar."
  | otherwise =
    case M.lookup n sust of
      Nothing ->let tt = TypeH $ addTypeHole t
                in if n == m
                   then tt
                   else termForAll' (n+1) m tt sust
      Just x -> let tt = addTypeTermST t x
                in if n == m
                   then tt
                   else termForAll' (n+1) m tt sust

----------------------------------------------------------------------------------------------------------------------
-- Comando EXACT

exactType :: (Type, TType) -> Proof ()
exactType ty =
  endSubProof >>
  (modifyTerm $ simplifyTypeInTerm ty)

exactTerm :: (LamTerm, Term) -> Proof ()
exactTerm te =
  do c <- getTermContext
     teo <- getTeorems
     q <- getTBTypeVars
     op <- getUsrOpers
     (_,t') <- eitherToProof $ inferType q c teo op te
     x <- getType
     (tt,tt') <- maybeToProof EmptyType x
     unless (t' == tt') $ throw $ ExactE1 tt
     endSubProof
     modifyTerm $ simplify (snd te)

----------------------------------------------------------------------------------------------------------------------
-- Comando UNFOLD

-- Argumentos:
-- 1. Conjunto de variables de tipos ligadas.
-- 2. Conjunto de variables de tipos libres.
-- 3. Código de la operación a "unfoldear".
-- 4. Tipo (con y sin nombre) sobre el que se aplica el unfold.
-- 5. Tipo (con y sin nombre) que define al operador foldeado (sin los para todos).
unfoldComm :: BTypeContext -> FTypeContext -> Int -> (Type, TType) -> (Type, TType) -> (Type, TType)
unfoldComm bs = unfoldComm' (foldr (\(_,x) xs -> x : xs) [] bs)

unfoldComm' :: [String] -> [String] -> Int -> (Type, TType) -> (Type, TType) -> (Type, TType)
unfoldComm' _ _ _ t@(B _, _) _ = t
unfoldComm' btc ftc code (RenameTy s l ts, RenameTTy m ts') body
  | m == code = applyTypes l ftc btc body mapUnfoldComm'
  | otherwise = let (xs, ys) = unzip mapUnfoldComm'
                in (RenameTy s l xs, RenameTTy m ys)
    where mapUnfoldComm' = map (\x -> unfoldComm' btc ftc code x body) $ zip ts ts'
unfoldComm' btc ftc code (Fun t t', TFun tt tt') body =
  let (t1,t1') = unfoldComm' btc ftc code (t,tt) body 
      (t2,t2') = unfoldComm' btc ftc code (t',tt') body
  in (Fun t1 t2, TFun t1' t2')
unfoldComm' btc ftc code (ForAll v t, TForAll t') body =
  let (t1, t1') = unfoldComm' (v:btc) ftc code (t,t') body
  in (ForAll v t1, TForAll t1')
unfoldComm' btc ftc code (Exists v t, TExists t') body =
  let (t1, t1') = unfoldComm' (v:btc) ftc code (t,t') body
  in (Exists v t1, TExists t1')


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
applyTypes :: Int -> [String] -> [String] -> (Type, TType) -> [(Type, TType)] -> (Type, TType)
applyTypes _ _ _ t [] = t
applyTypes l fs bs t xs = applyTypes' 0 l fs bs bs t xs

-- Realiza la sust. de tipos.
-- 1. Profundidad ("para todos"), procesados.
-- 2. Cantidad de tipos a reemplazar (podemos pensarlo como el número de corrimientos).
-- 3. Conjunto de variables de tipo libres.
-- 4. Conjunto de variables de tipo ligadas (con nombres) procesadas.
-- 5. Conjunto de los renombres de las variables de tipo ligadas (con nombres) del 4º arg.
--    Incluye además las var. de tipo ligadas del contexto.
-- 6. Tipo sobre el que se hace la sust. Sin los "para todos" que se van a sustituir.
-- 7. Tipos que se sustituyen.
applyTypes' :: Int -> Int -> FTypeContext -> [String] -> [String]
            -> (Type, TType) -> [(Type, TType)] -> (Type, TType)
applyTypes' n l fs bs rs (B v, TBound x) ts
  | x < n = case findIndex (\x -> x == v) bs of
              Just i -> (B $ rs !! i, TBound x)
              Nothing -> error "error: applyTypes', no debería pasar."
  | (n <= x) && (x < l) =
      let (ty,ty') = ts !! (l - x - 1)
      in (renameType fs rs ty, renameTType n ty')
  | otherwise = (B v, TBound $ x - l + n)
applyTypes' _ _ _ _ _ x@(_, TFree f) _ = x
applyTypes' n l fs bs rs (ForAll v t1, TForAll t1') ts =
  let v' = getRename v fs rs
      (tt, tt') = applyTypes' (n+1) (l+1) fs (v:bs) (v':rs) (t1,t1') ts
  in (ForAll v' tt, TForAll tt')
applyTypes' n l fs bs rs (Exists v t1, TExists t1') ts =
  let v' = getRename v fs rs
      (tt, tt') = applyTypes' (n+1) (l+1) fs (v:bs) (v':rs) (t1,t1') ts
  in (Exists v' tt, TExists tt')
applyTypes' n l fs bs rs (Fun t1 t2, TFun t1' t2') ts =
  let (tt1, tt1') = applyTypes' n l fs bs rs (t1,t1') ts
      (tt2, tt2') = applyTypes' n l fs bs rs (t2,t2') ts
  in (Fun tt1 tt2, TFun tt1' tt2')
applyTypes' n l fs bs rs (RenameTy s args xs, RenameTTy op xs') ts =
  let (r, r') = unzip $ map (\x -> applyTypes' n l fs bs rs x ts) $ zip xs xs'
  in (RenameTy s args r, RenameTTy op r')


-- Renombra las variables de tipo ligadas de un tipo con nombres válido.
-- Argumentos:
-- 1. Conjunto de variables de tipo libres.
-- 2. Conjunto de variables de tipos ligadas del contexto.
-- Es decir que tiene los nombres de la variables que no puede aparecer ligadas
-- en el resultado.
-- 3. Tipo sobre el que se realiza el renombramiento.
-- Obs: Asumimos que el tipo del 3º argumento está bien formado. Es decir que,
-- NO tiene variables espadas que no han sido declaradas en el contexto.
renameType :: FTypeContext -> [String] -> Type -> Type
renameType = renameType' []

renameType' :: [String] -> FTypeContext -> [String] -> Type -> Type
renameType' bs fs rs (B v) =
  case v `elemIndex` bs of
    Just i -> B $ rs !! i
    Nothing -> B v
renameType' bs fs rs (ForAll v t) = let v' = getRename v fs rs
                                    in ForAll v' $ renameType' (v:bs) fs (v':rs) t
renameType' bs fs rs (Exists v t) = let v' = getRename v fs rs
                                    in Exists v' $ renameType' (v:bs) fs (v':rs) t
renameType' bs fs rs (Fun t t') = Fun (renameType' bs fs rs t) (renameType' bs fs rs t')
renameType' bs fs rs (RenameTy s args ts) = RenameTy s args $ map (renameType' bs fs rs) ts

-- Realiza la sust. de tipos. sin nombre.
applyTTypes :: Int -> TType -> [TType] -> TType
applyTTypes _ t [] = t
applyTTypes l t xs = applyTTypes' 0 l t xs

-- Realiza la sust. de tipos sin nombre.
-- 1. Profundidad ("para todos"), procesados.
-- 2. Cantidad de tipos a reemplazar (podemos pensarlo como el número de corrimientos).
-- 3. Tipo sin nombre, sobre el que se hace la sust. Sin los "para todos" que se van a sustituir.
-- 4. Tipos sin nombre que se sustituyen.
applyTTypes' :: Int -> Int -> TType -> [TType] -> TType
applyTTypes' n l (TBound x) ts
  | x < n = TBound x
  | (n <= x) && (x < l) =
      renameTType n $ ts !! (l - x - 1)
  | otherwise = TBound $ x - l + n
applyTTypes' _ _ t@(TFree f) _ = t
applyTTypes' n l (TForAll t1) ts =
  TForAll $ applyTTypes' (n+1) (l+1) t1 ts
applyTTypes' n l (TExists t1) ts =
  TExists $ applyTTypes' (n+1) (l+1) t1 ts
applyTTypes' n l (TFun t1 t2) ts =
  TFun (applyTTypes' n l t1 ts) (applyTTypes' n l t2 ts)
applyTTypes' n l (RenameTTy op xs) ts =
  RenameTTy op $ map (\x -> applyTTypes' n l x ts) xs

----------------------------------------------------------------------------------------------------------------------
-- Algoritmo de unificación para el comando APPLY.

unification :: Bool -> Int -> TType -> (Type,TType) ->
  Either ProofExceptions (M.Map Int (Type,TType))
unification True _ = \ _ _ -> return M.empty
unification False n = unif 0 n M.empty

-- Se obtiene el conjunto de sustituciones que hacen que los tipos unifiquen.
-- Argumentos:
-- 1. Cantidad de "para todos" analizados.
-- 2. Cantidad de instancias a generar.
-- 3. Sustituciones encontradas. La clave indica la posición de la sustitucición (el valor), desde la izquierda.
-- Osea, si c1 < c2 => [t1/v1]..[t2/v2] (donde v1 y v2, son las variables con nombres de las variables sin nombres).
-- 4. El tipo sin nombre al que se le halla la unificación (sin los "para todos" externos).
-- 5. El tipo con y sin nombre, con el debe unificar el tipo dado en el 4º arg.
unif :: Int -> Int -> M.Map Int (Type,TType) -> TType -> (Type,TType) ->
  Either ProofExceptions (M.Map Int (Type,TType))
unif pos n sust t@(TBound i) tt@(tt1,tt2)
  | (pos <= i) && (i < n) =
    let k = n - 1 - i
    in case M.lookup k sust of
         Nothing -> maybe (throw Unif1)
                    (\s -> return $ M.insert k s sust) (substitution pos tt)
         Just (_,s) -> if renameTType pos s == tt2
                       then return sust
                       else throw Unif1
  | i < pos = if t == tt2
              then return $ sust
              else throw Unif2
  | otherwise = if TBound (i-n) == tt2
                then return $ sust
                else throw Unif2
unif _ _ sust (TFree x) (B _, TFree y)
  | x == y = return sust
  | otherwise = throw Unif3
unif pos n sust (TFun t1' t2') (Fun tt1 tt2, TFun tt1' tt2') =
  do res <- unif pos n sust t1' (tt1, tt1')
     unif pos n res t2' (tt2,tt2')
unif pos n sust (RenameTTy x ts) (RenameTy _ _ tts, RenameTTy y tts')
  | x == y = unifRename pos n sust ts tts tts'
  | otherwise = throw Unif4                
unif pos n sust (TForAll t') (ForAll _ tt, TForAll tt') = unif (pos+1) (n+1) sust t' (tt,tt')
unif pos n sust (TExists t') (Exists _ tt, TExists tt') = unif (pos+1) (n+1) sust t' (tt,tt')
unif _ _ _ _ _ = throw Unif4

-- Función auxiliar de unif. Trata el caso en el tipo a unificar sea una operación "foldeable".
unifRename :: Int -> Int -> M.Map Int (Type,TType) ->
              [TType] -> [Type] -> [TType] -> Either ProofExceptions (M.Map Int (Type,TType))
unifRename pos n sust [] [] [] = return sust
unifRename pos n sust (t:ts) (tt:tts) (tt':tts') =
  do res <- unif pos n sust t (tt, tt')
     unifRename pos n res ts tts tts'

-- Obtiene la substitución para la unificación, de acuerdo a la profundidad dada por el 1º argumento.
-- Realiza un corrimiento "negativo" de las variables de tipo escapadas.
-- Argumentos:
-- 1. Número de corrimiento.
-- 2. Tipo sobre el que se realiza el corrimiento.
substitution :: Int -> (Type, TType) -> Maybe (Type, TType)
substitution = substitution' 0

substitution' :: Int -> Int -> (Type, TType) -> Maybe (Type, TType)
substitution' m n (t,t'@(TBound x))
  | x < m = return (t,t')
  | (m <= x) && (x < n) = Nothing
  | otherwise = return (t, TBound $ x - n + m)
substitution' _ _ (t, t'@(TFree f)) = return (t,t')
substitution' m n (Fun t1 t2,TFun t1' t2') =
  do (x,x') <- substitution' m n (t1,t1')
     (y,y') <- substitution' m n (t2,t2')
     return (Fun x y, TFun x' y')
substitution' m n (RenameTy s args ts, RenameTTy op ts') =
  do rs <- sequence $ map (substitution' m n) $ zip ts ts'
     let (xs,ys) =  unzip rs
     return (RenameTy s args xs, RenameTTy op ys)
substitution' m n (ForAll v t, TForAll t') =
  do (x,x') <- substitution' (m+1) (n+1) (t,t')
     return (ForAll v x, TForAll x')
substitution' m n (Exists v t, TExists t') =
  do (x,x') <- substitution' (m+1) (n+1) (t,t')
     return (Exists v x, TExists x')

----------------------------------------------------------------------------------------------------------------------
-- Algoritmo de inferencia de tipos de un lambda término.

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
inferType :: Int -> TermContext -> Teorems -> FOperations
          -> (LamTerm, Term) -> Either ProofExceptions (Type, TType)
inferType n c te op t = case inferType' n c te op t of
                          Right r -> return r
                          Left e -> throw $ InferE (fst t) e

inferType' :: Int -> TermContext -> Teorems -> FOperations
          -> (LamTerm, Term) -> Either InferExceptions (Type, TType)
inferType' n _ te _ (_, Free (Global x)) =
  case M.lookup x te of
    Just (_ ::: t) -> return t
    Nothing -> throw $ InferE1 x -- NO puede haber variables de términos libres que no sean teoremas.
    _ -> error "error: inferType', no debería pasar."
inferType' n c te _ (_, Bound x) =
  let (_,m,t,t') = c V.! x
  in return (t,renameTType (n-m) t')
inferType' n c te op (Abs _ _ e, Lam (t,t') e') =
  do (tt,tt') <- inferType' n (V.cons (0,n,t,t') c) te op (e,e')
     return (Fun t tt, TFun t' tt')
inferType' n c te op (App e1 e2, e1' :@: e2') =
  do tt1 <- inferType' n c te op (e1, e1')
     case tt1 of
       (Fun t1 t2, TFun t1' t2') ->
         do (tt2, tt2') <- inferType' n c te op (e2, e2')
            if compareTTypes op tt2' t1'
              then return (t2, t2')
              else throw $ InferE2 e2 t1
       _ -> throw $ InferE3 e1 "* -> *"
inferType' n c te op (BAbs _ e, BLam v e') =
  do (t,t') <- inferType' (n+1) c te op (e, e')
     return (ForAll v t, TForAll t')
inferType' n c te op (BApp e _, e' :!: (t,t')) =
  do tt <- inferType' n c te op (e, e')
     case tt of
       (ForAll _ t1, TForAll t1') ->
         return $ inferReplaceType (t1,t1') (t,t')
       _ -> throw $ InferE3 e "forall *"
inferType' n c te op (EPack _ e _, Pack t1 e' t@(Exists _ t2 , TExists t2')) =
  do (_,tt1') <- inferType' n c te op (e, e')
     let (tt2, tt2') = inferReplaceType (t2,t2') t1
     if compareTTypes op tt1' tt2'
       then return t
       else throw $ InferE2 e tt2
inferType' n c te op (EUnpack _ _ e1 e2, Unpack _ e1' e2') =
  do t1 <- inferType' n c te op (e1, e1')
     case t1 of
       (Exists _ tt1, TExists tt1') -> 
         do t2 <- inferType' (n+1) (V.cons (0,n+1,tt1,tt1') c) te op (e2, e2')
            case substitution 1 t2 of
              Just t2' -> return t2'
              Nothing -> throw $ InferE4 e2
       _ -> throw $ InferE3 e1 "exists *"
inferType' n c te op (As e _, e' ::: t@(tt,tt')) =
  do (_, t1') <- inferType' n c te op (e, e')
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
  case op V.!? n of
    Just (_, (_, t), args, _) ->
      applyTTypes args (basicTType op t) basics
      --in error $ show t ++ "\n\n" ++ show (applyTTypes l t basics)
    Nothing -> RenameTTy n basics
  where basics = map (basicTType op) xs


-- Realiza un corrimiento "positivo" sobre las variables de tipo ligadas "escapadas".
-- Argumentos:
-- 1. Número de corrimiento.
-- 2. Tipo sin nombre sobre el que se realiza el corrimiento.
renameTType :: Int -> TType -> TType
renameTType 0 = id
renameTType n = renameTType' 0 n

renameTType' :: Int -> Int -> TType -> TType
renameTType' n r t@(TBound x)
  | x < n = t
  | otherwise = TBound (x+r)
renameTType' _ _ t@(TFree x) = t
renameTType' n r (TForAll t) = TForAll $ renameTType' (n+1) r t
renameTType' n r (TExists t) = TExists $ renameTType' (n+1) r t
renameTType' n r (TFun t1 t2) = TFun (renameTType' n r t1) (renameTType' n r t2)
renameTType' n r (RenameTTy op ts) = RenameTTy op $ map (renameTType' n r) ts

-- Consideramos que el 1º argumento corresponde al cuerpo de una cuantificación ("para todo", "existe").
-- Se reemplaza la variable ligada más "externa" por el 2º argumento.
-- Además, se corrigen las varibles ligadas escapadas.
inferReplaceType :: (Type, TType) -> (Type, TType) -> (Type, TType)
inferReplaceType = inferReplaceType' 0

inferReplaceType' :: Int -> (Type, TType) -> (Type, TType) -> (Type, TType)
inferReplaceType' n x@(tt, TBound m) (t, t')
  | n == m = (t, renameTType n t')
  | m > n = (tt, TBound (m-1))
  | otherwise = x
inferReplaceType' n x@(tt, TFree f) _ = x
inferReplaceType' n (ForAll v t1, TForAll t1') t =
  let (tt, tt') = inferReplaceType' (n+1) (t1,t1') t
  in (ForAll v tt, TForAll tt')
inferReplaceType' n (Exists v t1, TExists t1') t =
  let (tt, tt') = inferReplaceType' (n+1) (t1,t1') t
  in (Exists v tt, TExists tt')
inferReplaceType' n (Fun t1 t2, TFun t1' t2') t =
  let (tt1, tt1') = inferReplaceType' n (t1,t1') t
      (tt2, tt2') = inferReplaceType' n (t2,t2') t
  in (Fun tt1 tt2, TFun tt1' tt2')
inferReplaceType' n (RenameTy s args ts, RenameTTy op ts') t =
  let (xs, ys) = unzip $ map (\x -> inferReplaceType' n x t) $ zip ts ts'
  in (RenameTy s args xs, RenameTTy op ys)

-- Obtiene el tipo de la variable de término, renombrando su tipo sin nombres, de acuerdo
-- a la profundidad dada por el 1º argumento.
getTypeVar :: Int -> TermVar -> (Type, TType)
getTypeVar n (_,m, t, t') = (t, renameTType (n-m) t')


----------------------------------------------------------------------------------------------------------------------
-- Funciones auxiliares de "habitar".

maybeToProof :: ProofExceptions -> Maybe a -> Proof a
maybeToProof excep Nothing = throw excep
maybeToProof _ (Just val) = return val

eitherToProof :: Either ProofExceptions a -> Proof a
eitherToProof (Left e) = throw e
eitherToProof (Right x) = return x
