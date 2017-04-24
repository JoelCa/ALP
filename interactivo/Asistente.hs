module Asistente where

import Common
import Data.Char (isDigit)
import Data.List (findIndex, elemIndex, find)
import Control.Monad (unless, when)
import qualified Data.Map as M (Map, lookup, insert, empty, size)
import qualified Data.Sequence as S
import Data.Maybe (fromJust, isJust)
import ProofState
import qualified Data.Vector as V

-- Contruye la prueba.
habitar :: Tactic -> Proof ()
habitar Assumption =
  do x <- getType
     (_,tw) <- maybeToProof EmptyType x 
     c <- getTermContext
     q <- getTBTypeVars
     i <- maybeToProof AssuE (S.findIndexL
                              (\(_,p,_,t) -> renameTType (q - p) t == tw)
                               c)
     endSubProof
     modifyTerm $ simplify (Bound i)
habitar Intro =
  do x <- getType
     introComm x
habitar Intros =
  introsComm
habitar (Apply h) =
  do x <- getType
     (t,t') <- maybeToProof EmptyType x
     n <- getTTermVars
     i <- maybeToProof (HypoE h) $ getHypothesisValue n h
     c <- getTermContext
     q <- getTBTypeVars
     applyComm (n-i-1) (t,t') (getTypeVar q $ S.index c (n-i-1))
habitar (Elim h) =
  do x <- getType
     (t,t') <- maybeToProof EmptyType x
     n <- getTTermVars
     i <- maybeToProof (HypoE h) $ getHypothesisValue n h
     c <- getTermContext
     q <- getTBTypeVars
     elimComm (n-i-1) (t,t') (getTypeVar q $ S.index c (n-i-1))
habitar CLeft =
  do x <- getType
     case x of
       Just (RenameTy _ [t1,t2] , RenameTTy n [t1',t2']) ->
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
       Just (RenameTy _ [t1,t2] , RenameTTy n [t1',t2']) ->
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
       Just (RenameTy _ [t1,t2], RenameTTy n [t1',t2']) ->
         if n == and_code
         then do newSubProofs 2 [Just (t1,t1'), Just (t2,t2')]
                 modifyTerm $ addDHT (\x y -> ((Free $ Global "intro_and")
                                                :!: (t1,t1') :!: (t2,t2'))
                                              :@: x :@: y)
         else throw CommandInvalid
       _ -> throw CommandInvalid
habitar (Exact (Right te)) =
  do op <- getUsrOpers
     n <- getTTermVars
     btc <- getBTypeContext
     ftc <- getFTypeContext
     te' <- eitherToProof $ withoutName op ftc btc n te
     c <- getTermContext
     teo <- getTeorems
     q <- getTBTypeVars
     (_,t') <- eitherToProof $ inferType q c teo te'
     x <- getType
     (tt,tt') <- maybeToProof EmptyType x
     unless (t' == tt') $ throw $ ExactE1 tt
     endSubProof
     modifyTerm $ simplify (snd te')
habitar (Exact (Left ty)) =
  do x <- getType
     when (isJust x) $ throw $ ExactE2 $ fst $ fromJust x
     op <- getUsrOpers
     btc <- getBTypeContext
     ftc <- getFTypeContext
     ty' <- eitherToProof $ getRenamedType op ftc btc ty
     endSubProof
     modifyTerm $ simplifyTypeInTerm ty'
habitar (Unfold s Nothing) =
  do x <- getType
     (t,t') <- maybeToProof EmptyType x
     op <- getUsrOpers
     (m, (_, (tt,tt'), _, _)) <- maybeToProof (UnfoldE1 s) $ getElemIndex (\(x,_,_,_) -> x == s) op
     btc <- getBTypeContext
     ftc <- getFTypeContext
     replaceType $ unfoldComm (t,t') (tt,tt') m btc ftc
habitar (Unfold s (Just h)) =
  do op <- getUsrOpers
     (m, (_, (tt,tt'), _, _)) <- maybeToProof (UnfoldE1 s) $ getElemIndex (\(x,_,_,_) -> x == s) op
     n <- getTTermVars
     i <- maybeToProof (HypoE h) $ getHypothesisValue n h
     c <- getTermContext
     let (x,y,t,t') = S.index c (n-i-1)
     btc <- getBTypeContext
     ftc <- getFTypeContext
     let (r,r') = unfoldComm (t,t') (tt,tt') m btc ftc
     updateTermContext (n-i-1) (x,y,r,r')
habitar (Absurd ty) =
  do x <- getType
     case x of
       Just (RenameTy _ [] , RenameTTy n []) ->
         if n == bottom_code
         then do op <- getUsrOpers
                 btc <- getBTypeContext
                 ftc <- getFTypeContext
                 (tty, tty') <- eitherToProof $ getRenamedType op ftc btc ty
                 newSubProofs 2 [ Just (tty, tty')
                                , Just (RenameTy not_text [tty], RenameTTy not_code [tty']) ]
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
            ty' <- eitherToProof $ getRenamedType op ftc btc ty
            replaceType $ applyTypes 1 ftc btc (t,t') [ty']
            modifyTerm $ addHT (\x -> (ty', x) ::: tt)
       _ -> throw CommandInvalid
habitar (Cut ty) =
  do x <- getType
     (t,t') <- maybeToProof EmptyType x
     op <- getUsrOpers
     btc <- getBTypeContext
     ftc <- getFTypeContext
     (tty, tty') <- eitherToProof $ getRenamedType op ftc btc ty
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
elimComm i (t,t') (RenameTy _ [t1,t2], RenameTTy n [t1',t2'])
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
elimComm i t (RenameTy _ [], RenameTTy n [])
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

-- addTypeHole añade al lambda término de su primer arg., una instancia de tipo "vacia".
-- Retorna el TypeHole con la instacia "vacia".
addTypeHole :: SpecialTerm -> TypeHole
addTypeHole (Term te) = HTe $ \y -> te :!: y
addTypeHole (TypeH hte) = HTy $ \y -> addTypeTerm hte y
addTypeHole _ = error "error: newTypeHole, no debería pasar."

-- addTypeTermST añade al lambda término de su primer arg., una instancia de tipo "vacia".
-- Retorna el SpecialTerm con la instacia "vacia".
addTypeTermST :: SpecialTerm -> (Type, TType) -> SpecialTerm
addTypeTermST (Term te) x = Term $ te :!: x
addTypeTermST (TypeH hte) x = TypeH $ addTypeTerm hte x
addTypeTermST _ _ = error "error: addTypeTerm, no debería pasar."

-- addTypeTerm añade al lambda término de su primer arg. (desempaquetando el TypeHole), una instancia de tipo,
-- con el tipo de su segundo argumento. Retorna el TypeHole con esta nueva instancia de tipo, respetando la misma
-- estructura del TypeHole de su primer arg.
addTypeTerm :: TypeHole -> (Type, TType) -> TypeHole
addTypeTerm (HTe h) x = HTe $ \y -> h y :!: x
addTypeTerm (HTy h) x = HTy $ \y -> addTypeTerm (h y) x

----------------------------------------------------------------------------------------------------------------------
-- Comando UNFOLD

-- Argumentos:
-- 1. Tipo (con y sin nombre) sobre el que se aplica el unfold.
-- 2. Tipo (con y sin nombre) que define al operador foldeado.
-- 3. Código de la operación a "unfoldear".
-- 4. Conjunto de variables de tipos ligadas.
-- 5. Conjunto de variables de tipos libres.
unfoldComm :: (Type, TType) -> (Type, TType) -> Int -> BTypeContext -> FTypeContext -> (Type, TType)
unfoldComm t@(B _, _) _ _ _ _ = t
unfoldComm (RenameTy s ts, RenameTTy m ts') r n btc ftc
  | m == n = let l = length mapUnfoldComm
             in applyTypes l ftc btc (getBodyForAll l r) mapUnfoldComm
  | otherwise = let (xs, ys) = unzip mapUnfoldComm
                in (RenameTy s xs, RenameTTy m ys)
    where mapUnfoldComm = map (\x -> unfoldComm x r n btc ftc) $ zip ts ts'
unfoldComm (Fun t t', TFun tt tt') r n btc ftc =
  let (t1,t1') = unfoldComm (t,tt) r n btc ftc
      (t2,t2') = unfoldComm (t',tt') r n btc ftc
  in (Fun t1 t2, TFun t1' t2')
unfoldComm (ForAll v t, TForAll t') r n btc ftc =
  let (t1, t1') = unfoldComm (t,t') r n btc ftc
  in (ForAll v t1, TForAll t1')
unfoldComm (Exists v t, TExists t') r n btc ftc =
  let (t1, t1') = unfoldComm (t,t') r n btc ftc
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
applyTypes :: Int -> FTypeContext -> BTypeContext -> (Type, TType) -> [(Type, TType)] -> (Type, TType)
applyTypes _ _ _ t [] = t
applyTypes l fs bs t xs = applyTypes' 0 l fs [] (foldr (\(_,x) xs -> x : xs) [] bs) t xs

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
applyTypes' n l fs bs rs (RenameTy s xs, RenameTTy op xs') ts =
  let (r, r') = unzip $ map (\x -> applyTypes' n l fs bs rs x ts) $ zip xs xs'
  in (RenameTy s r, RenameTTy op r')

-- Función auxiliar.
getBodyForAll :: Int -> (Type, TType) -> (Type, TType)
getBodyForAll 0 t = t
getBodyForAll n (ForAll _ t, TForAll t') = getBodyForAll (n-1) (t, t')
getBodyForAll _ _ = error "error: getBodyForAll, no debería pasar."

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
renameType' bs fs rs (RenameTy s ts) = RenameTy s $ map (renameType' bs fs rs) ts

----------------------------------------------------------------------------------------------------------------------
-- Reglas de eliminación e introducción del "and","or", y "bottom".

intro_and :: (Term, (Type,TType))
intro_and =
  (
    BLam "a" $ BLam "b" $ Lam (B "a", TBound 1) $ Lam (B "b", TBound 0) $ BLam "c" $
    Lam (Fun (B "a") $ Fun (B "b") (B "c"), TFun (TBound 2) $ TFun (TBound 1) (TBound 0)) $
    (Bound 0 :@: Bound 2) :@: Bound 1
  , (
      ForAll "a" $ ForAll "b" $ Fun (B "a") $ Fun (B "b") $ RenameTy and_text [B "a", B "b"]
    , TForAll $ TForAll $ TFun (TBound 1) $ TFun (TBound 0) $ RenameTTy and_code [TBound 1, TBound 0]
    )
  )

-- Teorema de eliminación del and "general": forall a b c, a /\ b -> (a -> b -> c) -> c
elim_and :: (Term, (Type,TType))
elim_and =
  (
    BLam "a" $ BLam "b" $ BLam "c" $ Lam (RenameTy and_text [B "a", B "b"], RenameTTy and_code [TBound 2, TBound 1]) $
    Lam (Fun (B "a") (Fun (B "b") (B "c")), TFun (TBound 2) (TFun (TBound 1) (TBound 0))) $
    (Bound 1) :!: (B "c", TBound 0) :@: (Bound 0)
  , (
      ForAll "a" $ ForAll "b" $ ForAll "c" $ Fun (RenameTy and_text [B "a", B "b"]) $
      Fun (Fun (B "a") $ Fun (B "b") (B "c")) $ B "c"
    , TForAll $ TForAll $ TForAll $ TFun (RenameTTy and_code [TBound 2, TBound 1]) $
      TFun (TFun (TBound 2) (TFun (TBound 1) (TBound 0))) $ TBound 0
    )
  )

intro_or1 :: (Term, (Type,TType))
intro_or1 =
  (
    BLam "a" $ BLam "b" $ Lam (B "a", TBound 1) $ BLam "c" $
    Lam (Fun (B "a") (B "c"), TFun (TBound 2) (TBound 0)) $
    Lam (Fun (B "b") (B "c"), TFun (TBound 1) (TBound 0)) $ Bound 1 :@: Bound 2
  ,
    (
      ForAll "a" $ ForAll "b" $ Fun (B "a") $ RenameTy or_text [B "a", B "b"]
    , TForAll $ TForAll $ TFun (TBound 1) $ RenameTTy or_code [TBound 1, TBound 0]
    )
   )

intro_or2 :: (Term, (Type,TType))
intro_or2 =
  (
    BLam "a" $ BLam "b" $ Lam (B "b", TBound 0) $ BLam "c" $
    Lam (Fun (B "a") (B "c"), TFun (TBound 2) (TBound 0)) $
    Lam (Fun (B "b") (B "c"), TFun (TBound 1) (TBound 0)) $ Bound 0 :@: Bound 2
  , (
      ForAll "a" $ ForAll "b" $ Fun (B "b") $ RenameTy or_text [B "a", B "b"]
    , TForAll $ TForAll $ TFun (TBound 0) $ RenameTTy or_code [TBound 1, TBound 0]
    )
  )

elim_or :: (Term, (Type,TType))
elim_or =
  (
    BLam "a" $ BLam "b" $ BLam "c" $ Lam (RenameTy or_text [B "a",B "b"], RenameTTy or_code [TBound 2, TBound 1]) $
    Lam (Fun (B "a") (B "c"), TFun (TBound 2) (TBound 0)) $
    Lam (Fun (B "b") (B "c"), TFun (TBound 1) (TBound 0)) $
    ((Bound 2 :!: (B "c", TBound 0)) :@: Bound 1) :@: Bound 0
  , (
      ForAll "a" $ ForAll "b" $ ForAll "c" $ Fun (RenameTy or_text [B "a", B "b"]) $
      Fun (Fun (B "a") (B "c")) $ Fun (Fun (B "b") (B "c")) $ B "c"
    , TForAll $ TForAll $ TForAll $ TFun (RenameTTy or_code [TBound 2, TBound 1]) $
      TFun (TFun (TBound 2) (TBound 0)) $ TFun (TFun (TBound 1) (TBound 0)) $ TBound 0
    )
  )

intro_bottom :: (Term, (Type,TType))
intro_bottom =
  (
    BLam "a" $ Lam (B "a", TBound 0) $ Lam (RenameTy not_text [B "a"], RenameTTy not_code [TBound 0]) $
    Bound 0 :@: Bound 1
  , (
      ForAll "a" $ Fun (B "a") $ Fun (RenameTy not_text [B "a"]) $ RenameTy bottom_text []
    , TForAll $ TFun (TBound 0) $ TFun (RenameTTy not_code [TBound 0]) $ RenameTTy bottom_code []
    )
  )

elim_bottom :: (Term, (Type,TType))
elim_bottom =
  (
    BLam "a" $ Lam (RenameTy bottom_text [], RenameTTy bottom_code []) $ Bound 0 :!: (B "a", TBound 0)
  , (
      ForAll "a" $ Fun (RenameTy bottom_text []) $ B "a"
    , TForAll $ TFun (RenameTTy bottom_code []) $ TBound 0
    )
  )

----------------------------------------------------------------------------------------------------------------------
-- Funciones que operan sobre los lambda términos con aujeros.

simplifyTypeInTerm :: (Type, TType) -> [SpecialTerm] -> [SpecialTerm]
simplifyTypeInTerm ty (TypeH (HTe h) : ts) = simplify (h ty) ts
simplifyTypeInTerm ty (TypeH (HTy h) : ts) = (TypeH $ h ty) : ts

simplify :: Term -> [SpecialTerm] -> [SpecialTerm]
simplify t [HoleT et] = [Term $ et t]
simplify t ((DoubleHoleT et):ts) = (HoleT $ et t):ts
simplify t ((HoleT et):(DoubleHoleT et'):ts) = (HoleT $ (et' . et) t):ts

addHT :: (Term->Term) -> [SpecialTerm] -> [SpecialTerm]
addHT et ((HoleT et'):ts) = (HoleT $ et' . et):ts
addHT et ((DoubleHoleT et'):ts) = (DoubleHoleT $ et' . et):ts

addDHT :: (Term->Term->Term) -> [SpecialTerm] -> [SpecialTerm]
addDHT et ((HoleT et'):ts) = (DoubleHoleT $ (\f -> et' . f) . et):ts
addDHT et ((DoubleHoleT et'):ts) = (DoubleHoleT et):(DoubleHoleT et'):ts

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
unif pos n sust (RenameTTy x ts) (RenameTy _ tts, RenameTTy y tts')
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
substitution' m n (RenameTy s ts, RenameTTy op ts') =
  do rs <- sequence $ map (substitution' m n) $ zip ts ts'
     let (xs,ys) =  unzip rs
     return (RenameTy s xs, RenameTTy op ys)
substitution' m n (ForAll v t, TForAll t') =
  do (x,x') <- substitution' (m+1) (n+1) (t,t')
     return (ForAll v x, TForAll x')
substitution' m n (Exists v t, TExists t') =
  do (x,x') <- substitution' (m+1) (n+1) (t,t')
     return (Exists v x, TExists x')

----------------------------------------------------------------------------------------------------------------------
-- Trasformadores: Se pasa de un tipo con nombre, al equivalente sin nombre.

-- Crea una variable en base al 1º arg. "v", que no está en ninguna de las listas de variables.
-- Sabemos que "v" ocurre en el 2º arg. "xs".
newVar :: String -> [String] -> [String] -> String
newVar v xs ys
  | elem v' xs = newVar v' xs ys
  | otherwise = if elem v' ys
                then newVar v' ys xs
                else v'
  where v' = v++"0"

getRename :: String -> [String] -> [String] -> String
getRename v fv rv 
  | elem v rv = newVar v rv fv
  | otherwise = if elem v fv
                then newVar v fv rv
                else v

-- Retorna el tipo de su segundo arg. con las siguientes características:
-- Un tipo equivalente si hay conflicto con las variables ligadas.
-- En notación de brujin.
-- El 1º arg. son el conj. de proposiciones válidas, y el 2º las operaciones "foldeables".
rename :: FTypeContext -> FOperations -> Type -> Either ProofExceptions (Type, TType)
rename = rename' [] []

rename' :: [String] -> [String] -> FTypeContext -> FOperations -> Type -> Either ProofExceptions (Type, TType)
rename' rv bv fv _ (B v) =
  case v `elemIndex` bv of
    Just i -> return (B $ rv!!i, TBound i)
    Nothing -> if elem v fv
               then return (B v, TFree v)
               else throw $ PropNotExists v
rename' rv bv fv op (ForAll v t) = do let v' = getRename v fv rv
                                      (x,y) <- rename' (v':rv) (v:bv) fv op t
                                      return (ForAll v' x, TForAll y)
rename' rv bv fv op (Exists v t) = do let v' = getRename v fv rv
                                      (x,y) <- rename' (v':rv) (v:bv) fv op t
                                      return (Exists v' x, TExists y)
rename' rv bv fv op (Fun t t') = do (x,y) <- rename' rv bv fv op t
                                    (x',y') <- rename' rv bv fv op t'
                                    return (Fun x x', TFun y y')
rename' rv bv fv op (RenameTy s ts) =
    case find (\(x,_,_) -> x == s) notFoldeableOps of
      Just (_,n,to) -> if checkOperands to ts
                       then do rs <- sequence $ map (rename' rv bv fv op) ts
                               let (xs,ys) = unzip rs
                               return (RenameTy s xs, RenameTTy n ys)
                       else throw $ OpE1 s
      Nothing -> do (m, (_,_,to,_)) <- maybeToEither (OpE2 s) $ getElemIndex (\(x,_,_,_) -> x == s) op
                    if checkOperands to ts
                      then do rs <- sequence $ map (rename' rv bv fv op) ts
                              let (xs,ys) = unzip rs
                              return (RenameTy s xs, RenameTTy m ys)
                      else throw $ OpE1 s

checkOperands :: Operands -> [a] -> Bool
checkOperands Empty [] = True
checkOperands Unary [_] = True
checkOperands Binary [_,_] = True
checkOperands _ _ = False
  
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
-- Se usa en el algoritmo de inferencia.
withoutName :: FOperations -> FTypeContext -> BTypeContext -> Int
            -> LamTerm -> Either ProofExceptions (LamTerm, Term)
withoutName op fs bs = let bs' = foldr (\(_,x) xs -> x : xs) [] bs
                       in withoutName' [] bs' bs' fs op

withoutName' :: [String] -> [String] -> [String] -> FTypeContext -> FOperations -> Int
             -> LamTerm -> Either ProofExceptions (LamTerm, Term)
withoutName' teb _ _ _ _ n w@(LVar x) =
  case elemIndex x teb of
    Just m -> return (w, Bound m)
    Nothing -> let r = case getHypothesisValue n x of
                         Just h -> Bound $ n - h - 1
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
     return (EPack (fst tt) ee (fst tt'), (tt, ee') ::: tt')
withoutName' teb rs bs fs op n (EUnpack x y e1 e2) =
  do (ee1, ee1') <- withoutName' teb rs bs fs op n e1
     let v = getRename x fs rs
     (ee2, ee2') <- withoutName' (y:teb) (v:rs) (x:bs) fs op n e2
     return (EUnpack v y ee1 ee2, Unpack v ee1' ee2')
     

typeWithoutName :: [String] -> [String] -> FTypeContext -> FOperations
                -> Type -> Either ProofExceptions (Type, TType)
typeWithoutName rs bs fs _ (B x) =
  case findIndex (\y -> y == x) bs of
    Just n -> return (B $ rs !! n, TBound n)
    Nothing -> if elem x fs
               then return (B x, TFree x)
               else throw $ TermE x
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
typeWithoutName rs bs fs op (RenameTy s ts) =
  case find (\(x,_,_) -> x == s) notFoldeableOps of
    Just (_,n,to) ->
      if checkOperands to ts
      then do rs <- sequence $ map (typeWithoutName rs bs fs op) ts
              let (tt, tt') = unzip rs
              return (RenameTy s tt, RenameTTy n tt')
      else throw $ OpE1 s
    Nothing ->
      do (m, (_,_,to,_)) <- maybeToEither (OpE2 s) $ getElemIndex (\(x,_,_,_) -> x == s) op
         if checkOperands to ts
           then do rs <- sequence $ map (typeWithoutName rs bs fs op) ts
                   let (tt, tt') = unzip rs
                   return (RenameTy s tt, RenameTTy m tt')
           else throw $ OpE1 s

-- Obtiene el tipo con nombre renombrado, y el tipo sin nombre, del tipo dado
-- por el 4º argumento.
-- El renombramiento se realiza de modo tal que se respete la Convención 1 (ver informe).
getRenamedType :: FOperations -> FTypeContext -> BTypeContext
               -> Type -> Either ProofExceptions (Type, TType)
getRenamedType op fs bs = let bs' = foldr (\(_,x) xs -> x : xs) [] bs
                          in typeWithoutName bs' bs' fs op
                 
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
inferType :: Int -> TermContext -> Teorems -> (LamTerm, Term) -> Either ProofExceptions (Type, TType)
inferType n _ te (_, Free (Global x)) =
  case M.lookup x te of
    Just (_,t) -> return t
    Nothing -> throw $ InferE1 x -- NO puede haber variables de términos libres que no sean teoremas.
inferType n c te (_, Bound x) =
  let (_,m,t,t') = S.index c x
  in return (t,renameTType (n-m) t')
inferType n c te (Abs _ _ e, Lam (t,t') e') =
  do (tt,tt') <- inferType n ((0,n,t,t') S.<| c) te (e,e')
     return (Fun t tt, TFun t' tt')
inferType n c te (App e1 e2, e1' :@: e2') =
  do (tt1, tt1') <- inferType n c te (e1, e1')
     case (tt1, tt1') of
       (Fun t1 t2, TFun t1' t2') ->
         do (tt2, tt2') <- inferType n c te (e2, e2')
            if tt2' == t1'
              then return (t2, t2')
              else throw $ InferE2 e2 t1
       _ -> throw $ InferE3 e1 "* -> *"
inferType n c te (BAbs _ e, BLam v e') =
  do (t,t') <- inferType (n+1) c te (e, e')
     return (ForAll v t, TForAll t')
inferType n c te (BApp e _, e' :!: (t,t')) =
  do (tt,tt') <- inferType n c te (e, e')
     case (tt, tt') of
       (ForAll _ t1, TForAll t1') ->
         return $ inferReplaceType (t1,t1') (t,t')
       _ -> throw $ InferE3 e "forall *"
inferType n c te (EPack _ e _, (t1,e') ::: t@(Exists _ t2 , TExists t2')) =
  do (tt1,tt1') <- inferType n c te (e, e')
     let (tt2, tt2') = inferReplaceType (t2,t2') t1
     if tt1' == tt2'
       then return t
       else throw $ InferE2 e tt2
inferType n c te (EUnpack _ _ e1 e2, Unpack _ e1' e2') =
  do t1 <- inferType n c te (e1, e1')
     case t1 of
       (Exists _ tt1, TExists tt1') -> 
         do t2 <- inferType (n+1) ((0,n+1,tt1,tt1') S.<| c) te (e2, e2')
            case substitution 1 t2 of
              Just t2' -> return t2'
              Nothing -> throw $ InferE4 e2
       _ -> throw $ InferE3 e1 "exists *"

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
inferReplaceType' n (RenameTy s ts, RenameTTy op ts') t =
  let (xs, ys) = unzip $ map (\x -> inferReplaceType' n x t) $ zip ts ts'
  in (RenameTy s xs, RenameTTy op ys)

-- Obtiene el tipo de la variable de término, renombrando su tipo sin nombres, de acuerdo
-- a la profundidad dada por el 1º argumento.
getTypeVar :: Int -> TermVar -> (Type, TType)
getTypeVar n (_,m, t, t') = (t, renameTType (n-m) t')


----------------------------------------------------------------------------------------------------------------------
-- Funciones auxiliares de "habitar".

-- Obtiene el entero que contiene el 2º argumento.
-- Además, chequea que dicho valor sea válido.
getHypothesisValue :: Int -> String -> Maybe Int
getHypothesisValue n h
  | n <= 0 = Nothing
  | isDefault h = let x = getValue h
                  in if isValidValue n x
                     then return x
                     else Nothing
  | otherwise = Nothing

isDefault :: String -> Bool
isDefault ('H':xs) = isNumber xs
isDefault _ = False

isNumber :: String -> Bool
isNumber [x] = isDigit x
isNumber (x:xs) = (isDigit x) && (isNumber xs)
isNumber [] = False

getValue :: String -> Int
getValue (x:xs) = read xs :: Int
getValue _ = undefined

isValidValue :: Int -> Int -> Bool
isValidValue n value = (value >= 0) && (value < n)


maybeToEither :: e -> Maybe a -> Either e a
maybeToEither errorval Nothing = throw errorval
maybeToEither _ (Just normalval) = return normalval

maybeToProof :: ProofExceptions -> Maybe a -> Proof a
maybeToProof excep Nothing = throw excep
maybeToProof _ (Just val) = return val

eitherToProof :: Either ProofExceptions a -> Proof a
eitherToProof (Left e) = throw e
eitherToProof (Right x) = return x

pred :: Int -> Int
pred n
  | n <= 0 = 0
  | n > 0 = n-1
