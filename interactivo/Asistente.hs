module Asistente where

import Common
import Data.Char (isDigit)
import Data.List (findIndex, elemIndex, find)
import Control.Monad (unless, when)
import qualified Data.Map as M (Map, lookup, insert, empty, size)
import qualified Data.Sequence as S
import Data.Maybe (fromJust, isJust)
import ProofState
import Data.Foldable (foldl)

-- Contruye la prueba.
habitar :: Tactic -> Proof ()
habitar Assumption = do x <- getType
                        (_,tw) <- maybeToProof EmptyType x 
                        c <- getTermContext
                        q <- getTBTypeVars
                        i <- maybeToProof AssuE (S.findIndexL
                                                  (\(_,p,_,t) -> renameTType (q - p) t == tw)
                                                  c)
                        modifySubProofs 0 id
                        modifyTerm $ simplify (Bound i)
habitar Intro = do x <- getType
                   introComm x
habitar Intros = introsComm
habitar (Apply h) = do x <- getType
                       (t,t') <- maybeToProof EmptyType x
                       n <- getTTermVars
                       i <- maybeToProof ApplyE2 $ getHypothesisValue n h
                       c <- getTermContext
                       q <- getTBTypeVars
                       applyComm (n-i-1) (t,t') (getTypeVar q $ S.index c (n-i-1))
habitar (Elim h) = do x <- getType
                      (t,t') <- maybeToProof EmptyType x
                      n <- getTTermVars
                      i <- maybeToProof ApplyE2 $ getHypothesisValue n h
                      c <- getTermContext
                      q <- getTBTypeVars
                      elimComm (n-i-1) (t,t') (getTypeVar q $ S.index c (n-i-1))
habitar CLeft = do x <- getType
                   case x of
                     Just (RenameTy _ [t1,t2] , RenameTTy n [t1',t2']) ->
                       if n == or_code
                          then do replaceType (t1,t1')
                                  modifyTerm $ addHT (\x -> ((Free $ Global "intro_or1")
                                                             :!: (t1,t1') :!: (t2,t2'))
                                                            :@: x)
                       else throw CommandInvalid
                     _ -> throw CommandInvalid
habitar CRight = do x <- getType
                    case x of
                      Just (RenameTy _ [t1,t2] , RenameTTy n [t1',t2']) ->
                        if n == or_code
                        then do replaceType (t2,t2')
                                modifyTerm $ addHT (\x -> ((Free $ Global "intro_or2")
                                                           :!: (t1,t1') :!: (t2,t2'))
                                                          :@: x)
                        else throw CommandInvalid
                      _ -> throw CommandInvalid
habitar Split = do x <- getType
                   case x of
                     Just (RenameTy _ [t1,t2], RenameTTy n [t1',t2']) ->
                       if n == and_code
                       then do modifySubProofs 2 (\tys -> Just (t1,t1') : Just (t2,t2') : tys)
                               modifyTerm $ addDHT (\x y -> ((Free $ Global "intro_and")
                                                             :!: (t1,t1') :!: (t2,t2'))
                                                            :@: x :@: y)
                       else throw CommandInvalid
                     _ -> throw CommandInvalid
habitar (Exact (Right te)) = do op <- getUsrOpers
                                n <- getTTermVars
                                btc <- getBTypeContext
                                ftc <- getFTypeContext
                                te' <- eitherToProof $ withoutName op n (ftc,btc) te
                                c <- getTermContext
                                teo <- getTeorems
                                q <- getTBTypeVars
                                (_,t') <- eitherToProof $ inferType q c teo te'
                                x <- getType
                                (tt,tt') <- maybeToProof EmptyType x
                                unless (t' == tt') $ throw $ ExactE1 tt
                                modifySubProofs 0 id
                                modifyTerm $ simplify te'
habitar (Exact (Left ty)) = do x <- getType
                               when (isJust x) $ throw $ ExactE2 $ fst $ fromJust x
                               op <- getUsrOpers
                               btc <- getBTypeContext
                               ftc <- getFTypeContext
                               ty' <- eitherToProof $ typeWhitoutName op (ftc,btc) ty
                               modifySubProofs 0 id
                               modifyTerm $ simplifyTypeInTerm (ty,ty')
habitar (Unfold s Nothing) = do x <- getType
                                (t,t') <- maybeToProof EmptyType x
                                op <- getUsrOpers
                                case findIndex (\(x,_,_,_) -> x == s) op of
                                  Just m -> do let (_, (tt,tt'), _, _) = op !! m
                                               btc <- getBTypeContext
                                               ftc <- getFTypeContext
                                               replaceType $ unfoldComm (t,t') (tt,tt') m btc ftc
                                  Nothing -> throw $ UnfoldE1 s
habitar (Unfold s (Just h)) = do op <- getUsrOpers
                                 case findIndex (\(x,_,_,_) -> x == s) op of
                                   Just m -> do n <- getTTermVars
                                                i <- maybeToProof UnfoldE2 $ getHypothesisValue n h
                                                c <- getTermContext
                                                let (x,y,t,t') = S.index c (n-i-1)
                                                    (_, (tt,tt'), _, _) = op !! m
                                                btc <- getBTypeContext
                                                ftc <- getFTypeContext
                                                let (r,r') = unfoldComm (t,t') (tt,tt') m btc ftc
                                                updateTermContext (n-i-1) (x,y,r,r')
                                   Nothing -> throw $ UnfoldE1 s
                                   
----------------------------------------------------------------------------------------------------------------------
-- Comando INTRO e INTROS

introComm :: Maybe (Type, TType) -> Proof ()
introComm (Just (Fun t1 t2, TFun t1' t2')) =
  do incrementTVars (+1)
     q <- getTBTypeVars
     tv <- getTVars
     addTermContext (tv,q,t1,t1')
     replaceType (t2, t2')
     modifyTerm $ addHT (\x -> Lam (t1,t1') x)
introComm (Just (ForAll v t, TForAll t')) =
  do incrementTVars (+1)
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
elimComm i (t,t') (RenameTy s [t1,t2], RenameTTy _ [t1',t2'])
  | s == and_text = do replaceType (Fun t1 (Fun t2 t), TFun t1' (TFun t2' t'))
                       modifyTerm $ addHT (\x -> ((Free $ Global "elim_and")
                                                   :!: (t1,t1') :!: (t2,t2') :!: (t,t'))
                                                 :@: (Bound i) :@: x)
  | s == or_text = do modifySubProofs 2 (\tys -> Just (Fun t1 t, TFun t1' t') :
                                          Just (Fun t2 t, TFun t2' t') : tys)
                      modifyTerm $ addDHT (\x y -> ((Free $ Global "elim_or")
                                                     :!: (t1,t1') :!: (t2,t2') :!: (t,t'))
                                                   :@: (Bound i) :@: x :@: y)
  | otherwise = throw ElimE1
elimComm _ _ _ = throw ElimE1

----------------------------------------------------------------------------------------------------------------------
-- Comando APPLY

applyComm :: Int -> (Type, TType) -> (Type, TType) -> Proof ()
applyComm i x ht@(Fun _ _, TFun _ _) = 
  do n <- compareTypes ht x
     modifySubProofs n (\tys -> getTypesFun n ht ++ tys)
     modifyTerm $ getApplyTermFun n i
applyComm i x ht@(ForAll _ _, TForAll _) =
  do let equal = snd ht == snd x
     let (ft, n) = getNestedTypeForAll equal (snd ht)
     r <- eitherToProof $ unification equal n ft x
     let m = n - M.size r
     modifySubProofs m (\tys -> getTypesForAll m tys)
     modifyTerm $ getApplyTermForAll n r (Bound i)
applyComm i (t1, t1') (t, t')
  | t' == t1' = do modifySubProofs 0 id
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


repeatElem :: Int -> a -> [a] -> [a]
repeatElem n x xs
  | n == 0 = xs
  | n > 0 = x : repeatElem (n-1) x xs
  | otherwise = error "error: repeatElem, no debería pasar."

getTypesForAll :: Int -> [Maybe (Type, TType)] -> [Maybe (Type, TType)]
getTypesForAll m tys = repeatElem m Nothing tys
                 

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
-- 2. Tipo (con y sin nombre) que tiene el "cuerpo" del operador foldeado.
-- 3. Código de la operación a "unfoldear".
-- 4. Conjunto de variables de tipos ligadas.
-- 5. Conjunto de variables de tipos libres.
unfoldComm :: (Type, TType) -> (Type, TType) -> Int -> BTypeContext -> FTypeContext -> (Type, TType)
unfoldComm t@(B _, _) _ _ _ _ = t
unfoldComm (RenameTy s ts, RenameTTy m ts') r n btc ftc
  | m == n = applyTypes ftc btc r mapUnfoldComm
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


-- Realiza la sustitución de tipos: (((t [T1]) [T2])..) [Tn].
-- Para ello, hace dos cosas:
-- 1. Renombra todas las variables de tipo ligadas "escapadas" (sin nombres),
-- nos referimos a aquellas variables cuyo cuantificador no figura en el tipo
-- (sin nombre) del 3º arg.
-- 2. Renombra las variables de tipo ligadas (con nombres) del 3º arg., de modo tal que no halla
-- dos var. de tipo ligadas con el mismo nombre, una más anidada que la otra.
-- Argumentos:
-- 1. Conjunto de variables de tipo de libres.
-- 2. Conjunto de variables de tipo ligadas (con nombres), del contexto.
-- 3. Cuerpo del tipo (con nombres y sin nombres), sobre el que se realiza la sust.
-- 4. Tipos T1,..,Tn.
applyTypes :: FTypeContext -> BTypeContext -> (Type, TType) -> [(Type, TType)] -> (Type, TType)
applyTypes _ _ t [] = t
applyTypes fs bs t xs = let l = length xs
                        in applyTypes' l 0 fs [] (foldl (\xs (_,x) -> x : xs )[] bs) (getBodyForAll l t) xs

-- Realiza la sust. de tipos.
-- 1. Cantidad de tipos a reemplazar.
-- 2. Profundidad ("para todos"), procesados.
-- 3. Conjunto de variables de tipo libres.
-- 4. Conjunto de variables de tipo ligadas (con nombres) procesadas.
-- 5. Conjunto de los renombres de las variables de tipo ligadas (con nombres) del 4º arg.
--    Incluye además las var. de tipo ligadas del contexto.
-- 6. Tipo sobre el que se hace la sust. Sin los "para todos" que se van a sustituir.
-- 7. Tipos que se sustituyen.
applyTypes' :: Int -> Int -> FTypeContext -> [String] -> [String]
           -> (Type, TType) -> [(Type, TType)] -> (Type, TType)
applyTypes' l n fs bs rs (B v, TBound m) ts
  | (n <= m) && (m < l) = let (x,y) = ts !! (l - m - 1)
                          in (renameType fs rs x, renameTType n y )
  | otherwise = case findIndex (\x -> x == v) bs of
                  Just i -> (B $ rs !! i, TBound m)
                  Nothing -> error "error: applyTypes', no debería pasar."
applyTypes' _ _ _ _ _ x@(_, TFree f) _ = x
applyTypes' l n fs bs rs (ForAll v t1, TForAll t1') ts =
  let v' = getRename v fs rs
      (tt, tt') = applyTypes' (l+1) (n+1) fs (v:bs) (v':rs) (t1,t1') ts
  in (ForAll v' tt, TForAll tt')
applyTypes' l n fs bs rs (Fun t1 t2, TFun t1' t2') ts =
  let (tt1, tt1') = applyTypes' l n fs bs rs (t1,t1') ts
      (tt2, tt2') = applyTypes' l n fs bs rs (t2,t2') ts
  in (Fun tt1 tt2, TFun tt1' tt2')
applyTypes' l n fs bs rs (RenameTy s xs, RenameTTy op xs') ts =
  let (r, r') = unzip $ map (\x -> applyTypes' l n fs bs rs x ts) $ zip xs xs'
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
renameType :: FTypeContext -> [String] -> Type -> Type
renameType = renameType' []

renameType' :: [String] -> FTypeContext -> [String] -> Type -> Type
renameType' bs fs rs (B v) =
  case v `elemIndex` bs of
    Just i -> B $ rs !! i
    Nothing -> B v
renameType' bs fs rs (ForAll v t) = let v' = getRename v fs rs
                                    in ForAll v' $ renameType' (v:bs) fs (v':rs) t
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
unif _ _ _ _ _ = throw Unif4

-- Función auxiliar de unif. Trata el caso en el tipo a unificar sea una operación "foldeable".
unifRename :: Int -> Int -> M.Map Int (Type,TType) ->
              [TType] -> [Type] -> [TType] -> Either ProofExceptions (M.Map Int (Type,TType))
unifRename pos n sust [] [] [] = return sust
unifRename pos n sust (t:ts) (tt:tts) (tt':tts') =
  do res <- unif pos n sust t (tt, tt')
     unifRename pos n res ts tts tts'

-- Obtiene la substitución, a partir de la profundidad dada por el 1º argumento.
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
-- El 1º arg. son el conj. de proposiciones válidas, y el 2º las operaciones "unfoldeables".
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
      Nothing ->  case getCodeFromOP s op of
                    Just (m, to) -> if checkOperands to ts
                                    then do rs <- sequence $ map (rename' rv bv fv op) ts
                                            let (xs,ys) = unzip rs
                                            return (RenameTy s xs, RenameTTy m ys)
                                    else throw $ OpE1 s
                    Nothing -> throw $ OpE2 s
                    
getCodeFromOP :: String -> FOperations -> Maybe (Int, Operands)
getCodeFromOP = getCodeFromOP' 0

getCodeFromOP' :: Int -> String -> FOperations -> Maybe (Int, Operands)
getCodeFromOP' _ _ [] = Nothing
getCodeFromOP' n x ((y,_,o,_):ys)
  | x == y = return (n,o)
  | otherwise = getCodeFromOP' (n+1) x ys

checkOperands :: Operands -> [a] -> Bool
checkOperands Empty [] = True
checkOperands Unary [_] = True
checkOperands Binary [_,_] = True
checkOperands _ _ = False
  
----------------------------------------------------------------------------------------------------------------------
-- Trasformadores: Se pasa de un lambda término con nombre, al equivalente sin nombre.

-- Genera el lambda término, sin nombre de término ni de tipo.
-- Chequea que las variables de tipo sean válidas de acuerdo al contexto de tipos
-- dado por 3º arg., y que las variables de términos también lo sean, de
-- acuerdo la longitud del contexto de variables de términos "iniciales", dado por el 2º arg.
-- El 1º argumento, es la tabla de operaciones "unfoldeables".
withoutName :: FOperations -> Int -> (FTypeContext, BTypeContext) -> LamTerm -> Either ProofExceptions Term
withoutName = withoutName' []

withoutName' :: [String] -> FOperations -> Int -> (FTypeContext, BTypeContext) -> LamTerm -> Either ProofExceptions Term
withoutName' teb _ n _ (LVar x)
  | n == 0 = case elemIndex x teb of
               Just m -> return $ Bound m
               Nothing -> return $ Free $ Global x
  | n > 0 = case elemIndex x teb of
               Just m -> return $ Bound m
               Nothing -> case getHypothesisValue n x of
                            Just h -> return $ Bound $ n - h - 1
                            Nothing -> return $ Free $ Global x
  | otherwise = error "error: withoutName', no debería pasar."
withoutName' teb op n tyc (Abs x t e) = do t' <- typeWhitoutName op tyc t
                                           e' <- withoutName' (x:teb) op n tyc e
                                           return $ Lam (t, t') e'
withoutName' teb op n tyc (App e1 e2) = do e1' <- withoutName' teb op n tyc e1
                                           e2' <- withoutName' teb op n tyc e2
                                           return $ e1' :@: e2'
withoutName' teb op n (ftyc,btyc) (BAbs x e) = do e' <- withoutName' teb op n (ftyc, (0,x) S.<| btyc) e
                                                  return $ BLam x e'
withoutName' teb op n tyc (BApp e t) = do e' <- withoutName' teb op n tyc e
                                          t' <- typeWhitoutName op tyc t
                                          return $ e' :!: (t,t')


typeWhitoutName :: FOperations -> (FTypeContext, BTypeContext) -> Type -> Either ProofExceptions TType
typeWhitoutName _ (ftyc,btyc) (B x) = case S.findIndexL (\y-> snd y == x) btyc of
                                        Just n -> return $ TBound n
                                        Nothing -> if elem x ftyc
                                                   then return $ TFree x
                                                   else throw $ TermE x
typeWhitoutName op (ftyc,btyc) (ForAll x t) = do r <- typeWhitoutName op (ftyc, (0,x) S.<| btyc) t
                                                 return $ TForAll r
typeWhitoutName op tyc (Fun t1 t2) = do r1 <- typeWhitoutName op tyc t1
                                        r2 <- typeWhitoutName op tyc t2
                                        return $ TFun r1 r2
typeWhitoutName op tyc (RenameTy s ts) =
  case find (\(x,_,_) -> x == s) notFoldeableOps of
    Just (_,n,to) -> if checkOperands to ts
                     then do rs <- sequence $ map (typeWhitoutName op tyc) ts
                             return $ RenameTTy n rs
                     else throw $ OpE1 s
    Nothing -> case getCodeFromOP s op of
                 Just (m,to) -> if checkOperands to ts
                                then do rs <- sequence $ map (typeWhitoutName op tyc) ts
                                        return $ RenameTTy m rs
                                else throw $ OpE1 s
                 Nothing -> throw $ OpE2 s
                 
----------------------------------------------------------------------------------------------------------------------
-- Algoritmo de inferencia de tipos de un lambda término.

-- Infiere el tipo sin nombre de un lambda término, de acuerdo a la
-- lista de teoremas dada por el 3º arg.
-- Suponemos que ninguna de las pruebas de los teoremas son recursivas.
-- Es decir, que su lambda término es recursivo.
-- El 1º arg. indica la profundidad (respecto al cuantificador "para todo")
-- desde la que se quiere inferir.
-- El 2º arg. es el contexto de variables de términos, desde el que se quiere inferir.
inferType :: Int -> TermContext -> Teorems -> Term -> Either ProofExceptions (Type, TType)
inferType n _ te (Free (Global x)) =
  case M.lookup x te of
    Just (_,t) -> return t
    Nothing -> throw $ InferE1 x -- NO puede haber variables de términos libres que no sean teoremas.
inferType n c te (Bound x) = let (_,m,t,t') = S.index c x
                             in return (t,renameTType (n-m) t')
inferType n c te (Lam (t,t') x) = do (tt,tt') <- inferType n ((0,n,t,t') S.<| c) te x
                                     return (Fun t tt, TFun t' tt')
inferType n c te (x :@: y) = do (tt1, tt1') <- inferType n c te x
                                case (tt1, tt1') of
                                  (Fun _ t2, TFun t1' t2') ->
                                    do (tt2, tt2') <- inferType n c te y
                                       if tt2' == t1'
                                         then return (t2, t2')
                                         else throw $ InferE2 tt2
                                  _ -> throw $ InferE3 tt1
inferType n c te (BLam v x) = do (t,t') <- inferType (n+1) c te x
                                 return (ForAll v t, TForAll t')
inferType n c te (x :!: (t,t')) = do (tt,tt') <- inferType n c te x
                                     case (tt, tt') of
                                       (ForAll _ t1, TForAll t1') ->
                                         return $ inferReplaceType (t1,t1') (t,t')
                                       _ -> throw $ InferE4 tt

-- Renombra todas las variables de tipo ligadas "escapadas", nos referimos a aquellas
-- variables cuyo cuantificador en el tipo del 2º arg.
renameTType :: Int -> TType -> TType
renameTType 0 = id
renameTType n = renameTType' 0 n

renameTType' :: Int -> Int -> TType -> TType
renameTType' n r t@(TBound x)
  | x < n = t
  | otherwise = TBound (x+r)
renameTType' _ _ t@(TFree x) = t
renameTType' n r (TForAll t) = TForAll $ renameTType' (n+1) r t
renameTType' n r (TFun t1 t2) = TFun (renameTType' n r t1) (renameTType' n r t2)
renameTType' n r (RenameTTy op ts) = RenameTTy op $ map (renameTType' n r) ts
-- renameTType' n r (TExists t) = TExists $ renameTType' (n+1) r t

-- Consideramos que el 1º argumento corresponde al cuerpo de un "para todo".
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
-- Además, chequea que el valor sea válidos.
getHypothesisValue :: Int -> String -> Maybe Int
getHypothesisValue n h
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
