module Asistente where

import Common
import Data.Char (isDigit)
import Data.List (findIndex, elemIndex, find)
import Control.Monad (unless, when)
import qualified Data.Map as M (Map, lookup, insert, empty, size)
import qualified Data.Sequence as S
import Data.Maybe (fromJust, isJust)
import ProofState

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
                      elimComm i (t,t') (getTypeVar q $ S.index c (n-i-1))
habitar CLeft = do x <- getType
                   case x of
                     Just (RenameTy s [t1,t2] , RenameTTy _ [t1',t2']) ->
                       if s == or_text
                          then do replaceType (t1,t1')
                                  modifyTerm $ addHT (\x -> ((Free $ Global "intro_or1")
                                                             :!: (t1,t1') :!: (t2,t2'))
                                                            :@: x)
                       else throw CommandInvalid
                     _ -> throw CommandInvalid
habitar CRight = do x <- getType
                    case x of
                      Just (RenameTy s [t1,t2] , RenameTTy _ [t1',t2']) ->
                        if s == or_text
                        then do replaceType (t2,t2')
                                modifyTerm $ addHT (\x -> ((Free $ Global "intro_or2")
                                                           :!: (t1,t1') :!: (t2,t2'))
                                                          :@: x)
                        else throw CommandInvalid
                      _ -> throw CommandInvalid
habitar Split = do x <- getType
                   case x of
                     Just (RenameTy s [t1,t2], RenameTTy _ [t1',t2']) ->
                       if s == and_text
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
-- habitar (PState {name=name,
--                  subp=p,
--                  position=n:ns,
--                  typeContext=tc:tcs,
--                  context=c:cs,
--                  tyFromCut = cut,
--                  ty=Nothing:tys,
--                  term=ts}) (Exact x) =
--   return $ PState {name=name,
--                    subp=p-1,
--                    position=ns,
--                    typeContext=tcs,
--                    context=cs,
--                    tyFromCut = cut,
--                    ty=tys,
--                    term= simplifyTypeInTerm (x,x') ts}
--   where x' = typeWithoutName x
-- habitar (PState {ty=Just _ : tys}) (Exact x) = throw ExactE



-- habitar (CExists x) = do y <- getType
--                          case y of
--                            Just (Exists q t, TExists t') ->
--                              do tc <- getTypeContext
--                                 (y,y') <- eitherToProof $ getRenameWhitException tc x
--                                 let (z,z') = replace (t,t') (y,y')
--                                 r <- eitherToProof $ getRenameTypeWhitException tc z
--                                 replaceType (r,z')
--                                 modifyTerm $ addHT (\x -> (Free $ Global "intro_exists") :@: x)
--                            _ -> throw CommandInvalid

-- habitar (PState {name=name,
--                  subp=p,
--                  position=n:ns,
--                  typeContext=tc:tcs,
--                  context=c:cs,
--                  tyFromCut = cut,
--                  ty=Just (t, t'):tys,
--                  term=ts}) (Cut x) =
--   return $ PState {name=name,
--                    subp=p+1,
--                    position=n:n:ns,
--                    typeContext=tc:tc:tcs,
--                    context=c:c:cs,
--                    tyFromCut = x:cut,
--                    ty=Just (x,x') : Just (Fun x t,TFun x' t') : tys,
--                    term=addDHT (\x y -> y :@: x) ts}
--   where x' = typeWithoutName x


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

-- elimComm i (t,t') (Exists v t1, TExists t1') =
--   do tc <- getTypeContext
--      let tt = tyExists tc v t1 t
--      replaceType (tt, TForAll $ TFun t1' t')
--      modifyTerm $ addHT (\x -> (elim_exists (Exists v t1, TExists t1') (tt, TForAll $ TFun t1' t'))
--                                :@: (Bound i) :@: x)

-- -- Funciones auxiliares para la función elimComm

-- -- Genera el tipo correspondiente a la eliminación del existe.
-- tyExists :: TypeContext -> String -> Type -> Type -> Type
-- tyExists fv v t1 t2 = let v' = getNewVar fv (getBoundsList t1) (getBoundsList t2) v
--                       in ForAll v' $ Fun (replaceBound v v' t1) t2

-- -- Reemplaza una variable de tipo por otra, sobre un tipo donde los conjuntos de variables de tipo
-- -- ligadas y libres, son disjuntos.
-- replaceBound :: String -> String -> Type -> Type
-- replaceBound v v' (B n)
--   | n == v = B v'
--   | otherwise = B n
-- replaceBound v v' (Fun t1 t2) = Fun (replaceBound v v' t1) (replaceBound v v' t2)
-- replaceBound v v' (And t1 t2) = And (replaceBound v v' t1) (replaceBound v v' t2)
-- replaceBound v v' (Or t1 t2) = Or (replaceBound v v' t1) (replaceBound v v' t2)
-- replaceBound v v' (ForAll x t) = ForAll x $ replaceBound v v' t
-- replaceBound v v' (Exists x t) = Exists x $ replaceBound v v' t

-- -- Retorna una variable de tipo que no está en ninguno de los contextos de tipos, dados
-- -- en los argumentos de la función.
-- -- Sabemos que v no aparece en "bv1", ni en "fv".
-- getNewVar :: TypeContext -> TypeContext -> TypeContext -> String -> String
-- getNewVar fv bv1 bv2 v
--   | elem v bv2 = getNewVar fv bv2 bv1 (newVar v bv2 fv)
--   | otherwise = v
    
-- getBoundsList :: Type -> TypeContext
-- getBoundsList (ForAll v t) = v : getBoundsList t
-- getBoundsList (Exists v t) = v : getBoundsList t
-- getBoundsList (B _) = []
-- getBoundsList (And t1 t2) = getBoundsList t1 ++ getBoundsList t2
-- getBoundsList (Or t1 t2) = getBoundsList t1 ++ getBoundsList t2
-- getBoundsList (Fun t1 t2) = getBoundsList t1 ++ getBoundsList t2

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

-- Retorna el tipo más anidado de una "función", junto con la cantidad de tipos anidados.
-- getNestedTypeFun :: (Type, TType) -> ((Type, TType), Int)
-- getNestedTypeFun (Fun _ y, TFun _ y') = let (f, n) = getNestedTypeFun (y,y')
--                                         in (f, n+1)
-- getNestedTypeFun x = (x, 0)

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
-- -- Comando EXISTS

-- -- Funciones auxiliares

-- -- Igual a la función getRenameWhitException, solo que no retorna el tipo en
-- -- notación de brujin.
-- getRenameTypeWhitException :: [String] -> Type -> Either ProofExceptions Type
-- getRenameTypeWhitException fv t =
--   case renameType fv t of
--     Left s -> Left $ PropNotExists s
--     Right x -> Right x


-- renameType :: [String] -> Type -> Either String Type
-- renameType fv = renameType' fv [] []

-- renameType' :: [String] -> [String] -> [String] -> Type -> Either String Type
-- renameType' fv rv bv (B v) =
--   case v `elemIndex` bv of
--     Just i -> return $ B $ rv!!i
--     Nothing -> if elem v fv
--                then return $ B v
--                else Left v
-- renameType' fv rv bv (ForAll v t) = do let v' = getRename v fv rv
--                                        x <- renameType' fv (v':rv) (v:bv) t
--                                        return $ ForAll v' x
-- renameType' fv rv bv (Exists v t) = do let v' = getRename v fv rv
--                                        x <- renameType' fv (v':rv) (v:bv) t
--                                        return $ Exists v' x
-- renameType' fv rv bv (Fun t t') = do x <- renameType' fv rv bv t
--                                      x' <- renameType' fv rv bv t'
--                                      return $ Fun x x'
-- renameType' fv rv bv (And t t') = do x <- renameType' fv rv bv t
--                                      x' <- renameType' fv rv bv t'
--                                      return $ And x x'
-- renameType' fv rv bv (Or t t') = do x <- renameType' fv rv bv t
--                                     x' <- renameType' fv rv bv t'
--                                     return $ Or x x'


-- replace :: (Type,TType) -> (Type,TType) -> (Type,TType)
-- replace = replace' 0

-- replace' :: Int -> (Type,TType) -> (Type,TType) -> (Type,TType)
-- replace' n t@(x,TBound v) r
--   | n == v = r
--   | otherwise = t
-- replace' n t@(x,TFree v) _ = t
-- replace' n (Fun t1 t2, TFun t1' t2') r = let (x,x')= replace' n (t1,t1') r
--                                              (y,y')= replace' n (t2,t2') r
--                                          in (Fun x y, TFun x' y')
-- replace' n (Exists v t, TExists t') r = let (x,x') = replace' (n+1) (t,t') r          
--                                         in (Exists v x, TExists x')
-- replace' n (ForAll v t, TForAll t') r = let (x,x') = replace' (n+1) (t,t') r          
--                                         in (ForAll v x, TForAll x')
-- replace' n (And t1 t2, TAnd t1' t2') r = let (x,x')= replace' n (t1,t1') r
--                                              (y,y')= replace' n (t2,t2') r
--                                          in (And x y, TAnd x' y')
-- replace' n (Or t1 t2, TOr t1' t2') r = let (x,x')= replace' n (t1,t1') r
--                                            (y,y')= replace' n (t2,t2') r
--                                        in (Or x y, TOr x' y')
-- replace' _ _ _ = error "error: replace' no debería pasar."

----------------------------------------------------------------------------------------------------------------------

--ARREGLAR
-- intro_exists :: TType -> TType -> (Type, TType) -> Term
-- intro_exists s_a0 s a0 = Lam s_a0 $ BLam $ Lam (TForAll $ TFun s (TBound 1)) $ (Bound 0 :!: a0) :@: (Bound 1)      

--ESTA MAL
-- elim_exists :: (Type, TType) -> (Type, TType) -> Term
-- elim_exists (s,s') x@(ForAll _ (Fun _ t), TForAll (TFun _ t'))
--   = Lam (s, s') $ Lam x $ (Bound 1 :!: (t, t')) :@: (Bound 0)

-- elim_exists :: TType -> (Type, TType) -> Term
-- elim_exists s (b, b') = Lam (TExists s) $ Lam (TForAll $ TFun s b') $ (Bound 1 :!: (b, b')) :@: (Bound 0)


-- En el término utilizo TFree "a" en lugar de TBound 0, para que la impresión en
-- patalla quede bien.
-- intro_and :: (Type, TType) -> (Type, TType) -> Term
-- intro_and x@(x1, x2) y@(y1, y2) =
--   Lam x $ Lam y $
--   BLam "a" $ Lam (Fun x1 $ Fun y1 (B "a"), TFun x2 $ TFun y2 (TFree "a")) (((Bound 0) :@: (Bound 2)) :@: (Bound 1))

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

-- elim_and1 :: Term
-- elim_and1 =
--   BLam "a" $ BLam "b" $ Lam (And (B "a") (B "b"), TAnd (TBound 1) (TBound 0)) $
--   (Bound 0 :!: (B "a", TBound 1)) :@: (Lam (B "a", TBound 1) $ Lam (B "b", TBound 0) $ Bound 1)  

-- elim_and2 :: Term
-- elim_and2 =
--   BLam "a" $ BLam "b" $ Lam (And (B "a") (B "b"), TAnd (TBound 1) (TBound 0)) $
--   (Bound 0 :!: (B "b", TBound 0)) :@: (Lam (B "a", TBound 1) $ Lam (B "b", TBound 0) $ Bound 0)  

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

--------------------------------------------------------------------

-- typeWithoutName :: Type -> TType
-- typeWithoutName = typeWithoutName' []

-- typeWithoutName' :: [String] -> Type -> TType
-- typeWithoutName' xs (B t) = maybe (TFree t) TBound (t `elemIndex` xs)
-- typeWithoutName' xs (Fun t t') = TFun (typeWithoutName' xs t) (typeWithoutName' xs t')
-- typeWithoutName' xs (ForAll v t) = TForAll $ typeWithoutName' (v:xs) t
-- -- typeWithoutName' xs (Exists v t) = TExists $ typeWithoutName' (v:xs) t
-- typeWithoutName' xs (And t t') = TAnd (typeWithoutName' xs t) (typeWithoutName' xs t')
-- typeWithoutName' xs (Or t t') = TOr (typeWithoutName' xs t) (typeWithoutName' xs t')


unification :: Bool -> Int -> TType -> (Type,TType) ->
  Either ProofExceptions (M.Map Int (Type,TType))
unification True _ = \ _ _ -> return M.empty
unification False n = unif 0 n M.empty

--TERMINAR
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
  | otherwise = if TBound (i-1) == tt2
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
-- unif pos n sust (TExists t') (Exists _ tt, TExists tt') = unif (pos+1) (n+1) sust t' (tt,tt')

-- Función auxiliar de unif. Trata el caso en el tipo a unificar sea una operación "custom".
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
-- substitution' m n (Exists v t, TExists t') = do (x,x') <- substitution' (m+1) (n+1) (t,t')
--                                                 return (Exists v x, TExists x')

----------------------------------------------------------------------------------------------------------------------
-- Renombramiento

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
-- El 1º arg. son el conj. de proposiciones válidas, y el 2º las operaciones "custom".
rename :: FTypeContext -> UserOperations -> Type -> Either ProofExceptions (Type, TType)
rename = rename' [] []

rename' :: [String] -> [String] -> FTypeContext -> UserOperations -> Type -> Either ProofExceptions (Type, TType)
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
    case find (\(x,_,_,_) -> x == s) defaults_op of
      Just (_,n,_,_) -> do rs <- sequence $ map (rename' rv bv fv op) ts
                           let (xs,ys) = unzip rs
                           return (RenameTy s xs, RenameTTy n ys)
      Nothing ->  case findIndex (\(x,_,_) -> x == s) op of
                    Just m -> do rs <- sequence $ map (rename' rv bv fv op) ts
                                 let (xs,ys) = unzip rs
                                 return (RenameTy s xs, RenameTTy m ys)
                    Nothing -> throw $ OpE s
  
--------------------------------------------------------------------

-- Genera el lambda término, sin nombre de término ni de tipo.
-- Chequea que las variables de tipo sean válidas de acuerdo al contexto de tipos
-- dado por 3º arg., y que las variables de términos también lo sean, de
-- acuerdo la longitud del contexto de variables de términos "iniciales", dado por el 2º arg.
-- El 1º argumento, es la tabla de operaciones "custom".
withoutName :: UserOperations -> Int -> (FTypeContext, BTypeContext) -> LamTerm -> Either ProofExceptions Term
withoutName = withoutName' []

withoutName' :: [String] -> UserOperations -> Int -> (FTypeContext, BTypeContext) -> LamTerm -> Either ProofExceptions Term
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


typeWhitoutName :: UserOperations -> (FTypeContext, BTypeContext) -> Type -> Either ProofExceptions TType
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
  case find (\(x,_,_,_) -> x == s) defaults_op of
    Just (_,n,_,_) -> do rs <- sequence $ map (typeWhitoutName op tyc) ts
                         return $ RenameTTy n rs
    Nothing -> case findIndex (\(x,_,_) -> x == s) op of
                 Just m -> do rs <- sequence $ map (typeWhitoutName op tyc) ts
                              return $ RenameTTy m rs
                 Nothing -> throw $ OpE s


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
-- variables cuyo cuantificador no figura en el lambda término (el 2º arg.)
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
-- inferReplaceType' n (Exists v t1, TExists t1') t = let (tt, tt') = inferReplaceType' (n+1) (t1,t1') t
--                                                    in (Exists v tt, TExists tt')


-- Obtiene el tipo de la variable de término, renombrando su tipo sin nombres, de acuerdo
-- a la profundidad dada por el 1º argumento.
getTypeVar :: Int -> TermVar -> (Type, TType)
getTypeVar n (_,m, t, t') = (t, renameTType (n-m) t')

--------------------------------------------------------------------
-- Comando: Definition de nuevos operadores

getRenamedOperation :: FTypeContext -> UserOperations -> BodyOperation
                    -> Either ProofExceptions (TypeOperands, TTypeOperands)
getRenamedOperation fv op (BEmpty t) = do (tt,tt') <- rename fv op t
                                          return (Empty tt, Empty tt')
getRenamedOperation fv op (BUnary v t) = do tt <- getRenameOp False [] [] fv op [v] t
                                            return $ getRenamedOpUnary tt
getRenamedOperation fv op (BBinary v1 v2 t) = do tt <- getRenameOp True [] [] fv op [v1,v2] t
                                                 return $ getRenamedOpBinary tt
                                                 
-- Función auxiliar.
getRenamedOpUnary :: (TypeOperands, TTypeOperands, Maybe PositionOp) -> (TypeOperands, TTypeOperands)
getRenamedOpUnary (Empty t, Empty t', Nothing) =
  (Unary $ \w -> t, Unary $ \w -> t')
getRenamedOpUnary (Unary t, Unary t', Nothing) =
  (Unary t, Unary t')
getRenamedOpUnary _ = error "error: getRenamedOpBinary, no debería pasar."

-- Función auxiliar.
getRenamedOpBinary :: (TypeOperands, TTypeOperands, Maybe PositionOp) -> (TypeOperands, TTypeOperands)
getRenamedOpBinary (Unary t, Unary t', Just OpLeft) =
  (Binary $ \w1 w2 -> t w1, Binary $ \w1 w2 -> t' w1)
getRenamedOpBinary (Unary t, Unary t', Just OpRight) =
  (Binary $ \w1 w2 -> t w2, Binary $ \w1 w2 -> t' w2)
getRenamedOpBinary (Empty t, Empty t', Nothing) =
  (Binary $ \w1 w2 -> t, Binary $ \w1 w2 -> t')
getRenamedOpBinary (Binary t, Binary t', Nothing) =
  (Binary t, Binary t')
getRenamedOpBinary _ = error "error: getRenamedOpBinary, no debería pasar."

-- Es útil para saber a cual de los operandos le corresponde el aujero
-- en su body, cuando la operación es binaria.
data PositionOp = OpLeft | OpRight
                deriving (Show, Eq)

getRenameOp :: Bool -> [String] -> [String] -> FTypeContext -> UserOperations -> [Var] -> Type ->
  Either ProofExceptions (TypeOperands, TTypeOperands, Maybe PositionOp)
getRenameOp bin rv bv fv _ vs (B x) =
    case x `elemIndex` bv of
    Just i -> return (Empty $ B $ rv!!i, Empty $ TBound i, Nothing)
    Nothing -> case x `elemIndex` vs of
                    Just j -> return (Unary id, Unary id, getPosOp bin j)
                    Nothing -> if elem x fv
                               then return (Empty $ B x, Empty $ TFree x, Nothing)
                               else throw $ PropNotExists x
getRenameOp bin rv bv fv op vs (ForAll v t) =
  do let v' = getRename v fv rv
     (f,g,pos) <- getRenameOp bin (v':rv) (v:bv) fv op vs t
     return (simplifyOp1 (\w-> ForAll v w) f, simplifyOp1 (\w -> TForAll w) g, pos)
getRenameOp bin rv bv fv op vs (Fun t t') =
  do (f1, g1, pos1) <- getRenameOp bin rv bv fv op vs t
     (f2, g2, pos2) <- getRenameOp bin rv bv fv op vs t'
     let (x,y) = simplifyOp2 (\w1 w2 -> Fun w1 w2) (f1,pos1) (f2,pos2)
         (x',y') = simplifyOp2 (\w1 w2 -> TFun w1 w2) (g1,pos1) (g2,pos2)
     if y == y'
       then return (x, x', y)
       else error "error: getRenameOp, no debería pasar."
getRenameOp bin rv bv fv op vs (RenameTy s ts) =
  case find (\(x,_,_,_) -> x == s) defaults_op of
    Just (_,n,_,_) -> do rs <- sequence $ map (getRenameOp bin rv bv fv op vs) ts
                         let (xs,ys,zs) = unzip3 rs
                             (r1,r1') = simplifyOp3 (RenameTy s) (xs,zs)
                             (r2,r2') = simplifyOp3 (RenameTTy n) (ys,zs)
                         return (r1, r2, r1')
    _ -> case findIndex (\(x,_,_) -> x == s) op of
           Just m -> do rs <- sequence $ map (getRenameOp bin rv bv fv op vs) ts
                        let (xs,ys,zs) = unzip3 rs
                            (r1,r1') = simplifyOp3 (RenameTy s) (xs,zs)
                            (r2,r2') = simplifyOp3 (RenameTTy m) (ys,zs)
                        return (r1, r2, r1')
           Nothing -> throw $ OpE s

-- Función auxiliar de "getRenameOp". Indica cual de los operandos se
-- utilizo en el "aujereo", si la operación es binaria.
getPosOp :: Bool -> Int -> Maybe PositionOp
getPosOp False _ = Nothing
getPosOp True 0 = Just OpLeft
getPosOp True 1 = Just OpRight
getPosOp _ _ = error "error: getPosOp, no debería pasar."

-- Operaciones auxiliares para "getRenameOp". Simplifican los operandos.
simplifyOp1 :: (a -> a) -> Operands a -> Operands a
simplifyOp1 f (Empty t) = Empty $ f t
simplifyOp1 f (Unary g) = Unary $ f . g
simplifyOp1 f (Binary g) = Binary $ \ w1 w2 -> f (g w1 w2)

simplifyOp2 :: (a -> a -> a) -> (Operands a, Maybe PositionOp)
            -> (Operands a, Maybe PositionOp) -> (Operands a, Maybe PositionOp)
simplifyOp2 f (Empty t1, Nothing) (Empty t2, Nothing) = (Empty $ f t1 t2, Nothing)
simplifyOp2 f (Empty t1, Nothing) (Unary t2, p2) = (Unary $ (f t1) . t2, p2)
simplifyOp2 f (Empty t1, Nothing) (Binary t2, Nothing) =
  (Binary $ \w1 w2 -> (f t1) (t2 w1 w2), Nothing)
simplifyOp2 f (Unary t1, p1) (Empty t2, Nothing) = (Unary $ \w -> f (t1 w) t2, p1)
simplifyOp2 f (Binary t1, Nothing) (Empty t2, Nothing) =
  (Binary $ \w1 w2 -> f (t1 w1 w2) t2, Nothing)
simplifyOp2 f (Unary t1, po1) (Unary t2, po2)
  | po1 == po2 = (Unary $ \w -> f (t1 w) (t2 w), po1)
  | (po1 == Just OpLeft) && (po2 == Just OpRight) = (Binary $ \w1 w2 -> f (t1 w1) (t2 w2), Nothing)
  | (po1 == Just OpRight) && (po2 == Just OpLeft) = (Binary $ \w1 w2 -> f (t1 w2) (t2 w1), Nothing)
simplifyOp2 f (Unary t1, Just po1) (Binary t2, Nothing)
  | po1 == OpLeft = (Binary $ \w1 w2 -> f (t1 w1) (t2 w1 w2), Nothing)
  | po1 == OpRight = (Binary $ \w1 w2 -> f (t1 w2) (t2 w1 w2), Nothing)
simplifyOp2 f (Binary t1, Nothing) (Unary t2, Just po2)
  | po2 == OpLeft = (Binary $ \w1 w2 -> f (t1 w1 w2) (t2 w1), Nothing)
  | po2 == OpRight = (Binary $ \w1 w2 -> f (t1 w1 w2) (t2 w2), Nothing)
simplifyOp2  _ _ _ = error "error: simplifyOp2, no debería pasar."

-- ARREGLAR:
-- Definition algo x := (x /\  (forall w, w)) -> x.

-- Función auxiliar de "getRenameOp".
simplifyOp3 :: ([a] -> a) -> ([Operands a],[Maybe PositionOp]) -> (Operands a, Maybe PositionOp)
simplifyOp3 c ([],[]) = (Empty $ c [], Nothing)
simplifyOp3 c ([f],[p]) = (simplifyOp1 (\w -> c [w]) f, p)
simplifyOp3 c ([f,g], [p1,p2]) = simplifyOp2 (\w1 w2 -> c [w1, w2]) (f,p1) (f,p2)
simplifyOp3 _ _ = error "error: simplifyOp3, no debería pasar."

--------------------------------------------------------------------

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


-- Evaluador
-- eval :: Term -> Value
-- eval ((Lam ty t) :@: t2)
--   | isValue t2 = replaceTerm t t2
--   | otherwise = (Lam ty t) :@: (eval t2)
-- eval (t1 :@: t2)
--   | isValue t1 = t1 :@: (eval t2)
--   | otherwise = eval t1 :@: t2
-- eval ((BLam v t) :!: ty) = replaceType t ty
-- eval (t1 :!: ty) = eval t1 :!: ty
-- eval (Lam ty t) = VLam ty t
-- eval (BLam v t) = VBLam v t
-- eval _ = error "error: eval, no debería pasar."

-- isValue :: Term -> Bool
-- isValue (BLam _ _) = True
-- isValue (Lam _ _) = True
-- isValue _ = False
