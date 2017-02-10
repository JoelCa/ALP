module Asistente where

import Common
import Data.Char (isDigit)
import Data.List (findIndex, elemIndex)
import Control.Monad (unless)
import qualified Data.Map as M (Map, lookup, insert, empty, size)
import Data.Maybe (fromJust)
import ProofState

habitar :: Tactic -> Proof ()
habitar Assumption = do x <- getType
                        (_,tw) <- maybeToProof EmptyType x 
                        c <- getContext
                        q <- getQuantifier
                        i <- maybeToProof AssuE (findIndex
                                                  (\(p,_,t) -> renameTType (q - p) t == tw)
                                                  c)
                        modifySubProofs 0 id
                        modifyTerm $ simplify (Bound i)
habitar Intro = do x <- getType
                   introComm x
habitar Intros = introsComm
habitar (Apply h) = do x <- getType
                       (t,t') <- maybeToProof EmptyType x
                       n <- getPosition
                       i <- getHypothesisValue n h
                       c <- getContext
                       q <- getQuantifier
                       applyComm (n-i-1) (t,t') (getTypeVar q $ c !! (n-i-1))
habitar (Elim h) = do x <- getType
                      (t,t') <- maybeToProof EmptyType x
                      n <- getPosition
                      i <- getHypothesisValue n h
                      c <- getContext
                      q <- getQuantifier
                      elimComm i (t,t') (getTypeVar q $ c !! (n-i-1))
--CHEQUEAR lambda términos
habitar CLeft = do x <- getType
                   case x of
                     Just (Or t1 t2 , TOr t1' t2') ->
                       do replaceType (t1,t1')
                          modifyTerm $ addHT (\x -> ((Free $ Global "intro_or1")
                                                      :!: (t1,t1') :!: (t2,t2'))
                                                    :@: x)
                     _ -> throw CommandInvalid
habitar CRight = do x <- getType
                    case x of
                      Just (Or t1 t2 , TOr t1' t2') ->
                        do replaceType (t2,t2')
                           modifyTerm $ addHT (\x -> ((Free $ Global "intro_or2")
                                                       :!: (t1,t1') :!: (t2,t2'))
                                                     :@: x)
                      _ -> throw CommandInvalid
habitar Split = do x <- getType
                   case x of
                     Just (And t1 t2, TAnd t1' t2') ->
                       do modifySubProofs 2 (\tys -> Just (t1,t1') : Just (t2,t2') : tys)
                          modifyTerm $ addDHT (\x y -> ((Free $ Global "intro_and")
                                                         :!: (t1,t1') :!: (t2,t2'))
                                                       :@: x :@: y)
                     _ -> throw CommandInvalid
habitar (CExists x) = do y <- getType
                         case y of
                           Just (Exists q t, TExists t') ->
                             do tc <- getTypeContext
                                (y,y') <- eitherToProof $ getRenameWhitException tc x
                                let (z,z') = replace (t,t') (y,y')
                                r <- eitherToProof $ getRenameTypeWhitException tc z
                                replaceType (r,z')
                                modifyTerm $ addHT (\x -> (Free $ Global "intro_exists") :@: x)
                           _ -> throw CommandInvalid

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
-- --Modificar Exact
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


----------------------------------------------------------------------------------------------------------------------
-- Comando INTRO e INTROS

introComm :: Maybe (Type, TType) -> Proof ()
introComm (Just (Fun t1 t2, TFun t1' t2')) =
  do incrementPosition (+1)
     q <- getQuantifier
     addContext (q,t1,t1')
     replaceType (t2, t2')
     modifyTerm $ addHT (\x -> Lam (t1,t1') x)
introComm (Just (ForAll v t, TForAll t')) =
  do addTypeContext v
     incrementQuantifier (+1)
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

-- Función auxiliar para el comando intro, con "para todo".
renameBounds :: String -> TType -> TType
renameBounds = renameBounds' 0

renameBounds' :: Int -> String -> TType -> TType
renameBounds' n v t@(TBound x)
  | n == x = TFree v
  | otherwise = t
renameBounds' n v (TFun x y) = TFun (renameBounds' n v x) (renameBounds' n v y)
renameBounds' n v (TForAll x) = TForAll $ renameBounds' (n+1) v x
renameBounds' n v (TExists x) = TExists $ renameBounds' (n+1) v x
renameBounds' n v (TAnd x y) = TAnd (renameBounds' n v x) (renameBounds' n v y)
renameBounds' n v (TOr x y) = TOr (renameBounds' n v x) (renameBounds' n v y)
renameBounds' n v t@(TFree x) = t


----------------------------------------------------------------------------------------------------------------------
-- Comando ELIM

--CHEQUEAR lambda términos
-- Asumimos que las tuplas del 2º arg. , tienen la forma correcta.
elimComm :: Int -> (Type, TType) -> (Type, TType) -> Proof ()
elimComm i (t,t') (And t1 t2, TAnd t1' t2') =
  do replaceType (Fun t1 (Fun t2 t), TFun t1' (TFun t2' t'))
     modifyTerm $ addHT (\x -> ((Free $ Global "elim_and")
                                 :!: (t1,t1') :!: (t2,t2') :!: (t,t'))
                               :@: (Bound i) :@: x)
elimComm i (t,t') (Or t1 t2, TOr t1' t2') =
  do modifySubProofs 2 (\tys -> Just (Fun t1 t, TFun t1' t') :
                         Just (Fun t2 t, TFun t2' t') : tys)
     modifyTerm $ addDHT (\x y -> ((Free $ Global "elim_or")
                                    :!: (t1,t1') :!: (t2,t2') :!: (t,t'))
                                  :@: (Bound i) :@: x :@: y)
elimComm i (t,t') (Exists v t1, TExists t1') =
  do tc <- getTypeContext
     let tt = tyExists tc v t1 t
     replaceType (tt, TForAll $ TFun t1' t')
     modifyTerm $ addHT (\x -> (elim_exists (Exists v t1, TExists t1') (tt, TForAll $ TFun t1' t'))
                               :@: (Bound i) :@: x)
elimComm _ _ _ = throw ElimE1


-- Funciones auxiliares para la función elimComm

-- Genera el tipo correspondiente a la eliminación del existe.
tyExists :: TypeContext -> String -> Type -> Type -> Type
tyExists fv v t1 t2 = let v' = getNewVar fv (getBoundsList t1) (getBoundsList t2) v
                      in ForAll v' $ Fun (replaceBound v v' t1) t2

-- Reemplaza una variable de tipo por otra, sobre un tipo donde los conjuntos de variables de tipo
-- ligadas y libres, son disjuntos.
replaceBound :: String -> String -> Type -> Type
replaceBound v v' (B n)
  | n == v = B v'
  | otherwise = B n
replaceBound v v' (Fun t1 t2) = Fun (replaceBound v v' t1) (replaceBound v v' t2)
replaceBound v v' (And t1 t2) = And (replaceBound v v' t1) (replaceBound v v' t2)
replaceBound v v' (Or t1 t2) = Or (replaceBound v v' t1) (replaceBound v v' t2)
replaceBound v v' (ForAll x t) = ForAll x $ replaceBound v v' t
replaceBound v v' (Exists x t) = Exists x $ replaceBound v v' t

-- Retorna una variable de tipo que no está en ninguno de los contextos de tipos, dados
-- en los argumentos de la función.
-- Sabemos que v no aparece en "bv1", ni en "fv".
getNewVar :: TypeContext -> TypeContext -> TypeContext -> String -> String
getNewVar fv bv1 bv2 v
  | elem v bv2 = getNewVar fv bv2 bv1 (newVar v bv2 fv)
  | otherwise = v
    
getBoundsList :: Type -> TypeContext
getBoundsList (ForAll v t) = v : getBoundsList t
getBoundsList (Exists v t) = v : getBoundsList t
getBoundsList (B _) = []
getBoundsList (And t1 t2) = getBoundsList t1 ++ getBoundsList t2
getBoundsList (Or t1 t2) = getBoundsList t1 ++ getBoundsList t2
getBoundsList (Fun t1 t2) = getBoundsList t1 ++ getBoundsList t2

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
-- Comando EXISTS

-- Funciones auxiliares

-- Igual a la función getRenameWhitException, solo que no retorna el tipo en
-- notación de brujin.
getRenameTypeWhitException :: [String] -> Type -> Either ProofExceptions Type
getRenameTypeWhitException fv t =
  case renameType fv t of
    Left s -> Left $ PropNotExists s
    Right x -> Right x


renameType :: [String] -> Type -> Either String Type
renameType fv = renameType' fv [] []

renameType' :: [String] -> [String] -> [String] -> Type -> Either String Type
renameType' fv rv bv (B v) =
  case v `elemIndex` bv of
    Just i -> return $ B $ rv!!i
    Nothing -> if elem v fv
               then return $ B v
               else Left v
renameType' fv rv bv (ForAll v t) = do let v' = getRename v fv rv
                                       x <- renameType' fv (v':rv) (v:bv) t
                                       return $ ForAll v' x
renameType' fv rv bv (Exists v t) = do let v' = getRename v fv rv
                                       x <- renameType' fv (v':rv) (v:bv) t
                                       return $ Exists v' x
renameType' fv rv bv (Fun t t') = do x <- renameType' fv rv bv t
                                     x' <- renameType' fv rv bv t'
                                     return $ Fun x x'
renameType' fv rv bv (And t t') = do x <- renameType' fv rv bv t
                                     x' <- renameType' fv rv bv t'
                                     return $ And x x'
renameType' fv rv bv (Or t t') = do x <- renameType' fv rv bv t
                                    x' <- renameType' fv rv bv t'
                                    return $ Or x x'


replace :: (Type,TType) -> (Type,TType) -> (Type,TType)
replace = replace' 0

replace' :: Int -> (Type,TType) -> (Type,TType) -> (Type,TType)
replace' n t@(x,TBound v) r
  | n == v = r
  | otherwise = t
replace' n t@(x,TFree v) _ = t
replace' n (Fun t1 t2, TFun t1' t2') r = let (x,x')= replace' n (t1,t1') r
                                             (y,y')= replace' n (t2,t2') r
                                         in (Fun x y, TFun x' y')
replace' n (Exists v t, TExists t') r = let (x,x') = replace' (n+1) (t,t') r          
                                        in (Exists v x, TExists x')
replace' n (ForAll v t, TForAll t') r = let (x,x') = replace' (n+1) (t,t') r          
                                        in (ForAll v x, TForAll x')
replace' n (And t1 t2, TAnd t1' t2') r = let (x,x')= replace' n (t1,t1') r
                                             (y,y')= replace' n (t2,t2') r
                                         in (And x y, TAnd x' y')
replace' n (Or t1 t2, TOr t1' t2') r = let (x,x')= replace' n (t1,t1') r
                                           (y,y')= replace' n (t2,t2') r
                                       in (Or x y, TOr x' y')
replace' _ _ _ = error "error: replace' no debería pasar."

----------------------------------------------------------------------------------------------------------------------

--ARREGLAR
-- intro_exists :: TType -> TType -> (Type, TType) -> Term
-- intro_exists s_a0 s a0 = Lam s_a0 $ BLam $ Lam (TForAll $ TFun s (TBound 1)) $ (Bound 0 :!: a0) :@: (Bound 1)      

--ESTA MAL
elim_exists :: (Type, TType) -> (Type, TType) -> Term
elim_exists (s,s') x@(ForAll _ (Fun _ t), TForAll (TFun _ t'))
  = Lam (s, s') $ Lam x $ (Bound 1 :!: (t, t')) :@: (Bound 0)

-- elim_exists :: TType -> (Type, TType) -> Term
-- elim_exists s (b, b') = Lam (TExists s) $ Lam (TForAll $ TFun s b') $ (Bound 1 :!: (b, b')) :@: (Bound 0)


-- En el término utilizo TFree "a" en lugar de TBound 0, para que la impresión en
-- patalla quede bien.
-- intro_and :: (Type, TType) -> (Type, TType) -> Term
-- intro_and x@(x1, x2) y@(y1, y2) =
--   Lam x $ Lam y $
--   BLam "a" $ Lam (Fun x1 $ Fun y1 (B "a"), TFun x2 $ TFun y2 (TFree "a")) (((Bound 0) :@: (Bound 2)) :@: (Bound 1))

intro_and :: Term
intro_and =
  BLam "a" $ BLam "b" $ Lam (B "a", TBound 1) $ Lam (B "b", TBound 0) $ BLam "c" $
  Lam (Fun (B "a") $ Fun (B "b") (B "c"), TFun (TBound 2) $ TFun (TBound 1) (TBound 0)) $
  (Bound 0 :@: Bound 2) :@: Bound 1

-- Teorema de eliminación del and "general": forall a b c, a /\ b -> (a -> b -> c) -> c
elim_and :: Term
elim_and =
  BLam "a" $ BLam "b" $ BLam "c" $ Lam (And (B "a") (B "b"), TAnd (TBound 2) (TBound 1)) $
  Lam (Fun (B "a") (Fun (B "b") (B "c")), TFun (TBound 2) (TFun (TBound 1) (TBound 0))) $
  (Bound 1) :!: (B "c", TBound 0) :@: (Bound 0)

-- elim_and1 :: Term
-- elim_and1 =
--   BLam "a" $ BLam "b" $ Lam (And (B "a") (B "b"), TAnd (TBound 1) (TBound 0)) $
--   (Bound 0 :!: (B "a", TBound 1)) :@: (Lam (B "a", TBound 1) $ Lam (B "b", TBound 0) $ Bound 1)  

-- elim_and2 :: Term
-- elim_and2 =
--   BLam "a" $ BLam "b" $ Lam (And (B "a") (B "b"), TAnd (TBound 1) (TBound 0)) $
--   (Bound 0 :!: (B "b", TBound 0)) :@: (Lam (B "a", TBound 1) $ Lam (B "b", TBound 0) $ Bound 0)  

intro_or1 ::Term
intro_or1 =
  BLam "a" $ BLam "b" $ Lam (B "a", TBound 1) $ BLam "c" $
  Lam (Fun (B "a") (B "c"), TFun (TBound 2) (TBound 0)) $
  Lam (Fun (B "b") (B "c"), TFun (TBound 1) (TBound 0)) $ Bound 1 :@: Bound 2

intro_or2 ::Term
intro_or2 =
  BLam "a" $ BLam "b" $ Lam (B "b", TBound 0) $ BLam "c" $
  Lam (Fun (B "a") (B "c"), TFun (TBound 2) (TBound 0)) $
  Lam (Fun (B "b") (B "c"), TFun (TBound 1) (TBound 0)) $ Bound 0 :@: Bound 2

elim_or :: Term
elim_or =
  BLam "a" $ BLam "b" $ BLam "c" $ Lam (Or (B "a") (B "b"), TOr (TBound 2) (TBound 1)) $
  Lam (Fun (B "a") (B "c"), TFun (TBound 2) (TBound 0)) $
  Lam (Fun (B "b") (B "c"), TFun (TBound 1) (TBound 0)) $
  ((Bound 2 :!: (B "c", TBound 0)) :@: Bound 1) :@: Bound 0

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

getHypothesisValue :: Int -> String -> Proof Int
getHypothesisValue n h
  | isDefault h = let x = getValue h
                  in if isValidValue n x
                     then return x
                     else throw ApplyE2
  | otherwise = throw ApplyE2

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

bottom :: (Type, TType)
bottom = (ForAll "a" (B "a"), TForAll (TBound 0))


typeWithoutName :: Type -> TType
typeWithoutName = typeWithoutName' []

typeWithoutName' :: [String] -> Type -> TType
typeWithoutName' xs (B t) = maybe (TFree t) TBound (t `elemIndex` xs)
typeWithoutName' xs (Fun t t') = TFun (typeWithoutName' xs t) (typeWithoutName' xs t')
typeWithoutName' xs (ForAll v t) = TForAll $ typeWithoutName' (v:xs) t
typeWithoutName' xs (Exists v t) = TExists $ typeWithoutName' (v:xs) t
typeWithoutName' xs (And t t') = TAnd (typeWithoutName' xs t) (typeWithoutName' xs t')
typeWithoutName' xs (Or t t') = TOr (typeWithoutName' xs t) (typeWithoutName' xs t')


unification :: Bool -> Int -> TType -> (Type,TType) ->
  Either ProofExceptions (M.Map Int (Type,TType))
unification True _ = \ _ _ -> return M.empty
unification False n = unif 0 n M.empty

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
unif pos n sust (TAnd t1' t2') (And tt1 tt2, TAnd tt1' tt2') =
  do res <- unif pos n sust t1' (tt1, tt1')
     unif pos n res t2' (tt2,tt2')
unif pos n sust (TOr t1' t2') (Or tt1 tt2, TOr tt1' tt2') =
  do res <- unif pos n sust t1' (tt1, tt1')
     unif pos n res t2' (tt2,tt2')
unif pos n sust (TForAll t') (ForAll _ tt, TForAll tt') = unif (pos+1) (n+1) sust t' (tt,tt')
unif pos n sust (TExists t') (Exists _ tt, TExists tt') = unif (pos+1) (n+1) sust t' (tt,tt')
unif _ _ _ _ _ = throw Unif4

-- Obtiene la substitución, a partir de la profundidad dada por el 1º argumento.
substitution :: Int -> (Type, TType) -> Maybe (Type, TType)
substitution = substitution' 0

substitution' :: Int -> Int -> (Type, TType) -> Maybe (Type, TType)
substitution' m n (t,t'@(TBound x))
  | x < m = return (t,t')
  | (m <= x) && (x < n) = Nothing
  | otherwise = return (t, TBound $ x - n + m)
substitution' _ _ (t, t'@(TFree f)) = return (t,t')
substitution' m n (Fun t1 t2,TFun t1' t2') = do (x,x') <- substitution' m n (t1,t1')
                                                (y,y') <- substitution' m n (t2,t2')
                                                return (Fun x y, TFun x' y')
substitution' m n (ForAll v t, TForAll t') = do (x,x') <- substitution' (m+1) (n+1) (t,t')
                                                return (ForAll v x, TForAll x')
substitution' m n (Exists v t, TExists t') = do (x,x') <- substitution' (m+1) (n+1) (t,t')
                                                return (Exists v x, TExists x')

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
getRenameWhitException :: [String] -> Type -> Either ProofExceptions (Type, TType)
getRenameWhitException fv t =
  case rename fv t of
    Left s -> Left $ PropNotExists s
    Right x -> Right x
  

rename :: [String] -> Type -> Either String (Type, TType)
rename fv = rename' fv [] []

rename' :: [String] -> [String] -> [String] -> Type -> Either String (Type, TType)
rename' fv rv bv (B v) =
  case v `elemIndex` bv of
    Just i -> return (B $ rv!!i, TBound i)
    Nothing -> if elem v fv
               then return (B v, TFree v)
               else Left v
rename' fv rv bv (ForAll v t) = do let v' = getRename v fv rv
                                   (x,y) <- rename' fv (v':rv) (v:bv) t
                                   return (ForAll v' x, TForAll y)
rename' fv rv bv (Exists v t) = do let v' = getRename v fv rv
                                   (x,y) <- rename' fv (v':rv) (v:bv) t
                                   return (Exists v' x, TExists y)
rename' fv rv bv (Fun t t') = do (x,y) <- rename' fv rv bv t
                                 (x',y') <- rename' fv rv bv t'
                                 return (Fun x x', TFun y y')
rename' fv rv bv (And t t') = do (x,y) <- rename' fv rv bv t
                                 (x',y') <- rename' fv rv bv t'
                                 return (And x x', TAnd y y')
rename' fv rv bv (Or t t') = do (x,y) <- rename' fv rv bv t
                                (x',y') <- rename' fv rv bv t'
                                return  (Or x x', TOr y y')

--------------------------------------------------------------------

-- Genera el lambda término, sin nombre de término ni de tipo.
-- Además, chequea que las variables de tipo sean válidas de acuerdo al contexto
-- dado por el 1º arg.
withoutName :: TypeContext -> LamTerm -> Either ProofExceptions Term
withoutName = withoutName' [] []

withoutName' :: [String] -> [String] -> TypeContext -> LamTerm -> Either ProofExceptions Term
withoutName' _ teb tyc (LVar x) = case elemIndex x teb of
                                    Just n -> return $ Bound n
                                    Nothing -> return $ Free $ Global x
withoutName' tyb teb tyc (Abs x t e) = do t' <- typeWhitoutName tyc tyb t
                                          e' <- withoutName' tyb (x:teb) tyc e
                                          return $ Lam (t, t') e'
withoutName' tyb teb tyc (App e1 e2) = do e1' <- withoutName' tyb teb tyc e1
                                          e2' <- withoutName' tyb teb tyc e2
                                          return $ e1' :@: e2'
withoutName' tyb teb tyc (BAbs x e) = do e' <- withoutName' (x:tyb) teb tyc e
                                         return $ BLam x e'
withoutName' tyb teb tyc (BApp e t) = do e' <- withoutName' tyb teb tyc e
                                         t' <- typeWhitoutName tyc tyb t
                                         return $ e' :!: (t,t')


typeWhitoutName :: TypeContext -> [String] -> Type -> Either ProofExceptions TType
typeWhitoutName tyc xs (B x) = case elemIndex x xs of
                                 Just n -> return $ TBound n
                                 Nothing -> case elemIndex x tyc of
                                              Just m -> return $ TFree x
                                              Nothing -> throw $ TermE x
typeWhitoutName tyc xs (ForAll x t) = do r <- typeWhitoutName tyc (x:xs) t
                                         return $ TForAll r
typeWhitoutName tyc xs (Exists x t) = do r <- typeWhitoutName tyc (x:xs) t
                                         return $ TExists r
typeWhitoutName tyc xs (Fun t1 t2 ) = do r1 <- typeWhitoutName tyc xs t1
                                         r2 <- typeWhitoutName tyc xs t2
                                         return $ TFun r1 r2
typeWhitoutName tyc xs (And t1 t2) = do r1 <- typeWhitoutName tyc xs t1
                                        r2 <- typeWhitoutName tyc xs t2
                                        return $ TAnd r1 r2
typeWhitoutName tyc xs (Or t1 t2) = do r1 <- typeWhitoutName tyc xs t1
                                       r2 <- typeWhitoutName tyc xs t2
                                       return $ TOr r1 r2


-- Infiere el tipo sin nombre de un lambda término, de acuerdo a la
-- lista de teoremas dada por el 1º arg.
-- Suponemos que ninguna de las pruebas de los teoremas son recursivas.
-- Es decir, que su lambda término es recursivo.
inferType :: M.Map String Term -> Term -> Either ProofExceptions (Type, TType)
inferType = inferType' 0 []

inferType' :: Int -> [(Int,Type,TType)] -> M.Map String Term -> Term -> Either ProofExceptions (Type, TType)
inferType' n _ te (Free (Global x)) =
  case M.lookup x te of
    Just t -> inferType te t
    Nothing -> throw $ InferE1 x -- NO puede haber variables de términos libres que no sean teoremas.
inferType' n c te (Bound x) = let (m,t,t') = c !! x
                              in return (t,renameTType (n-m) t')
inferType' n c te (Lam (t,t') x) = do (tt,tt') <- inferType' n ((n,t,t'):c) te x
                                      return (Fun t tt, TFun t' tt')
inferType' n c te (x :@: y) = do (tt1, tt1') <- inferType' n c te x
                                 case (tt1, tt1') of
                                   (Fun _ t2, TFun t1' t2') ->
                                     do (tt2, tt2') <- inferType' n c te y
                                        if tt2' == t1'
                                          then return (t2, t2')
                                          else throw $ InferE2 tt2
                                   _ -> throw $ InferE3 tt1
inferType' n c te (BLam v x) = do (t,t') <- inferType' (n+1) c te x
                                  return (ForAll v t, TForAll t')
inferType' n c te (x :!: (t,t')) = do (tt,tt') <- inferType' n c te x
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
renameTType' n r (TExists t) = TExists $ renameTType' (n+1) r t
renameTType' n r (TFun t1 t2) = TFun (renameTType' n r t1) (renameTType' n r t2)
renameTType' n r (TAnd t1 t2) = TAnd (renameTType' n r t1) (renameTType' n r t2)
renameTType' n r (TOr t1 t2) = TOr (renameTType' n r t1) (renameTType' n r t2)

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
inferReplaceType' n (ForAll v t1, TForAll t1') t = let (tt, tt') = inferReplaceType' (n+1) (t1,t1') t
                                                   in (ForAll v tt, TForAll tt')
inferReplaceType' n (Exists v t1, TExists t1') t = let (tt, tt') = inferReplaceType' (n+1) (t1,t1') t
                                                   in (Exists v tt, TExists tt')
inferReplaceType' n (Fun t1 t2, TFun t1' t2') t = let (tt1, tt1') = inferReplaceType' n (t1,t1') t
                                                      (tt2, tt2') = inferReplaceType' n (t2,t2') t
                                                  in (Fun tt1 tt2, TFun tt1' tt2')
inferReplaceType' n (And t1 t2, TAnd t1' t2') t = let (tt1, tt1') = inferReplaceType' n (t1,t1') t
                                                      (tt2, tt2') = inferReplaceType' n (t2,t2') t
                                                  in (And tt1 tt2, TAnd tt1' tt2')
inferReplaceType' n (Or t1 t2, TOr t1' t2') t = let (tt1, tt1') = inferReplaceType' n (t1,t1') t
                                                    (tt2, tt2') = inferReplaceType' n (t2,t2') t
                                                in (Or tt1 tt2, TOr tt1' tt2')

-- Obtiene la variable de tipo renombrada de acuerdo a la profundidad que se quiere
-- con el 1º argumento.
getTypeVar :: Int -> TypeVar -> (Type, TType)
getTypeVar n (m, t, t') = (t, renameTType (n-m) t')

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
