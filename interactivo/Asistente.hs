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
                        i <- maybeToProof AssuE (findIndex (\x->snd x == tw) c)
                        modifyTerm $ simplify (Bound i)
                        finishSubProof                        
habitar Intro = do x <- getType
                   introComm x
habitar Intros = introsComm
habitar (Apply h) = do x <- getType
                       (t,t') <- maybeToProof EmptyType x
                       n <- getPosition
                       i <- getHypothesisValue n h
                       c <- getContext
                       applyComm (n-i-1) (t,t') (c !! (n-i-1))                       
habitar (Elim h) = do x <- getType
                      (t,t') <- maybeToProof EmptyType x
                      n <- getPosition
                      i <- getHypothesisValue n h
                      c <- getContext
                      elimComm i (t,t') (c !! (n-i-1))
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
                       do modifySubP (+1)
                          modifyPosition $ repeatOrSubstract 2
                          modifyTypeCont $ repeatOrSubstract 2
                          modifyContext $ repeatOrSubstract 2
                          modifyType (\tys -> Just (t1,t1') : Just (t2,t2') : tail tys)
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
  do incrementPosition (+ 1)
     addContext (t1,t1')
     replaceType (t2, t2')
     modifyTerm $ addHT (\x -> Lam t1' x)
introComm (Just (ForAll q t, TForAll t')) =
  do addTypeContext q
     replaceType (t, renameBounds q t')
     modifyTerm $ addHT (\x -> BLam x)
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
  do modifySubP (+ 1)
     modifyPosition $ repeatOrSubstract 2
     modifyTypeCont $ repeatOrSubstract 2
     modifyContext $ repeatOrSubstract 2
     modifyType (\tys -> Just (Fun t1 t, TFun t1' t') :
                         Just (Fun t2 t, TFun t2' t') : tail tys)
     modifyTerm $ addDHT (\x y -> ((Free $ Global "elim_or")
                                    :!: (t1,t1') :!: (t2,t2') :!: (t,t'))
                                  :@: (Bound i) :@: x :@: y)
elimComm i (t,t') (Exists v t1, TExists t1') =
  do tc <- getTypeContext
     replaceType (tyExists tc v t1 t, TForAll $ TFun t1' t')
     modifyTerm $ addHT (\x -> (elim_exists t1' (t,t')) :@: (Bound i) :@: x)
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
     modifySubP (+ (n-1))
     modifyPosition $ repeatOrSubstract n
     modifyTypeCont $ repeatOrSubstract n
     modifyContext $ repeatOrSubstract n
     modifyType (\tys -> getTypesFun n ht ++ tail tys)
     modifyTerm $ getApplyTermFun n i
applyComm i x ht@(ForAll _ _, TForAll _) =
  do let equal = snd ht == snd x
     let (ft, n) = getNestedTypeForAll equal (snd ht)
     r <- eitherToProof $ unification equal n ft x
     let m = n - M.size r
     modifySubP (+ (m-1))
     modifyPosition $ repeatOrSubstract m
     modifyTypeCont $ repeatOrSubstract m
     modifyContext $ repeatOrSubstract m
     modifyType (\tys -> getTypesForAll m (tail tys))
     modifyTerm $ getApplyTermForAll n r (Bound i)
applyComm i (t1, t1') (t, t')
  | t' == t1' = do modifyTerm $ simplify (Bound i)
                   finishSubProof
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

repeatHead :: Int -> [a] -> [a]
repeatHead _ [] = error "error: repeatHead."
repeatHead n xs
  | n == 0 = xs
  | n > 0 = head xs : (repeatHead (n-1) xs )
  | n < 0 = error "error: repeatHead."

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

repeatOrSubstract :: Int -> [a] -> [a]
repeatOrSubstract m xs
  | m == 0 = tail xs
  | otherwise = repeatHead (m-1) xs

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


intro_exists :: TType -> TType -> (Type, TType) -> Term
intro_exists s_a0 s a0 = Lam s_a0 $ BLam $ Lam (TForAll $ TFun s (TBound 1)) $ (Bound 0 :!: a0) :@: (Bound 1)      

elim_exists :: TType -> (Type, TType) -> Term
elim_exists s (b, b') = Lam (TExists s) $ Lam (TForAll $ TFun s b') $ (Bound 1 :!: (b, b')) :@: (Bound 0)

intro_and :: Term
intro_and = BLam $ BLam $ Lam (TBound 1) $ Lam (TBound 0) $ BLam $ Lam (TFun (TBound 2) (TFun (TBound 1) (TBound 0)))
            (((Bound 0) :@: (Bound 2)) :@: (Bound 1))
            
elim_and :: Term
elim_and = BLam $ BLam $ BLam $ Lam (TAnd (TBound 2) (TBound 1)) $ Lam (TFun (TBound 2) (TFun (TBound 1) (TBound 0)))
           (Bound 1) :!: (B "c", TBound 0) :@: (Bound 0)

intro_or1 ::Term
intro_or1 = BLam $ BLam $ Lam (TBound 1) $ BLam $ Lam (TFun (TBound 2) (TBound 0)) $ Lam (TFun (TBound 1) (TBound 0))
            (Bound 1) :@: (Bound 2)

intro_or2 ::Term
intro_or2 = BLam $ BLam $ Lam (TBound 0) $ BLam $ Lam (TFun (TBound 2) (TBound 0)) $ Lam (TFun (TBound 1) (TBound 0))
            (Bound 0) :@: (Bound 2)

elim_or :: Term
elim_or = BLam $ BLam $ BLam $ Lam (TOr (TBound 2) (TBound 1)) $ Lam (TFun (TBound 2) (TBound 0)) $
          Lam (TFun (TBound 1) (TBound 0)) $ (Bound 2) :!: (B "c", TBound 0) :@: (Bound 1) :@: (Bound 0)



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

isFreeType' :: Var -> TType -> Bool
isFreeType' q (TFree p) = q == p
isFreeType' q (TBound p) = False
isFreeType' q (TFun a b) = isFreeType' q a || isFreeType' q b
isFreeType' q (TForAll a) = isFreeType' q a
isFreeType' q (TExists a) = isFreeType' q a
isFreeType' q (TAnd a b) = isFreeType' q a || isFreeType' q b

--Creo que no es necesaria
isFreeType :: Var -> Context -> Bool
isFreeType q = foldl (\r x -> isFreeType' q (snd x) || r) False


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
                    (\s -> return $ M.insert k s sust) (substitution tt)
         Just (s,s') -> if s' == tt2
                        then return sust
                        else throw Unif1
  | otherwise = if t == tt2
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


substitution :: (Type, TType) -> Maybe (Type, TType)
substitution = substitution' 0

substitution' :: Int -> (Type, TType) -> Maybe (Type, TType)
substitution' m (t,t'@(TBound x))
  | x < m = return (t,t')
  | otherwise = Nothing
substitution' _ (t, t'@(TFree f)) = return (t,t')
substitution' m (Fun t1 t2,TFun t1' t2') = do (x,x') <- substitution' m (t1,t1')
                                              (y,y') <- substitution' m (t2,t2')
                                              return (Fun x y, TFun x' y')
substitution' m (ForAll v t, TForAll t') = do (x,x') <- substitution' (m+1) (t,t')
                                              return (ForAll v x, TForAll x')
substitution' m (Exists v t, TExists t') = do (x,x') <- substitution' (m+1) (t,t')
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
--TERMINAR
-- termWithName :: Term -> Type -> LamTerm
-- termWithName' t = termWithName [] (vars \\ fv t) t

-- termWithName' :: [String] -> [String] -> Term -> Type -> LamTer
-- termWithName' (b:bs) fs (Bound i) (B t) = LVar $ bs !! j
-- termWithName' bs fs (Free (Global n)) (B t)
--   | n == t = LVar n
--   | otherwise = error "error: termWithName', no debería pasar"
-- termWithName' bs (f:fs) (Lam tt te) (Fun t1 t2) = Abs f t1 $ termWithName' bs fs te t2
-- termWithName' bs fs (te1 :@: te2) t = 


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
