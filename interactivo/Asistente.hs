module Asistente where

import Common
import Data.Char (isDigit)
import Data.List (findIndex, elemIndex)
import Control.Monad (unless)

habitar :: ProofState -> Tactic -> Either ProofExceptions ProofState
--habitar (PState {term=Term _}) _ = error "habitar: no debería pasar"

habitar (PState {name=name, subp=p, position=n:ns, typeContext=tc:tcs, context=c:cs, ty=(t, tw):tys, term=ts}) Assumption =
  do i <- maybeToEither AssuE (findIndex (\x->snd x == tw) c)
     return $ PState {name=name, subp=p-1, position=ns, typeContext=tcs, context=cs, ty=tys, term=simplify (Bound i) ts}

habitar (PState {name=name, subp=p, position=n:ns, typeContext=tcs, context=c:cs, ty=(Fun t1 t2, TFun t1' t2'):tys, term=ts}) Intro =
  return $ PState {name=name, subp=p, position=(n+1):ns, typeContext=tcs, context=((t1,t1'):c):cs, ty=(t2, t2'):tys, term=addHT (\x -> Lam t1' x) ts}

habitar (PState {name=name, subp=p, position=ns, typeContext=tc:tcs, context=c:cs, ty=(ForAll q t, TForAll t'):tys, term=ts}) Intro
  | not $ isFreeType q c = return PState {name=name, subp=p, position=ns, typeContext=(q:tc):tcs, context=c:cs, ty=(t, renameBounds q t'):tys, term=addHT (\x -> BLam x) ts}
  | otherwise = throwError IntroE2

habitar _ Intro = throwError IntroE1

habitar st@(PState {position=n:ns,context=c:cs}) (Apply h) = do i <- getHypothesisValue n h
                                                                applyComm (n-i-1) st (c !! (n-i-1))
                                                          
habitar st@(PState {position=n:ns,context=c:cs}) (Elim h) = do i <- getHypothesisValue n h
                                                               elimComm i st (c !! (n-i-1))
                                                               
habitar (PState {name=name, subp=p, position=ns, typeContext=tcs, context=cs, ty=(Or t1 t2 , TOr t1' t2'):tys, term=ts}) CLeft = 
  return $ PState {name=name, subp=p, position=ns, typeContext=tcs, context=cs, ty=(t1,t1'):tys,
                   term=addHT (\x -> ((Free $ Global "intro_or1") :!: (t1,t1') :!: (t2,t2')) :@: x) ts}

habitar (PState {name=name, subp=p, position=ns, typeContext=tcs, context=cs, ty=(Or t1 t2 , TOr t1' t2'):tys, term=ts}) CRight = 
  return $ PState {name=name, subp=p, position=ns, typeContext=tcs, context=cs, ty=(t2,t2'):tys,
                   term=addHT (\x -> ((Free $ Global "intro_or2") :!: (t1,t1') :!: (t2,t2')) :@: x) ts}

habitar (PState {name=name, subp=p, position=n:ns, typeContext=tc:tcs, context=c:cs, ty=(And t1 t2, TAnd t1' t2'):tys, term=ts}) Split =
  return $ PState {name=name, subp=p+1, position=n:n:ns, typeContext=tc:tc:tcs, context=c:c:cs, ty=(t1,t1'):(t2,t2'):tys,
                   term=addDHT (\x y -> ((Free $ Global "intro_and") :!: (t1,t1') :!: (t2,t2')) :@: x :@: y) ts}

-- TERMINAR: hacer "intro_exists"
habitar (PState {name=name, subp=p, position=ns, typeContext=tc:tcs, context=c:cs, ty=(Exists q t, TExists t'):tys, term=ts}) (CExists x)=
  do (y,y') <- getRenameWhitException tc x
     let (z,z') = replace (t,t') (y,y') 
     r <- getRenameTypeWhitException tc z
     return $ PState {name=name, subp=p, position=ns, typeContext=tc:tcs, context=c:cs, ty=(r,z'):tys, term=addHT (\x -> (Free $ Global "intro_exists") :@: x) ts}


-- Asumimos que las tuplas del 3º arg. , tienen la forma correcta.
elimComm :: Int -> ProofState -> (Type, TType) -> Either ProofExceptions ProofState
elimComm i (PState {name=name, subp=p, position=ns, typeContext=tcs, context=cs, ty=(t, t'):tys, term=ts}) (And t1 t2, TAnd t1' t2') =
  return $ PState {name=name, subp=p, position=ns, typeContext=tcs, context=cs, ty=(Fun t1 (Fun t2 t), TFun t1' (TFun t2' t')):tys,
                   term=addHT (\x -> ((Free $ Global "elim_and") :!: (t1,t1') :!: (t2,t2') :!: (t,t')) :@: (Bound i) :@: x) ts}
elimComm i (PState {name=name, subp=p, position=n:ns, typeContext=tc:tcs, context=c:cs, ty=(t,t'):tys, term=ts}) (Or t1 t2, TOr t1' t2') =
  return $ PState {name=name, subp=p+1, position=n:n:ns, typeContext=tc:tc:tcs, context=c:c:cs, ty=(Fun t1 t, TFun t1' t'):(Fun t2 t, TFun t2' t'):tys,
                   term=addDHT (\x y -> ((Free $ Global "elim_or") :!: (t1,t1') :!: (t2,t2') :!: (t,t')) :@: (Bound i) :@: x :@: y) ts}
elimComm _ _ _ = throwError ElimE1

getFinalType :: TType -> (TType, Int)
getFinalType (TFun x y) = let (f, n) = getFinalType y
                                  in (f, n+1)
getFinalType x = (x, 0)

repeatHead :: Int -> [a] -> [a]
repeatHead _ [] = error "error: repeatHead"
repeatHead n xs
  | n == 0 = xs
  | n > 0 = head xs : (repeatHead (n-1) xs )
  | n < 0 = error "error: repeatHead"
            
getArgsType :: (Type, TType) -> [(Type, TType)]
getArgsType (Fun t1 t2, TFun t1' t2') = (t1,t1') : getArgsType (t2, t2')
getArgsType _ = []

getApplyTerms :: Int -> Int -> [SpecialTerm] -> [SpecialTerm]
getApplyTerms 1 i ts = addHT (\x -> (Bound i) :@: x) ts
getApplyTerms 2 i ts = addDHT (\x y -> ((Bound i) :@: x) :@: y) ts
getApplyTerms n i ts = addDHT (\x y -> x :@: y) $ getApplyTerms (n-1) i ts

applyComm :: Int -> ProofState -> (Type, TType) -> Either ProofExceptions ProofState
applyComm i (PState {name=name, subp=p, position=ns, typeContext=tcs, context=cs, ty=(t, t'):tys, term=ts}) ht@(Fun t1 t2, TFun t1' t2') =
  do let (ft, n) = getFinalType $ snd ht
     unless (t' == ft) (throwError ApplyE1)
     return $ PState {name=name, subp=p+n-1,
                      position=repeatHead (n-1) ns,
                      typeContext=repeatHead (n-1) tcs,
                      context=repeatHead (n-1) cs,
                      ty=getArgsType ht ++ tys,
                      term=getApplyTerms n i ts}
applyComm i (PState {name=name, subp=p, position=n:ns, typeContext=tc:tcs, context=c:cs, ty=(t,t'):tys, term=ts}) (ForAll v t1, TForAll t1') =
  do r <- unification (t1, t1') (t,t')
     case r of
       Nothing -> return $ PState {name=name, subp=p-1, position=ns, typeContext=tcs, context=cs, ty=tys, term=simplify ((Bound i) :!: bottom) ts}
       Just x -> return $ PState {name=name, subp=p-1, position=ns, typeContext=tcs, context=cs, ty=tys, term=simplify ((Bound i) :!: x) ts}
applyComm _ _ _ = throwError ApplyE2


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


getHypothesisValue :: Int -> String -> Either ProofExceptions Int
getHypothesisValue n h
  | isDefault h = let x = getValue h
                  in if isValidValue n x
                     then return x
                     else throwError ApplyE3
  | otherwise = throwError ApplyE3

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
typeWithoutName' xs (And t t') = TAnd (typeWithoutName' xs t) (typeWithoutName' xs t')
typeWithoutName' xs (Or t t') = TOr (typeWithoutName' xs t) (typeWithoutName' xs t')


unification :: (Type,TType) -> (Type,TType) -> Either ProofExceptions (Maybe (Type,TType))
unification = unif 0 Nothing

unif :: Int -> Maybe (Type,TType) -> (Type,TType) -> (Type,TType) -> Either ProofExceptions (Maybe (Type,TType))
unif pos sust (t1,t2@(TBound n)) tt@(tt1,tt2)
  | n == pos = case sust of
    Nothing -> maybe (throwError Unif1) (return . return) (substitution pos tt)
    Just (s,s') -> if s' == tt2
                   then return $ Just (s,s')
                   else throwError Unif1
  | otherwise = if t2 == tt2
                then return $ sust
                else throwError Unif2
unif _ sust (t1,TFree n) (tt1,TFree m)
  | n == m = return sust
  | otherwise = throwError Unif3
unif pos sust (Fun t1 t2,TFun t1' t2') (Fun tt1 tt2, TFun tt1' tt2') =
  do res <- unif pos sust (t1,t1') (tt1, tt1')
     unif pos res (t2,t2') (tt2,tt2')
unif pos sust (And t1 t2,TAnd t1' t2') (And tt1 tt2, TAnd tt1' tt2') =
  do res <- unif pos sust (t1,t1') (tt1, tt1')
     unif pos res (t2,t2') (tt2,tt2')
unif pos sust (Or t1 t2,TOr t1' t2') (Fun tt1 tt2, TFun tt1' tt2') =
  do res <- unif pos sust (t1,t1') (tt1, tt1')
     unif pos res (t2,t2') (tt2,tt2')
unif pos sust (ForAll _ t, TForAll t') (ForAll _ tt, TForAll tt') = unif (pos+1) sust (t,t') (tt,tt')
unif pos sust (Exists _ t, TExists t') (Exists _ tt, TExists tt') = unif (pos+1) sust (t,t') (tt,tt')
unif _ _ _ _ = throwError Unif4


substitution :: Int -> (Type, TType) -> Maybe (Type, TType)
substitution = substitution' 0

substitution' :: Int -> Int -> (Type, TType) -> Maybe (Type, TType)
substitution' m n (t,t'@(TBound x))
  | x < m = return (t,t')
  | otherwise = Nothing
substitution' _ _ (t, t'@(TFree f)) = return (t,t')
substitution' m n (Fun t1 t2,TFun t1' t2') = do (x,x') <- substitution' m n (t1,t1')
                                                (y,y') <- substitution' m n (t2,t2')
                                                return (Fun x y, TFun x' y')
substitution' m n (ForAll v t, TForAll t') = do (x,x') <- substitution' (m+1) (n+1) (t,t')
                                                return (ForAll v x, TForAll x')
substitution' m n (Exists v t, TExists t') = do (x,x') <- substitution' (m+1) (n+1) (t,t')
                                                return (Exists v x, TExists x')


--------------------------------------------------------------------
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


--------------------------------------------------------------------


maybeToEither :: e -> Maybe a -> Either e a
maybeToEither errorval Nothing = throwError errorval
maybeToEither _ (Just normalval) = return normalval

throwError :: e -> Either e a
throwError x = Left x