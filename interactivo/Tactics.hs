module Tactics where

import Common
import Proof
import DefaultOperators
import TermsWithHoles
import RenamedVariables
import Hypothesis
import Transformers
import TypeInference (typeInference)
import TypeUnification (unification)
import TypeSubstitution (typeSubs)
import Control.Monad (unless, when)
import qualified Data.Map.Strict as M (Map, lookup, insert, empty, size)
import Data.Maybe (fromJust, isJust)
import qualified Data.Sequence as S

-- Contruye la prueba.
habitar :: Tactic -> Proof ()
habitar Assumption =
  do x <- getType
     (_,tw) <- maybeToProof EmptyType x 
     c <- getTermContext
     q <- getTBTypeVars
     i <- maybeToProof AssuE $ S.findIndexL (\(_,p,_,t) -> positiveShift (q - p) t == tw) c
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
     applyComm i (t,t') (getTypeVar q $ S.index c i)
habitar (Elim h) =
  do x <- getType
     (t,t') <- maybeToProof EmptyType x
     n <- getTTermVars
     cn <- getConflictNames
     i <- maybeToProof (HypoE h) $ getHypoPosition cn n h
     c <- getTermContext
     q <- getTBTypeVars
     elimComm i (t,t') (getTypeVar q $ S.index c i)
habitar CLeft =
  do x <- getType
     case x of
       Just (RenameTy _ 2 [t1,t2] , RenameTTy n [t1',t2']) ->
         if n == or_code
         then do replaceType (t1,t1')
                 modifyTerm $ addHT (\x -> ((Free $ NGlobal "intro_or1")
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
                 modifyTerm $ addHT (\x -> ((Free $ NGlobal "intro_or2")
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
                 modifyTerm $ addDHT (\x y -> ((Free $ NGlobal "intro_and")
                                                :!: (t1,t1') :!: (t2,t2'))
                                              :@: x :@: y)
         else throw CommandInvalid
       _ -> throw CommandInvalid
habitar (Exact (LamT te)) =
  do x <- getType
     tt <- maybeToProof EmptyType x
     op <- getUsrOpers
     n <- getTTermVars
     cn <- getConflictNames
     btc <- getBTypeContext
     ftc <- getFTypeContext
     te' <- eitherToProof $ withoutName op ftc btc (cn,n) te
     exactTerm te' tt  
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
     x <- getType
     case t of
       Right te ->
         do tt <- maybeToProof EmptyType x
            exactTerm te tt
       Left ty ->
         do when (isJust x) $ throw $ ExactE2 $ fst $ fromJust x
            exactType ty
habitar (Unfold s Nothing) =
  do x <- getType
     (t,t') <- maybeToProof EmptyType x
     op <- getUsrOpers
     (m, (_, (tt,tt'), _, _)) <- maybeToProof (UnfoldE1 s) $ getElemIndex (\(x,_,_,_) -> x == s) op
     btc <- getBTypeContext
     ftc <- getFTypeContext
     replaceType $ unfoldComm btc ftc op m (t,t') (tt,tt')
habitar (Unfold s (Just h)) =
  do op <- getUsrOpers
     (m, (_, (tt,tt'), _, _)) <- maybeToProof (UnfoldE1 s) $ getElemIndex (\(x,_,_,_) -> x == s) op
     n <- getTTermVars
     cn <- getConflictNames
     i <- maybeToProof (HypoE h) $ getHypoPosition cn n h
     c <- getTermContext
     let (x,y,t,t') = S.index c i
     btc <- getBTypeContext
     ftc <- getFTypeContext
     let (r,r') = unfoldComm btc ftc op m (t,t') (tt,tt')
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
                 modifyTerm $ addDHT (\x y -> ((Free $ NGlobal "intro_bottom")
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
            replaceType $ typeSubs 1 btc ftc op (t,t') [ty']
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
     op <- getUsrOpers
     replaceType (renamedValidType (bTypeVar v S.<| btc) ftc op t, positiveShift 1 t')
     modifyTerm $ addHT (\x -> Unpack v (Bound i) x)
elimComm i (t,t') (RenameTy _ _ [t1,t2], RenameTTy n [t1',t2'])
  | n == and_code =
      do replaceType (Fun t1 (Fun t2 t), TFun t1' (TFun t2' t'))
         modifyTerm $ addHT (\x -> ((Free $ NGlobal "elim_and")
                                     :!: (t1,t1') :!: (t2,t2') :!: (t,t'))
                                   :@: (Bound i) :@: x)
  | n == or_code =
      do newSubProofs 2 [ Just (Fun t1 t, TFun t1' t')
                        , Just (Fun t2 t, TFun t2' t') ]
         modifyTerm $ addDHT (\x y -> ((Free $ NGlobal "elim_or")
                                        :!: (t1,t1') :!: (t2,t2') :!: (t,t'))
                                      :@: (Bound i) :@: x :@: y)
  | otherwise =
      throw ElimE1
elimComm i t (RenameTy _ _ [], RenameTTy n [])
  | n == bottom_code =
      do endSubProof
         modifyTerm $ simplify $ (Free $ NGlobal "elim_bottom") :!: t :@: (Bound i)
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

exactTerm :: (LamTerm, Term) -> (Type, TType) -> Proof ()
exactTerm te (tt, tt') =
  do c <- getTermContext
     teo <- getTheorems
     q <- getTBTypeVars
     op <- getUsrOpers
     (_,t') <- eitherToProof $ typeInference q c teo op te
     unless (t' == tt') $ throw $ ExactE1 tt
     endSubProof
     modifyTerm $ simplify (snd te)

----------------------------------------------------------------------------------------------------------------------
-- Comando UNFOLD

-- Argumentos:
-- 1. Contexto de variables de tipos ligadas.
-- 2. Contexto de variables de tipos libres.
-- 3. Código de la operación a "unfoldear".
-- 4. Tipo (con y sin nombre) sobre el que se aplica el unfold.
-- 5. Tipo (con y sin nombre) que define al operador foldeado (sin los para todos).
unfoldComm :: BTypeContext -> FTypeContext -> FOperations -> Int -> (Type, TType) -> (Type, TType) -> (Type, TType)
unfoldComm _ _ _ _ t@(B _, _) _ = t
unfoldComm btc ftc op code (RenameTy s l ts, RenameTTy m ts') body
  | m == code = typeSubs l btc ftc op body mapUnfoldComm
  | otherwise = let (xs, ys) = unzip mapUnfoldComm
                in (RenameTy s l xs, RenameTTy m ys)
    where mapUnfoldComm = map (\x -> unfoldComm btc ftc op code x body) $ zip ts ts'
unfoldComm btc ftc op code (Fun t t', TFun tt tt') body =
  let (t1,t1') = unfoldComm btc ftc op code (t,tt) body 
      (t2,t2') = unfoldComm btc ftc op code (t',tt') body
  in (Fun t1 t2, TFun t1' t2')
unfoldComm btc ftc op code (ForAll v t, TForAll t') body =
  let (t1, t1') = unfoldComm (bTypeVar v S.<| btc) ftc op code (t,t') body
  in (ForAll v t1, TForAll t1')
unfoldComm btc ftc op code (Exists v t, TExists t') body =
  let (t1, t1') = unfoldComm (bTypeVar v S.<| btc) ftc op code (t,t') body
  in (Exists v t1, TExists t1')

----------------------------------------------------------------------------------------------------------------------
-- Funciones auxiliares de "habitar".

-- Obtiene el tipo de la variable de término, renombrando su tipo sin nombres, de acuerdo
-- a la profundidad dada por el 1º argumento.
getTypeVar :: Int -> TermVarWithType -> (Type, TType)
getTypeVar n (_,m, t, t') = (t, positiveShift (n-m) t')

maybeToProof :: ProofExceptions -> Maybe a -> Proof a
maybeToProof excep Nothing = throw excep
maybeToProof _ (Just val) = return val

eitherToProof :: Either ProofExceptions a -> Proof a
eitherToProof (Left e) = throw e
eitherToProof (Right x) = return x
