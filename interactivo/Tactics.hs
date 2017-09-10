module Tactics where

import Common
import LambdaTermDefinition (LamDefs)
import TypeDefinition (TypeDefs, getTypeData)
import Proof
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
import Data.Foldable (find)


-- Contruye la prueba.
habitar :: Tactic -> Proof ()
habitar Assumption =
  do x <- getType
     t <- maybeToProof EmptyType x 
     c <- getTermContext
     q <- getTBTypeVars
     i <- maybeToProof AssuE $ S.findIndexL (\(_,p,t') -> positiveShift (q - p) t' == t) c
     endSubProof
     modifyTerm $ simplifyLTerm $ LVar $ Bound i
habitar Intro =
  do x <- getType
     introComm x
habitar Intros =
  introsComm
habitar (Apply h) =
  do x <- getType
     t <- maybeToProof EmptyType x
     n <- getTTermVars
     cn <- getConflictNames
     i <- maybeToProof (HypoE h) $ getHypoPosition cn n h
     c <- getTermContext
     q <- getTBTypeVars
     applyComm i t (getTypeVar q $ S.index c i)
habitar (Elim h) =
  do x <- getType
     t <- maybeToProof EmptyType x
     n <- getTTermVars
     cn <- getConflictNames
     i <- maybeToProof (HypoE h) $ getHypoPosition cn n h
     c <- getTermContext
     q <- getTBTypeVars
     elimComm i t (getTypeVar q $ S.index c i)
habitar CLeft =
  do x <- getType
     case x of
       Just (RenamedType s [t1,t2]) ->
         if s == or_id
         then do replaceType t1
                 modifyTerm $ addHT (\x -> ((LVar $ Free "intro_or1")
                                             :!: t1 :!: t2)
                                           :@: x)
         else throw CommandInvalid
       _ -> throw CommandInvalid
habitar CRight =
  do x <- getType
     case x of
       Just (RenamedType s [t1,t2]) ->
         if s == or_id
         then do replaceType t2
                 modifyTerm $ addHT (\x -> ((LVar $ Free "intro_or2")
                                             :!: t1 :!: t2)
                                           :@: x)
         else throw CommandInvalid
       _ -> throw CommandInvalid
habitar Split =
  do x <- getType
     case x of
       Just (RenamedType s [t1,t2]) ->
         if s == and_id
         then do newSubProofs 2 [Just t1, Just t2]
                 modifyTerm $ addDHT (\x y -> ((LVar $ Free "intro_and")
                                                :!: t1 :!: t2)
                                              :@: x :@: y)
         else throw CommandInvalid
       _ -> throw CommandInvalid
habitar (Exact (LamT te)) =
  do x <- getType
     tt <- maybeToProof EmptyType x
     op <- getTypeDefinitions
     n <- getTTermVars
     cn <- getConflictNames
     btc <- getBTypeContext
     ftc <- getFTypeContext
     ld <- getLamDefinitions
     te' <- eitherToProof $ withoutName op ftc btc (cn,n) ld te
     exactTerm te' tt  
habitar (Exact (T ty)) =
  do x <- getType
     when (isJust x) $ throw $ ExactE2 $ fromJust x
     op <- getTypeDefinitions
     btc <- getBTypeContext
     ftc <- getFTypeContext
     ld <- getLamDefinitions
     ty' <- eitherToProof $ renamedType2 btc ftc op ld ty
     exactType ty'     
habitar (Exact (Appl aps)) =
  do op <- getTypeDefinitions
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
         do when (isJust x) $ throw $ ExactE2 $ fromJust x
            exactType ty
habitar (Unfold s Nothing) =
  do x <- getType
     t <- maybeToProof EmptyType x
     op <- getTypeDefinitions
     (tt, _, _) <- maybeToProof (UnfoldE1 s) $ getTypeData s op
     btc <- getBTypeContext
     ftc <- getFTypeContext
     ld <- getLamDefinitions
     replaceType $ unfoldComm btc ftc op ld s t tt
habitar (Unfold s (Just h)) =
  do op <- getTypeDefinitions
     (tt, _, _) <- maybeToProof (UnfoldE1 s) $ getTypeData s op
     n <- getTTermVars
     cn <- getConflictNames
     i <- maybeToProof (HypoE h) $ getHypoPosition cn n h
     c <- getTermContext
     let (x,y,t) = S.index c i
     btc <- getBTypeContext
     ftc <- getFTypeContext
     ld <- getLamDefinitions
     let r = unfoldComm btc ftc op ld s t tt
     updateTermContext i (x,y,r)
habitar (Absurd ty) =
  do x <- getType
     case x of
       Just (RenamedType s []) ->
         if s == bottom_id
         then do op <- getTypeDefinitions
                 btc <- getBTypeContext
                 ftc <- getFTypeContext
                 ld <- getLamDefinitions
                 tty <- eitherToProof $ renamedType2 btc ftc op ld ty
                 newSubProofs 2 [ Just tty
                                , Just (RenamedType not_id [tty]) ]
                 modifyTerm $ addDHT (\x y -> ((LVar $ Free "intro_bottom")
                                                :!: tty)
                                              :@: x :@: y)
         else throw CommandInvalid
       _ -> throw CommandInvalid
habitar (CExists ty) =
  do x <- getType
     case x of
       Just tt@(Exists v t) ->
         do op <- getTypeDefinitions
            btc <- getBTypeContext
            ftc <- getFTypeContext
            ld <- getLamDefinitions
            ty' <- eitherToProof $ renamedType2 btc ftc op ld ty
            replaceType $ typeSubs 1 btc ftc op ld t [ty']
            modifyTerm $ addHT (\x -> EPack ty' x tt)
       _ -> throw CommandInvalid
habitar (Cut ty) =
  do x <- getType
     t <- maybeToProof EmptyType x
     op <- getTypeDefinitions
     btc <- getBTypeContext
     ftc <- getFTypeContext
     ld <- getLamDefinitions
     tty <- eitherToProof $ renamedType2 btc ftc op ld ty
     newSubProofs 2 [ Just (Fun tty t)
                    , Just tty ]
     modifyTerm $ addDHT (\x y -> x :@: y)

----------------------------------------------------------------------------------------------------------------------
-- Comando INTRO e INTROS

introComm :: Maybe DoubleType -> Proof ()
introComm (Just (Fun t1 t2)) =
  do modifyTVars (+1)
     q <- getTBTypeVars
     tv <- getTVars
     addTermContext (tv, q, t1)
     replaceType t2
     modifyTerm $ addHT (\x -> Abs () t1 x)
introComm (Just (ForAll v t)) =
  do modifyTVars (+1)
     tv <- getTVars
     addBTypeContext (tv, v)
     replaceType t
     modifyTerm $ addHT (\x -> BAbs v x)
introComm Nothing = throw EmptyType
introComm _ = throw IntroE1

-- Implementamos el comando INTROS, como una secuencia de comandos INTRO.
-- Cuando falla el último INTRO, se recupera el estado previo al error mediante catch.
introsComm :: Proof ()
introsComm = catch (do habitar Intro
                       introsComm)
             ((\e -> return ()) :: SemanticException -> Proof ())

----------------------------------------------------------------------------------------------------------------------
-- Comando ELIM

-- Asumimos que las tuplas del 2º arg. , tienen la forma correcta.
elimComm :: Int -> DoubleType -> DoubleType -> Proof ()
elimComm i t (Exists v tt) =
  do modifyTVars (+1)
     tv <- getTVars
     addBTypeContext (tv, v)
     modifyTVars (+1)
     q <- getTBTypeVars
     tv <- getTVars
     addTermContext (tv, q, tt)
     btc <- getBTypeContext
     ftc <- getFTypeContext
     op <- getTypeDefinitions
     ld <- getLamDefinitions
     replaceType $ renamedValidType1 1 (bTypeVar v S.<| btc) ftc op ld t
     modifyTerm $ addHT (\x -> EUnpack v () (LVar $ Bound i) x)
elimComm i t (RenamedType s [t1,t2])
  | s == and_id =
      do replaceType (Fun t1 (Fun t2 t))
         modifyTerm $ addHT (\x -> ((LVar $ Free "elim_and")
                                     :!: t1 :!: t2 :!: t)
                                   :@: (LVar $ Bound i) :@: x)
  | s == or_id =
      do newSubProofs 2 [ Just (Fun t1 t)
                        , Just (Fun t2 t) ]
         modifyTerm $ addDHT (\x y -> ((LVar $ Free "elim_or")
                                        :!: t1 :!: t2 :!: t)
                                      :@: (LVar $ Bound i) :@: x :@: y)
  | otherwise =
      throw ElimE1
elimComm i t (RenamedType s [])
  | s == bottom_id =
      do endSubProof
         modifyTerm $ simplifyLTerm $ (LVar $ Free "elim_bottom") :!: t :@: (LVar $ Bound i)
  | otherwise =
      throw ElimE1
elimComm _ _ _ = throw ElimE1

----------------------------------------------------------------------------------------------------------------------
-- Comando APPLY

applyComm :: Int -> DoubleType -> DoubleType -> Proof ()
applyComm i x ht@(Fun _ _) = 
  do n <- compareTypes ht x
     evaluateSubProof n $ getTypesFun n ht
     modifyTerm $ getApplyTermFun n i
applyComm i x ht@(ForAll _ _) =
  do let equal = ht == x
         (ft, n) = getNestedTypeForAll equal ht
     r <- eitherToProof $ unification equal n ft x
     let m = n - M.size r
     evaluateSubProof m $ getTypesForAll m
     modifyTerm $ getApplyTermForAll n r (LVar $ Bound i)
applyComm i x t
  | t == x = do evaluateSubProof 0 []
                modifyTerm $ simplifyLTerm (LVar $ Bound i)
  | otherwise = throw $ ApplyE1 t x
  

-- Funciones auxiliares para la función applyComm'

compareTypes :: DoubleType -> DoubleType -> Proof Int
compareTypes x y
 | x == y = return 0
 | otherwise =  compareTypes' x y

compareTypes' :: DoubleType -> DoubleType -> Proof Int
compareTypes' (Fun _ x) t
  | x == t = return 1
  | otherwise = do n <- compareTypes' x t
                   return $ n + 1
compareTypes' x y = throw $ ApplyE1 x y


getTypesFun :: Int -> DoubleType -> [Maybe DoubleType]
getTypesFun n (Fun t1 t2)
  | n > 0 = Just t1 : getTypesFun (n-1) t2
  | otherwise = error "error: getTypesFun, no debería pasar 1."
getTypesFun 0 _ = []
getTypesFun _ _ = error $ "error: getTypesFun, no debería pasar 2."


getNestedTypeForAll :: Bool -> DoubleType -> (DoubleType, Int)
getNestedTypeForAll flag x
  | flag = (x, 0)
  | otherwise = getNestedTypeForAll' x

getNestedTypeForAll' :: DoubleType -> (DoubleType, Int)
getNestedTypeForAll' (ForAll _ x) = let (f, n) = getNestedTypeForAll' x
                                    in (f, n+1)
getNestedTypeForAll' x = (x,0)

getApplyTermFun :: Int -> Int -> LTermHoles -> LTermHoles
getApplyTermFun 0 i ts = simplifyLTerm (LVar $ Bound i) ts
getApplyTermFun 1 i ts = addHT (\x -> (LVar $ Bound i) :@: x) ts
getApplyTermFun 2 i ts = addDHT (\x y -> ((LVar $ Bound i) :@: x) :@: y) ts
getApplyTermFun n i ts = getApplyTermFun (n-1) i $ addDHT (\x y -> x :@: y) ts


repeatElem :: Int -> a -> [a]
repeatElem n x
  | n == 0 = []
  | n > 0 = x : repeatElem (n-1) x
  | otherwise = error "error: repeatElem, no debería pasar."

getTypesForAll :: Int -> [Maybe DoubleType]
getTypesForAll m = repeatElem m Nothing

getApplyTermForAll :: Int -> M.Map Int DoubleType -> LTerm2 -> LTermHoles -> LTermHoles
getApplyTermForAll n sust t =
  addTypeHoleInTerm $ termForAll n t sust

termForAll :: Int -> LTerm2 -> M.Map Int DoubleType -> LTerm2Holes
termForAll n t sust
  | n == 0 = Term1 t
  | n > 0 = termForAll' 0 (n-1) (Term1 t) sust
  | otherwise = error "error: termForAll, no deberia pasar."

termForAll' :: Int -> Int -> LTerm2Holes -> M.Map Int DoubleType  -> LTerm2Holes
termForAll' n m t sust
  | n < 0 = error "error: termForAll', no deberia pasar."
  | otherwise =
    case M.lookup n sust of
      Nothing ->let tt = addTypeHole t
                in if n == m
                   then tt
                   else termForAll' (n+1) m tt sust
      Just x -> let tt = addTypeTerm x t
                in if n == m
                   then tt
                   else termForAll' (n+1) m tt sust

----------------------------------------------------------------------------------------------------------------------
-- Comando EXACT

exactType :: DoubleType -> Proof ()
exactType ty =
  endSubProof >>
  (modifyTerm $ simplifyType ty)

exactTerm :: DoubleLTerm -> DoubleType -> Proof ()
exactTerm te tt =
  do c <- getTermContext
     ld <- getLamDefinitions
     q <- getTBTypeVars
     op <- getTypeDefinitions
     t <- eitherToProof $ typeInference q c ld op te
     unless (t == tt) $ throw $ ExactE1 tt
     endSubProof
     modifyTerm $ simplifyLTerm $ toNoName te

----------------------------------------------------------------------------------------------------------------------
-- Comando UNFOLD

-- Argumentos:
-- 1. Contexto de variables de tipos ligadas.
-- 2. Contexto de variables de tipos libres.
-- 3. Operaciones "foldeables".
-- 4. Teoremas.
-- 5. Nombre de la operación a "unfoldear".
-- 6. Tipo sobre el que se aplica el unfold.
-- 7. Tipo que define al operador foldeado (sin los para todos).
unfoldComm :: BTypeContext -> FTypeContext -> TypeDefs -> LamDefs
           -> String -> DoubleType -> DoubleType -> DoubleType
unfoldComm _ _ _ _ _ t@(TVar _) _ = t
unfoldComm btc ftc op te oper (RenamedType s ts) body
  | s == oper = typeSubs (length ts) btc ftc op te body mapUnfoldComm
  | otherwise = let xs = mapUnfoldComm
                in RenamedType s xs
    where mapUnfoldComm = map (\x -> unfoldComm btc ftc op te oper x body) ts
unfoldComm btc ftc op te oper (Fun t t') body =
  let t1 = unfoldComm btc ftc op te oper t body 
      t2 = unfoldComm btc ftc op te oper t' body
  in Fun t1 t2
unfoldComm btc ftc op te oper (ForAll v t) body =
  let t' = unfoldComm (bTypeVar v S.<| btc) ftc op te oper t body
  in (ForAll v t')
unfoldComm btc ftc op te oper (Exists v t) body =
  let t' = unfoldComm (bTypeVar v S.<| btc) ftc op te oper t body
  in (Exists v t')

----------------------------------------------------------------------------------------------------------------------
-- Funciones auxiliares de "habitar".

-- Obtiene el tipo de la variable de término, renombrando su tipo sin nombre, de acuerdo
-- a la profundidad dada por el 1º argumento.
getTypeVar :: Int -> TermVarWithType -> DoubleType
getTypeVar n (_,m, t) = positiveShift (n-m) t

maybeToProof :: SemanticException -> Maybe a -> Proof a
maybeToProof excep Nothing = throw excep
maybeToProof _ (Just val) = return val

eitherToProof :: Either SemanticException a -> Proof a
eitherToProof (Left e) = throw e
eitherToProof (Right x) = return x
