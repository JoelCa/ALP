module Tactics where

import Common
import LambdaTermDefinition (LamDefs)
import TypeDefinition (TypeDefs, getTypeData)
import Proof
import TermsWithHoles
import Hypothesis
import Transformers
import TypeInference (typeInference, fullEqualTypes)
import TypeUnification (unification)
import TypeSubstitution (typeSubs)
import Control.Monad (unless, when)
import qualified Data.Map.Strict as M (Map, lookup, size)
import Data.Maybe (fromJust, isJust)
import qualified Data.Sequence as S


-- Contruye la prueba a partir de la táctica.
habitar :: Tactic -> Proof ()
habitar Assumption =
  do x <- getType
     t <- maybeToProof EmptyType x 
     c <- getTermContext
     q <- getTBTypeVars
     (i,hy) <- maybeToProof AssuE $
               S.foldrWithIndex (\index (h,_,p,Just t') r -> if positiveShift (q - p) t' == t then return (index,h) else r) Nothing c
     endSubProof
     modifyTerm $ simplifyLTerm $ LVar (hy, Bound i)
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
     c <- getTermContext
     i <- maybeToProof (HypoE h) $ getHypoPosition (c,n) cn h
     q <- getTBTypeVars
     applyComm (hypothesis h cn) i t (renameType q $ S.index c i)
habitar (Elim h) =
  do x <- getType
     t <- maybeToProof EmptyType x
     n <- getTTermVars
     cn <- getConflictNames
     c <- getTermContext
     i <- maybeToProof (HypoE h) $ getHypoPosition (c,n) cn h
     q <- getTBTypeVars
     elimComm (hypothesis h cn) i t (renameType q $ S.index c i)
habitar CLeft =
  do x <- getType
     case x of
       Just (RenamedType s [t1,t2]) ->
         if s == or_id
         then do replaceType t1
                 modifyTerm $ addHT (\x -> ((LVar ("intro_or1", Free "intro_or1"))
                                             :!: t1 :!: t2)
                                           :@: x)
         else throw InvalidCommand
       _ -> throw InvalidCommand
habitar CRight =
  do x <- getType
     case x of
       Just (RenamedType s [t1,t2]) ->
         if s == or_id
         then do replaceType t2
                 modifyTerm $ addHT (\x -> ((LVar ("intro_or2", Free "intro_or2"))
                                             :!: t1 :!: t2)
                                           :@: x)
         else throw InvalidCommand
       _ -> throw InvalidCommand
habitar Split =
  do x <- getType
     case x of
       Just (RenamedType s [t1,t2]) ->
         if s == and_id
         then do newSubProofs 2 [Just t1, Just t2]
                 modifyTerm $ addDHT (\x y -> ((LVar ("intro_and", Free "intro_and"))
                                                :!: t1 :!: t2)
                                              :@: x :@: y)
         else throw InvalidCommand
       _ -> throw InvalidCommand
habitar (Exact (LamT te)) =
  do x <- getType
     tt <- maybeToProof EmptyType x
     op <- getTypeDefinitions
     n <- getTTermVars
     btc <- getBTypeContext
     ftc <- getFTypeContext
     ld <- getLamDefinitions
     c <- getTermContext
     te' <- eitherToProof $ withoutName (n+1) btc c op ftc ld te
     exactTerm te' tt  
habitar (Exact (T ty)) =
  do x <- getType
     when (isJust x) $ throw $ ExactE2 $ fromJust x
     op <- getTypeDefinitions
     btc <- getBTypeContext
     ftc <- getFTypeContext
     ld <- getLamDefinitions
     c <- getTermContext
     ty' <- eitherToProof $ renamedType2 btc c ftc op ld ty
     exactType ty'     
habitar (Exact (Appl aps)) =
  do op <- getTypeDefinitions
     btc <- getBTypeContext
     ftc <- getFTypeContext
     c <- getTermContext
     t <- eitherToProof $ disambiguatedTerm c btc ftc op aps
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
     c <- getTermContext
     i <- maybeToProof (HypoE h) $ getHypoPosition (c,n) cn h
     let (x,y,z,Just t) = S.index c i
     btc <- getBTypeContext
     ftc <- getFTypeContext
     ld <- getLamDefinitions
     let r = unfoldComm btc ftc op ld s t tt
     updateTermContext i (x,y,z,Just r)
habitar (Absurd ty) =
  do x <- getType
     case x of
       Just (RenamedType s []) ->
         if s == bottom_id
         then do op <- getTypeDefinitions
                 btc <- getBTypeContext
                 ftc <- getFTypeContext
                 ld <- getLamDefinitions
                 c <- getTermContext
                 tty <- eitherToProof $ renamedType2 btc c ftc op ld ty
                 newSubProofs 2 [ Just tty
                                , Just (RenamedType not_id [tty]) ]
                 modifyTerm $ addDHT (\x y -> ((LVar ("intro_bottom", Free "intro_bottom"))
                                                :!: tty)
                                              :@: x :@: y)
         else throw InvalidCommand
       _ -> throw InvalidCommand
habitar (CExists ty) =
  do x <- getType
     case x of
       Just tt@(Exists _ t) ->
         do op <- getTypeDefinitions
            btc <- getBTypeContext
            ftc <- getFTypeContext
            ld <- getLamDefinitions
            c <- getTermContext
            ty' <- eitherToProof $ renamedType2 btc c ftc op ld ty
            replaceType $ typeSubs 1 btc ftc op ld t [ty']
            modifyTerm $ addHT (\x -> EPack ty' x tt)
       _ -> throw InvalidCommand
habitar (Cut ty) =
  do x <- getType
     t <- maybeToProof EmptyType x
     op <- getTypeDefinitions
     btc <- getBTypeContext
     ftc <- getFTypeContext
     ld <- getLamDefinitions
     c <- getTermContext
     tty <- eitherToProof $ renamedType2 btc c ftc op ld ty
     newSubProofs 2 [ Just (Fun tty t)
                    , Just tty ]
     modifyTerm $ addDHT (\x y -> x :@: y)
habitar Show = return ()

----------------------------------------------------------------------------------------------------------------------
-- Comando INTRO e INTROS

introComm :: Maybe DoubleType -> Proof ()
introComm (Just (Fun t1 t2)) =
  do modifyTVars (+1)
     q <- getTBTypeVars
     tv <- getTVars
     to <- getTTermVars
     cn <- getConflictNames
     let h = hypothesis to cn
     addTermContext (h, tv, q, Just t1)
     replaceType t2
     modifyTerm $ addHT (\x -> Abs h t1 x)
introComm (Just (ForAll v t)) =
  do modifyTVars (+1)
     tv <- getTVars
     addBTypeContext (v, tv)
     addConflicNameInProof v
     replaceType t
     modifyTerm $ addHT (\x -> BAbs v x)
introComm Nothing = throw EmptyType
introComm _ = throw IntroE1

-- Implementamos el comando INTROS, como una secuencia de comandos INTRO.
-- Cuando falla el último INTRO, se recupera el estado previo al error mediante catch.
introsComm :: Proof ()
introsComm = catch (do habitar Intro
                       introsComm)
             ((\_ -> return ()) :: SemanticException -> Proof ())

----------------------------------------------------------------------------------------------------------------------
-- Comando ELIM

elimComm :: TermVar -> Int -> DoubleType -> DoubleType -> Proof ()
elimComm h i t (Exists v tt) =
  do modifyTVars (+1)
     tv <- getTVars
     addBTypeContext (v, tv)
     modifyTVars (+1)
     q <- getTBTypeVars
     tv <- getTVars
     to <- getTTermVars
     cn <- getConflictNames
     let hy = hypothesis (to - i) cn
     addTermContext (hy, tv, q, Just tt)
     btc <- getBTypeContext
     ftc <- getFTypeContext
     op <- getTypeDefinitions
     ld <- getLamDefinitions
     replaceType $ renamedValidType1 1 (typeVar0 v S.<| btc) ftc op ld t
     modifyTerm $ addHT (\x -> EUnpack v hy (LVar (h, Bound i)) x)
elimComm h i t (RenamedType s [t1,t2])
  | s == and_id =
      do replaceType (Fun t1 (Fun t2 t))
         modifyTerm $ addHT (\x -> ((LVar ("elim_and", Free "elim_and"))
                                     :!: t1 :!: t2 :!: t)
                                   :@: (LVar (h, Bound i)) :@: x)
  | s == or_id =
      do newSubProofs 2 [ Just (Fun t1 t)
                        , Just (Fun t2 t) ]
         modifyTerm $ addDHT (\x y -> ((LVar ("elim_and", Free "elim_or"))
                                        :!: t1 :!: t2 :!: t)
                                      :@: (LVar (h, Bound i)) :@: x :@: y)
  | otherwise =
      throw ElimE1
elimComm h i t (RenamedType s [])
  | s == bottom_id =
      do endSubProof
         modifyTerm $ simplifyLTerm $ (LVar ("elim_bottom", Free "elim_bottom")) :!: t :@: (LVar (h, Bound i))
  | otherwise =
      throw ElimE1
elimComm _ _ _ _ = throw ElimE1

----------------------------------------------------------------------------------------------------------------------
-- Comando APPLY

applyComm :: TermVar -> Int -> DoubleType -> DoubleType -> Proof ()
applyComm h i x ht@(Fun _ _) = 
  do n <- compareTypes ht x
     evaluateSubProof n $ getTypesFun n ht
     modifyTerm $ getApplyTermFun n h i
applyComm h i x ht@(ForAll _ _) =
  do let equal = ht == x
         (ft, n) = getNestedTypeForAll equal ht
     r <- eitherToProof $ unification equal n ft x
     let m = n - M.size r
     evaluateSubProof m $ getTypesForAll m
     modifyTerm $ getApplyTermForAll n r (LVar (h, Bound i))
applyComm h i x t
  | t == x = do evaluateSubProof 0 []
                modifyTerm $ simplifyLTerm (LVar (h, Bound i))
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

getApplyTermFun :: Int -> TermVar -> Int -> LTermHoles -> LTermHoles
getApplyTermFun 0 h i ts = simplifyLTerm (LVar (h, Bound i)) ts
getApplyTermFun 1 h i ts = addHT (\x -> (LVar (h, Bound i)) :@: x) ts
getApplyTermFun 2 h i ts = addDHT (\x y -> ((LVar (h, Bound i)) :@: x) :@: y) ts
getApplyTermFun n h i ts = getApplyTermFun (n-1) h i $ addDHT (\x y -> x :@: y) ts


repeatElem :: Int -> a -> [a]
repeatElem n x
  | n == 0 = []
  | n > 0 = x : repeatElem (n-1) x
  | otherwise = error "error: repeatElem, no debería pasar."

getTypesForAll :: Int -> [Maybe DoubleType]
getTypesForAll m = repeatElem m Nothing

getApplyTermForAll :: Int -> M.Map Int DoubleType -> DoubleLTerm -> LTermHoles -> LTermHoles
getApplyTermForAll n sust t =
  addTypeHoleInTerm $ termForAll n t sust

termForAll :: Int -> DoubleLTerm -> M.Map Int DoubleType -> LTerm2Holes
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
     unless (fullEqualTypes op t tt) $ throw $ ExactE1 tt
     endSubProof
     modifyTerm $ simplifyLTerm te

----------------------------------------------------------------------------------------------------------------------
-- Comando UNFOLD

-- Argumentos:
-- 1. Contexto de variables de tipos ligadas.
-- 2. Contexto de variables de tipos libres.
-- 3. Tipos definidos.
-- 4. Lambda términos definidos.
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
  let t' = unfoldComm (typeVar0 v S.<| btc) ftc op te oper t body
  in (ForAll v t')
unfoldComm btc ftc op te oper (Exists v t) body =
  let t' = unfoldComm (typeVar0 v S.<| btc) ftc op te oper t body
  in (Exists v t')

----------------------------------------------------------------------------------------------------------------------
-- Funciones auxiliares de "habitar".

-- Obtiene el tipo de la variable de término, renombrando su tipo sin nombre, de acuerdo
-- a la profundidad dada por el 1º argumento.
renameType :: Int -> TermVarWithType -> DoubleType
renameType n (_, _, m, Just t) = positiveShift (n-m) t

maybeToProof :: SemanticException -> Maybe a -> Proof a
maybeToProof excep Nothing = throw excep
maybeToProof _ (Just val) = return val

eitherToProof :: Either SemanticException a -> Proof a
eitherToProof (Left e) = throw e
eitherToProof (Right x) = return x
