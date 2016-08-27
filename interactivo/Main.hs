import System.Environment
import System.Console.Haskeline
import Asistente
import Parser
import Common hiding (State)
import Text.PrettyPrint.HughesPJ (render)
import PrettyPrinter (printTerm, printProof)
import System.Console.Haskeline.MonadException
import Control.Monad.Trans.Class
import Control.Monad.State.Strict
import Control.Monad.IO.Class
import Data.Maybe
import qualified Data.Map as Map
import Data.List (findIndex, elemIndex)


type ProverInputState a = InputT (StateT ProverState IO) a

initialT' = [("intro_and", intro_and),
             ("elim_and", elim_and),
             ("intro_or1", intro_or1),
             ("intro_or2", intro_or2),
             ("elim_or", elim_or)]

initialT = Map.fromList initialT'


main :: IO ()
main = do args <- getArgs
          if args == []
            then evalStateT (runInputT defaultSettings prover) initProverState
            else do putStrLn "aviso: hay argumentos!" --Tratar
                    evalStateT (runInputT defaultSettings prover) initProverState


initProverState :: ProverState
initProverState = PSt {global=PGlobal {terms=initialT, props=[]}, proof=Nothing}


prover :: ProverInputState ()
prover = do minput <- getInputLine "> "
            case minput of
              Nothing -> return ()
              Just "-quit" -> do outputStrLn "Saliendo."
                                 return ()
              Just "-r" -> resetProof
              Just x -> catch (do command <- returnInput $ getCommand x
                                  checkCommand command) (\e -> errorMessage (e :: ProofExceptions) >> prover)


newProof :: String -> Type -> TType -> TypeContext -> ProofState
newProof name ty tty ps = PState {name=name, subp=1, position=[0], typeContext = [ps], context=[[]], ty=[(ty, tty)], term=[HoleT id]}

renderNewProof :: Type -> String
renderNewProof ty = render $ printProof 1 [0] [[]] [[]] [ty]

renderFinalTerm :: ProofState -> String
renderFinalTerm p = render $ printTerm $ getTermFromProof p

renderProof :: ProofState -> String
renderProof p = render $ printProof (subp p) (position p) (typeContext p) (context p) (map fst (ty p))


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


propRepeated2 :: [String] -> [String] -> Maybe String
propRepeated2 _ [] = Nothing
propRepeated2 [] _ = Nothing
propRepeated2 (p:ps) ps'
  | elem p ps' = return p
  | otherwise = propRepeated2 ps ps'
                
propRepeated1 :: [String] -> Maybe String
propRepeated1 [] = Nothing
propRepeated1 (p:ps)
  | elem p ps = return p
  | otherwise = propRepeated1 ps


checkCommand :: Command -> ProverInputState ()
checkCommand (Ty name ty) = do s <- lift get
                               when (isJust $ proof s) (throwIO PNotFinished)
                               when (Map.member name (terms $ global s)) (throwIO $ PExist name)
                               (tyr,tty) <- returnInput $ getRenameWhitException (props $ global s) ty
                               let p = newProof name tyr tty (props $ global s)
                               lift $ put $ PSt {global=global s, proof=Just  p}
                               outputStrLn $ renderProof p               
                               prover
                               
checkCommand(Props ps) = do s <- lift get
                            when (isJust $ proof s) (throwIO PNotFinished)
                            let gps = props $ global s
                            let pr1 = propRepeated1 ps
                            let pr2 = propRepeated2 ps gps
                            when (isJust pr1) (throwIO $ PropRepeated1 $ fromJust pr1)
                            when (isJust pr2) (throwIO $ PropRepeated2 $ fromJust pr2)
                            lift $ put $ PSt {global=PGlobal {terms=terms $ global s, props=ps++gps}, proof=proof s}
                            prover

checkCommand (Ta (Print x)) = do s <- lift get
                                 let ter = terms $ global s
                                 when (Map.notMember x ter) (throwIO $ PNotExist x)
                                 outputStrLn $ render $ printTerm $ ter Map.! x
                                 prover
                                 
checkCommand (Ta ta) = do  s <- lift get
                           when (isNothing $ proof s) (throwIO PNotStarted)
                           p <- returnInput $ habitar (fromJust $ proof s) ta
                           lift $ put $ PSt {global=global s, proof=Just p}
                           if (isFinalTerm p)
                             then ((outputStrLn $ "Prueba completa.\n" ++ renderFinalTerm p)
                                   >> reloadProver)
                             else outputStrLn $ renderProof p
                           prover

resetProof :: ProverInputState ()
resetProof = do s <- lift get
                lift $ put $ PSt {global=global s, proof=Nothing}
                prover

reloadProver :: ProverInputState ()
reloadProver = do s <- lift get
                  let p = fromJust $ proof s
                  lift $ put $ PSt {global=PGlobal {terms=Map.insert (name p) (getTermFromProof p) (terms $ global s),
                                                   props=props $ global s},
                                    proof=Nothing}

isFinalTerm :: ProofState -> Bool
isFinalTerm (PState {term=[Term _]}) = True
isFinalTerm _ = False

getTermFromProof :: ProofState -> Term
getTermFromProof (PState {term=[Term t]}) = t
getTermFromProof _ = error "getTermFromProof: no debería pasar"


returnInput :: Either ProofExceptions a -> ProverInputState a
returnInput (Left exception) = throwIO exception
returnInput (Right x) = return x


errorMessage :: ProofExceptions -> ProverInputState ()
errorMessage SyntaxE = outputStrLn "error sintaxis."
errorMessage PNotFinished = outputStrLn "error: prueba no terminada."
errorMessage PNotStarted = outputStrLn "error: prueba no comenzada."
errorMessage (PExist s) = outputStrLn $ "error: " ++ s ++ " ya existe."
errorMessage (PNotExist s) = outputStrLn $ "error: " ++ s ++ " no existe."
errorMessage AssuE = outputStrLn "error: comando assumption mal aplicado."
errorMessage IntroE1 = outputStrLn "error: comando intro mal aplicado."
errorMessage IntroE2 = outputStrLn "error: comando intro, variable no tipo libre."
errorMessage ApplyE1 = outputStrLn "error: comando apply mal aplicado, función no coincide tipo."
errorMessage ApplyE2 = outputStrLn "error: comando apply mal aplicado, hipótesis no es función ni cuantificación."
errorMessage ApplyE3 = outputStrLn "error: comando apply, hipótesis no existe."
errorMessage Unif1 = outputStrLn "error: unificación inválida 1."
errorMessage Unif2 = outputStrLn "error: unificación inválida 2."
errorMessage Unif3 = outputStrLn "error: unificación inválida 3."
errorMessage Unif4 = outputStrLn "error: unificación inválida 4."
errorMessage ElimE1 = outputStrLn "error: comando elim mal aplicado."
errorMessage CommandInvalid = outputStrLn "error: comando inválido."
errorMessage (PropRepeated1 s) = outputStrLn $ "error: proposición \""++ s ++"\" repetida."
errorMessage (PropRepeated2 s) = outputStrLn $ "error: proposición \""++ s ++"\" ya existe."
errorMessage (PropNotExists s) = outputStrLn $ "error: proposición \""++ s ++"\" no existe en el entorno."
