import System.Environment
import System.Console.Haskeline
import Asistente
import Parser
import Common hiding (State, catch, get)
import Text.PrettyPrint.HughesPJ (render)
import PrettyPrinter (printTerm, printProof, printType, printTType, printTermTType)
import System.Console.Haskeline.MonadException
import Control.Monad.Trans.Class
import Control.Monad.State.Strict
import Control.Monad.IO.Class
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Sequence as S
import Data.List (findIndex, elemIndex)

type ProverInputState a = InputT (StateT ProverState IO) a

-- instance MonadState ProverState ProverInputState where
--      get = lift . get
--      put = lift . put

operations :: [String]
operations = [and_op, or_op]


initialT' = [ ("intro_and", intro_and),
              ("elim_and", elim_and),
              ("intro_or1", intro_or1),
              ("intro_or2", intro_or2),
              ("elim_or", elim_or)
            ]

initialT = Map.fromList initialT'


main :: IO ()
main = do args <- getArgs
          if args == []
            then evalStateT (runInputT defaultSettings prover) initProverState
            else do putStrLn "aviso: hay argumentos!" --Tratar
                    evalStateT (runInputT defaultSettings prover) initProverState


initProverState :: ProverState
initProverState = PSt {global=PGlobal {teorems=initialT, fTContext=[], opers=operations}, proof=Nothing}


prover :: ProverInputState ()
prover = do minput <- getInputLine "> "
            case minput of
              Nothing -> return ()
              Just "-quit" -> do outputStrLn "Saliendo."
                                 return ()
              Just "-r" -> resetProof
              Just "" -> prover
              Just x -> catch (do command <- returnInput $ getCommand x
                                  checkCommand command) (\e -> errorMessage (e :: ProofExceptions) >> prover)

newProof :: ProverGlobal -> String -> Type -> TType -> ProofState
newProof pglobal name ty tty =
  let c = PConstruction { bTContexts = [S.empty]
                        , termContexts = [S.empty]
                        , ty=[Just (ty, tty)]
                        , term=[HoleT id]
                        , tsubp=1
                        , lsubp=[1]
                        , tvars = [length $ fTContext $ pglobal]
                        , cglobal = pglobal
                        }
  in PState { name = name
            , types = (ty, tty)
            , constr = c
            }

renderFinalTerm :: ProofConstruction -> String
renderFinalTerm p = render $ printTerm $ getTermFromProof p

--PRUEBA
renderFinalTermWithoutName :: [String] -> ProofConstruction -> String
renderFinalTermWithoutName op p = render $ printTermTType op $ getTermFromProof p

renderProof :: ProofConstruction -> String
renderProof p = render $ printProof (tsubp p) (fTContext $ cglobal p) (head $ bTContexts p) (head $ termContexts p) (ty p)

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
                               let glo = global s
                               when (Map.member name (teorems $ glo)) (throwIO $ PExist name)
                               (tyr,tty) <- returnInput $ rename (fTContext glo) (opers glo) ty
                               let p = newProof glo name tyr tty
                               lift $ put $ PSt {global=glo, proof=Just p}
                               outputStrLn $ renderProof $ constr p
                               prover
                               
checkCommand (Props ps) = do s <- lift get
                             when (isJust $ proof s) (throwIO PNotFinished)
                             let gps = fTContext $ global s
                             let pr1 = propRepeated1 ps
                             let pr2 = propRepeated2 ps gps
                             when (isJust pr1) (throwIO $ PropRepeated1 $ fromJust pr1)
                             when (isJust pr2) (throwIO $ PropRepeated2 $ fromJust pr2)
                             lift $ put $ s {global = (global s) {teorems=teorems $ global s, fTContext=ps++gps}}
                             prover

-- TERMINAR
-- checkCommand (TypeDef (op, flagInfix, t)) = 

checkCommand (Ta (Print x)) = do s <- lift get
                                 let ter = teorems $ global s
                                 when (Map.notMember x ter) (throwIO $ PNotExist x)
                                 outputStrLn $ render $ printTerm $ fst $ ter Map.! x
                                 prover

checkCommand (Ta (Infer x)) = do s <- lift get
                                 outputStrLn $ show x ++ "\n"         -- Borrar SHOW
                                 te <- returnInput $ withoutName (opers $ global s) 0 (fTContext $ global s, S.empty) x
                                 outputStrLn $ show te ++ "\n"
                                 (ty,ty') <- returnInput $ inferType 0 S.empty (teorems $ global s) te
                                 outputStrLn $ render $ printType ty
                                 outputStrLn $ render $ printTType (opers $ global s) ty'
                                 prover
                                 
checkCommand (Ta ta) = do  s <- lift get
                           when (isNothing $ proof s) (throwIO PNotStarted)
                           let pr = fromJust $ proof s
                           (_ , p) <- returnInput $ runStateExceptions (habitar ta) (constr $ pr)
                           lift $ put $ s {proof = Just $ pr {constr = p}}
                           if (isFinalTerm p)
                             then ((outputStrLn $ "Prueba completa.\n"
                                     ++ renderFinalTerm p ++ "\n"
                                     ++ renderFinalTermWithoutName (opers $ global s) p ++ "\n"
                                     ++ show (getTermFromProof p) ++ "\n") -- Borrar SHOWs
                                   >> reloadProver)
                             else (outputStrLn (renderProof p) >> (outputStrLn $ show $ length $ term p))
                           prover

resetProof :: ProverInputState ()
resetProof = do s <- lift get
                lift $ put $ PSt {global=global s, proof=Nothing}
                prover

reloadProver :: ProverInputState ()
reloadProver = do s <- lift get
                  let p = fromJust $ proof s
                  lift $ put $ PSt { global= (global s)
                                             {teorems=Map.insert (name p)
                                                    (getTermFromProof (constr p), types p)
                                                    (teorems $ global s)}
                                   , proof = Nothing
                                   }

isFinalTerm :: ProofConstruction -> Bool
isFinalTerm (PConstruction {term=[Term _]}) = True
isFinalTerm _ = False

getTermFromProof :: ProofConstruction -> Term
getTermFromProof (PConstruction {term=[Term t]}) = t
getTermFromProof _ = error "getTermFromProof: no debería pasar"


returnInput :: Either ProofExceptions a -> ProverInputState a
returnInput (Left exception) = throwIO exception
returnInput (Right x) = return x


errorMessage :: ProofExceptions -> ProverInputState ()
errorMessage SyntaxE = outputStrLn "error de sintaxis."
errorMessage PNotFinished = outputStrLn "error: prueba no terminada."
errorMessage PNotStarted = outputStrLn "error: prueba no comenzada."
errorMessage (PExist s) = outputStrLn $ "error: " ++ s ++ " ya existe."
errorMessage (PNotExist s) = outputStrLn $ "error: " ++ s ++ " no existe."
errorMessage AssuE = outputStrLn "error: comando assumption mal aplicado."
errorMessage IntroE1 = outputStrLn "error: comando intro mal aplicado."
errorMessage (ApplyE1 t1 t2) =
  outputStrLn $ "error: comando apply mal aplicado, \"" ++
  (render $ printType t1) ++  "\" no coincide con \"" ++
  (render $ printType t2) ++ "\"."
errorMessage ApplyE2 = outputStrLn "error: comando apply, hipótesis no existe."
errorMessage Unif1 = outputStrLn "error: unificación inválida 1."
errorMessage Unif2 = outputStrLn "error: unificación inválida 2."
errorMessage Unif3 = outputStrLn "error: unificación inválida 3."
errorMessage Unif4 = outputStrLn "error: unificación inválida 4."
errorMessage ElimE1 = outputStrLn "error: comando elim mal aplicado."
errorMessage CommandInvalid = outputStrLn "error: comando inválido."
errorMessage EmptyType = outputStrLn "error: comando inválido (debe añadir una fórmula mediante \"exact\")."
errorMessage (PropRepeated1 s) = outputStrLn $ "error: proposición \""++ s ++"\" repetida."
errorMessage (PropRepeated2 s) = outputStrLn $ "error: proposición \""++ s ++"\" ya existe."
errorMessage (PropNotExists s) = outputStrLn $ "error: proposición \""++ s ++"\" no existe en el entorno."
errorMessage (OpE s) = outputStrLn $ "error: la operación \""++ s ++"\" no existe."
errorMessage (ExactE1 ty) = outputStrLn $ "error: el término ingresado no tiene el tipo \"" ++ render (printType ty) ++ "\". "
errorMessage (ExactE2 ty) = outputStrLn $ "error: debe ingresar una prueba de \"" ++ render (printType ty) ++ "\". "
errorMessage PSE = outputStrLn "error: operación sobre el estado interno inválida"
errorMessage (TermE x) = outputStrLn $ "error: el tipo \"" ++ x ++ "\" no fue declarado."
errorMessage (InferE1 x) = outputStrLn $ "error: la variable de término \"" ++ x ++ "\" no fue declarada."
errorMessage (InferE2 ty) = outputStrLn $ errorInferPrintTerm ty ++ "El tipo no unifica con la función."
errorMessage (InferE3 ty) = outputStrLn $ errorInferPrintTerm ty ++ "El tipo no es una función."
errorMessage (InferE4 ty) = outputStrLn $ errorInferPrintTerm ty ++ "El tipo no es un para todo."

errorInferPrintTerm :: Type -> String
errorInferPrintTerm ty =
  "error: no se esperaba el tipo \"" ++ render (printType ty) ++ "\". "
