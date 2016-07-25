import System.Environment
import System.Console.Haskeline
import Asistente
import Parser
import Common
import Text.PrettyPrint.HughesPJ (render)
import PrettyPrinter (printTerm, printProof)
import System.Console.Haskeline.MonadException
import Control.Monad.Trans.Class
import Control.Monad.State.Strict
import Control.Monad.IO.Class
import Data.Maybe
  
type ProofInputState a = InputT (StateT (Maybe ProofState) IO) a


main :: IO ()
main = do args <- getArgs
          if args == []
            then evalStateT (runInputT defaultSettings prover) Nothing
            else do putStrLn "aviso: hay argumentos!" --Tratar
                    evalStateT (runInputT defaultSettings prover) Nothing


prover :: ProofInputState ()
prover = do minput <- getInputLine "> "
            s <- lift get
            when (isNothing s) (outputStrLn "Estado nulo")
            case minput of
              Nothing -> return ()
              Just "-quit" -> do outputStrLn "Saliendo."
                                 return ()
              Just "-r" -> resetProver >> prover  --"Reset"
              Just x -> catch (do command <- returnInput $ getCommand x
                                  checkCommand command) (\e -> errorMessage (e :: ProofExceptions) >> prover)


checkCommand :: Command -> ProofInputState ()
checkCommand (Ty ty) = do s <- lift get
                          when (isJust s) (throwIO PNotFinished)
                          outputStrLn $ render $ printProof 0 [] ty
                          lift $ put $ Just $ PState {position=0, context=[], ty=(ty, typeWithoutName ty), term=EmptyTerm id}
                          prover
checkCommand (Ta ta) = do  s <- lift get
                           when (isNothing s) (throwIO PNotStarted)
                           proof <- returnInput $ habitar (fromJust s) ta
                           lift $ put $ Just proof
                           if (isFinalTerm proof)
                             then (outputStrLn ("prueba terminada\n" ++ render (printTerm (getTermFromProof proof)))
                                    >> resetProver)
                             else outputStrLn $ render $ printProof (position proof) (context proof) (fst (ty proof))
                           prover


resetProver :: ProofInputState ()
resetProver = lift $ put Nothing

isFinalTerm :: ProofState -> Bool
isFinalTerm (PState {term=Term _}) = True
isFinalTerm _ = False

getTermFromProof :: ProofState -> Term
getTermFromProof (PState {term=Term t}) = t
getTermFromProof _ = error "getTermFromProof: no debería pasar"


returnInput :: Either ProofExceptions a -> ProofInputState a
returnInput (Left exception) = throwIO exception
returnInput (Right x) = return x


errorMessage :: ProofExceptions -> ProofInputState ()
errorMessage SyntaxE = outputStrLn "error sintaxis"
errorMessage PNotFinished = outputStrLn "error: prueba no terminada"
errorMessage PNotStarted = outputStrLn "error: prueba no comenzada"
errorMessage AssuE = outputStrLn "error: comando assumption mal aplicado"
errorMessage IntroE1 = outputStrLn "error: comando intro mal aplicado"
errorMessage IntroE2 = outputStrLn "error: comando intro, variable no tipo libre"
errorMessage ApplyE1 = outputStrLn "error: comando apply mal aplicado, función no coincide tipo"
errorMessage ApplyE2 = outputStrLn "error: comando apply mal aplicado, hipótesis no es función ni cuantificación"
errorMessage ApplyE3 = outputStrLn "error: comando apply, hipótesis no existe"
errorMessage Unif1 = outputStrLn "error: unificación inválida 1"
errorMessage Unif2 = outputStrLn "error: unificación inválida 2"
errorMessage Unif3 = outputStrLn "error: unificación inválida 3"
errorMessage Unif4 = outputStrLn "error: unificación inválida 4"
errorMessage CommandInvalid = outputStrLn "error: comando inválido"
