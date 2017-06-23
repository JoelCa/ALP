import Tactics (habitar)
import Parser
import Common hiding (State, catch, get)
import Text.PrettyPrint.HughesPJ (render)
import PrettyPrinter (printTerm, printProof, printType, printTType, printTermTType, printLamTerm)
import Rules
import Transformers
import ErrorMsj
import TypeInference (basicTypeInference)
import ProverState
import GlobalState
import Proof (ProofConstruction, getTermFromProof, isFinalTerm, cglobal, tsubp, subps)
import TermsWithHoles
import DefaultOperators
import System.Environment
import System.Console.Haskeline
import System.Console.Haskeline.MonadException
import Control.Monad.Trans.Class
import Control.Monad.State.Strict
import Control.Monad.IO.Class
import Data.Maybe
import Data.List (find, findIndex, elemIndex)
import qualified Data.Sequence as S

type ProverInputState a = InputT (StateT ProverState IO) a


-- Aborta la prueba.
resetProof :: ProverInputState ()
resetProof = lift $ modify $ finishProof
                
-- Finaliza la prueba.
reloadProver :: ProverInputState ()
reloadProver = lift $ modify $ finishProof . newTheoremFromProof


main :: IO ()
main = do args <- getArgs
          if args == []
            then evalStateT (runInputT defaultSettings prover) initialProver
            else do putStrLn "aviso: hay argumentos!" --Tratar
                    evalStateT (runInputT defaultSettings prover) initialProver


prover :: ProverInputState ()
prover = do s <- lift get
            minput <- getInputLine "> "
            case minput of
              Nothing -> return ()
              Just "-quit" -> do outputStrLn "Saliendo."
                                 return ()
              Just "-r" -> resetProof >> prover
              Just "" -> prover
              Just x -> catch (do command <- returnInput $ getCommand x (infixParser s)
                                  checkCommand command)
                        (\e -> outputStrLn (errorMessage (opers $ global s) (e :: ProofExceptions))
                               >> prover)


-- Tratamiento de los comandos.
checkCommand :: Command -> ProverInputState ()
checkCommand (Ty name ty) =
  do s <- lift get
     when (proofStarted s) (throwIO PNotFinished)
     let g = global s
     when (invalidName name g) (throwIO $ ExistE name)
     (tyr,tty) <- returnInput $ renamedType (fTypeContext g) (opers g) ty
     --outputStrLn $ show (tyr,tty) ++ "\n"
     lift $ modify $ newProof name (ty,tty) (tyr,tty)
     s' <- lift get
     outputStrLn $ renderProof $ getProofC s'
     prover                          
checkCommand (Types ps) =
  do s <- lift get
     when (proofStarted s) (throwIO PNotFinished)
     let (tr1, tr2) = typeRepeated ps (\t -> invalidName t $ global s)
     when (isJust tr1) (throwIO $ TypeRepeated $ fromJust tr1)
     when (isJust tr2) (throwIO $ ExistE $ fromJust tr2)
     lift $ modify $ modifyGlobal $ addFreeVars ps
     prover
checkCommand (Definition name body) =
  do s <- lift get
     when (proofStarted s) (throwIO PNotFinished)
     when (invalidName name $ global s) (throwIO $ ExistE name)
     defCommand name body
     prover
checkCommand (Ta (Print x)) =
  do s <- lift get
     let g = global s
     when (not $ isTheorem x g) (throwIO $ NotExistE x)
     outputStrLn $ render $ printTerm (opers g) $ getLTerm x g
     prover
checkCommand (Ta (Infer x)) =
  do s <- lift get
     let op = opers $ global s
     (te,te') <- returnInput $ withoutNameBasic op (fTypeContext $ global s) x
     --outputStrLn $ "Renombramiento: " ++ (render $ printLamTerm (opers $ global s) te)
     (ty,ty') <- returnInput $ basicTypeInference (theorems $ global s) op (te,te')
     --outputStrLn $ "Renombramiento: " ++ (render $ printTerm (opers $ global s) te')
     outputStrLn $ render $ printType op ty
     outputStrLn $ render $ printTType op ty'
     prover                            
checkCommand (Ta ta) =
  do s <- lift get
     when (not $ proofStarted s) (throwIO PNotStarted)
     let pc = getProofC s
         typ = getTypeProof s
     (_ , pc') <- returnInput $ runStateExceptions (habitar ta) pc
     lift $ modify $ setProofC pc'
     if (isFinalTerm pc')
       then ((outputStrLn $ "Prueba completa.\n"
              ++ renderFinalTerm (opers $ global s) (getTermFromProof pc' typ)  ++ "\n")
             >> reloadProver)
       else outputStrLn $ renderProof pc'
     prover

-- Trata el comando de definición.
-- Define el término dado por el 2º argumento.
defCommand :: String -> BodyDef -> ProverInputState ()
defCommand name (Type (body, n, args, isInfix)) =
  do s <- lift get
     let glo = global s   
     t <- returnInput $ renamedType3 args (fTypeContext glo) (opers glo) body
     outputStrLn $ render $ printType (opers glo) $ fst t
     typeDefinition name t n isInfix
defCommand name (LTerm body) =
  do s <- lift get
     let glo = global s
     te  <- returnInput $ withoutNameBasic (opers glo) (fTypeContext glo) body
     outputStrLn $ "Renombramiento: " ++ (render $ printLamTerm (opers glo) $ fst te)
     lamTermDefinition name te
defCommand name (Ambiguous ap) =
  do s <- lift get
     let glo = global s
     t <- returnInput $ basicDisambiguatedTerm (fTypeContext glo) (opers glo) ap
     case t of
       Left ty ->
         do outputStrLn $ render $ printType (opers glo) $ fst ty
            typeDefinition name ty 0 False
       Right te ->
         do outputStrLn $ "Renombramiento: " ++ (render $ printLamTerm (opers glo) $ fst te)
            lamTermDefinition name te

-- Función auxiliar de defCommand
typeDefinition :: String -> (Type, TType) -> Int -> Bool -> ProverInputState ()
typeDefinition name t n isInfix =
  do lift $ modify $ modifyGlobal $ addOperator (name, t, n, isInfix)
     when isInfix $ lift $ modify $ modifyUsrParser $ usrInfixParser name . getParser

-- Función auxiliar de defCommand
lamTermDefinition :: String -> (LamTerm, Term) -> ProverInputState ()
lamTermDefinition name te =
  do s <- lift get
     let glo = global s
     ty <- returnInput $ basicTypeInference (theorems glo) (opers glo) te
     lift $ modify $ newTheorem name (snd te ::: ty)

-- Funciones auxiliares del comando "Props/Types".
typeRepeated :: S.Seq TypeVar -> (String -> Bool) -> (Maybe String, Maybe String)
typeRepeated ps f
  | S.null ps = (Nothing, Nothing)
  | otherwise = let p = S.index ps 0
                    ps' = S.drop 1 ps
                in if elem p ps'
                   then (return p, Nothing)
                   else if f p
                        then (Nothing, return p)
                        else typeRepeated ps' f
                            

-- Impresión del lambda término final.
renderFinalTerm :: FOperations -> Term -> String
renderFinalTerm op t = render $ printTerm op t

-- Impresión del lambda término final sin nombres (a modo de prueba).
renderFinalTermWithoutName :: FOperations -> Term -> String
renderFinalTermWithoutName op t = render $ printTermTType op t

-- Impresión de la prueba en construcción
renderProof :: ProofConstruction -> String
renderProof p = render $ printProof (tsubp p) (conflict $ cglobal p) (opers $ cglobal p) (fTypeContext $ cglobal p) (subps p)

returnInput :: Either ProofExceptions a -> ProverInputState a
returnInput (Left exception) = throwIO exception
returnInput (Right x) = return x
