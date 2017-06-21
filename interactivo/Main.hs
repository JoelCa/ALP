import Tactics (habitar)
import Parser
import Common hiding (State, catch, get)
import Text.PrettyPrint.HughesPJ (render)
import PrettyPrinter (printTerm, printProof, printType, printTType, printTermTType, printLamTerm)
import Rules
import Transformers
import ErrorMsj
import TypeInference (typeInference)
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
import qualified Data.IntSet as IS
import qualified Data.Map as Map
  
type ProverInputState a = InputT (StateT ProverState IO) a


-- Aborta la prueba.
resetProof :: ProverInputState ()
resetProof = (lift $ modify $ finishProof) >> prover
                
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
              Just "-r" -> resetProof
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
     when (isInvalidName name g) (throwIO $ ExistE name)
     (tyr,tty) <- returnInput $ renamedType (fTypeContext g) (opers g) ty
     --outputStrLn $ show (tyr,tty) ++ "\n"
     lift $ modify $ newProof g name (ty,tty) (tyr,tty)
     s' <- lift get
     outputStrLn $ renderProof $ getProofC s'
     prover                          
checkCommand (Types ps) =
  do s <- lift get
     when (isJust $ proof s) (throwIO PNotFinished)
     let glo = global s
         gps = fTypeContext glo
         (tr1, tr2) = typeRepeated ps
                      (\t -> (elem t gps)
                             || (Map.member t $ theorems $ glo)
                             || (any (\(x,_,_,_) -> x == t) $ opers glo)
                             || (any (\(x,_,_) -> x == t) notFoldeableOps)
                      )
     when (isJust tr1) (throwIO $ TypeRepeated $ fromJust tr1)
     when (isJust tr2) (throwIO $ ExistE $ fromJust tr2)
     lift $ put $ s {global = (global s) {theorems = theorems $ global s, fTypeContext= ps S.>< gps}}   --VER
     prover
checkCommand (Definition name body) =
  do s <- lift get
     let glo = global s
     when (isJust $ proof s) (throwIO PNotFinished)
     when ( (any (\(x,_,_,_)-> x == name) $ opers glo)
            || (any (\(x,_,_) -> x == name) notFoldeableOps)
          )
       (throwIO $ DefE name)
     when ( (elem name $ fTypeContext glo)
            || (Map.member name $ theorems $ glo)
          )
       (throwIO $ ExistE name)
     defCommand name body
     prover
checkCommand (Ta (Print x)) =
  do s <- lift get
     let ter = theorems $ global s
     when (Map.notMember x ter) (throwIO $ NotExistE x)
     let t = ter Map.! x
     outputStrLn $ render $ printTerm (opers $ global s) $ t
     --outputStrLn $ render $ printType (opers $ global s) $ fst $ snd t
     prover
checkCommand (Ta (Infer x)) =
  do s <- lift get
     let op = opers $ global s
     (te,te') <- returnInput $ withoutName op (fTypeContext $ global s) (S.empty) (IS.empty, 0) x
     --outputStrLn $ "Renombramiento: " ++ (render $ printLamTerm (opers $ global s) te)
     (ty,ty') <- returnInput $ typeInference 0 S.empty (theorems $ global s) op (te,te')
     --outputStrLn $ "Renombramiento: " ++ (render $ printTerm (opers $ global s) te')
     outputStrLn $ render $ printType op ty
     outputStrLn $ render $ printTType op ty'
     prover                            
checkCommand (Ta ta) =
  do s <- lift get
     when (isNothing $ proof s) (throwIO PNotStarted)
     let pr = fromJust $ proof s
     (_ , p) <- returnInput $ runStateExceptions (habitar ta) (constr $ pr)
     lift $ put $ s {proof = Just $ pr {constr = p}}
     if (isFinalTerm p)
       then ((outputStrLn $ "Prueba completa.\n"
              ++ renderFinalTerm (opers $ cglobal p) (getTermFromProof p (types pr))  ++ "\n")
             >> reloadProver)
       else outputStrLn $ renderProof p
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
     te  <- returnInput $ withoutName (opers glo) (fTypeContext glo) (S.empty) (IS.empty, 0) body
     outputStrLn $ "Renombramiento: " ++ (render $ printLamTerm (opers glo) $ fst te)
     lamTermDefinition name te
defCommand name (Ambiguous ap) =
  do s <- lift get
     let glo = global s
     t <- returnInput $ disambiguatedTerm S.empty (fTypeContext glo) (opers glo) (conflict glo, 0) ap
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
  do lift $ modify $
       \s ->  s { global = (global s) { opers = opers (global s) S.|> (name, t, n, isInfix)} }
     when isInfix $ lift $ modify $
       \s' -> s' {infixParser =  usrInfixParser name $ getParser $ infixParser s' }

-- Función auxiliar de defCommand
lamTermDefinition :: String -> (LamTerm, Term) -> ProverInputState ()
lamTermDefinition name te =
  do s <- lift get
     let glo = global s
     ty <- returnInput $ typeInference 0 S.empty (theorems glo) (opers glo) te
     lift $ modify $ newTheorem name (snd te ::: ty)
     -- lift $ put $ s { global = glo { theorems = Map.insert name (snd te ::: ty) $ theorems $ glo
     --                               , conflict = checkNameConflict name $ conflict $ glo } }

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
