import Common hiding (catch)
import System.Console.Haskeline
import Control.Monad.State.Strict
import Data.Maybe
import Data.List (isPrefixOf)
import qualified Data.Sequence as S
import Tactics (habitar)
import Parser (emptyPos, commandsFromFile, reservedWords, getCommand, usrInfixParser, getParser)
import Text.PrettyPrint (render)
import PrettyPrinter (printLTermNoName, printProof, printType)
import Transformers
import ErrorMsj (printError, printErrorNoPos)
import TypeInference (basicTypeInference)
import ProverState
import GlobalState
import Proof (ProofConstruction, getLTermFromProof, isFinalTerm, cglobal, tsubp, subps)
  
type ProverInputState a = InputT (StateT ProverState IO) a


-- Aborta la prueba.
resetProof :: ProverInputState ()
resetProof = lift $ modify $ finishProof
                
-- Finaliza la prueba.
reloadProver :: ProverInputState ()
reloadProver = lift $ modify $ finishProof . newTheoremFromProof


main :: IO ()
main = evalStateT (runInputT settings proverFromCLI) initialProver

searchCompl :: String -> [Completion]
searchCompl str = map simpleCompletion $ filter (str `isPrefixOf`) reservedWords

settings :: Settings (StateT ProverState IO)
settings = Settings { historyFile = Nothing
                    , complete = completeWord Nothing " \t" $ return . searchCompl
                    , autoAddHistory = True
                    }

prompt :: ProverState -> String
prompt s = if proofStarted s
           then theoremName s ++ " < "
           else "> "

proverFromCLI :: ProverInputState ()
proverFromCLI = prover Nothing

proverFromFile :: String -> ProverInputState ()
proverFromFile file = prover $ Just file

prover :: Maybe String -> ProverInputState ()
prover Nothing =
  do s <- lift get
     minput <- getInputLine $ prompt s
     case minput of
       Nothing -> return ()
       Just "" -> prover Nothing
       Just x ->
         catch (do command <- returnInput emptyPos $ getCommand x $ infixParser s
                   checkCliCommand command)
         (\e -> outputStrLn (render $ printErrorNoPos (opers $ global s) e)
                >> prover Nothing)
prover (Just file) =
  do s <- lift get
     r <- lift $ lift $ commandsFromFile file (infixParser s)
     catch (do commands <- returnInput emptyPos r
               checkCommand commands)
       (\e -> outputStrLn (render $ printError file (opers $ global s) e)
              >> prover Nothing)

checkCliCommand :: (LinePos, CLICommand) -> ProverInputState ()
checkCliCommand (pos, Escaped Exit) = outputStrLn "Saliendo."
checkCliCommand (pos, Escaped Reset) = resetProof >> proverFromCLI
checkCliCommand (pos, Escaped (Load file)) =
  do outputStrLn $ "File: " ++ file ++ "\n"
     proverFromFile file
checkCliCommand (pos, Lang c) = checkCommand [(pos, c)]


theoremCommand :: LinePos -> String -> Type1 -> ProverInputState ()
theoremCommand pos name ty =
  do s <- lift get
     when (proofStarted s) $ throwIO (pos, PNotFinished)
     let g = global s
     when (invalidName name g) $ throwIO (pos, ExistE name)
     tyr <- returnInput pos $ renamedType1 (fTypeContext g) (opers g) (theorems g) ty
     ty' <- returnInput pos $ basicTypeWithoutName (fTypeContext g) (opers g) ty
     lift $ modify $ newProof name ty' tyr

typesVarCommand :: LinePos -> S.Seq TypeVar -> ProverInputState ()
typesVarCommand pos ps =
  do s <- lift get
     when (proofStarted s) $ throwIO (pos, PNotFinished)
     let (tr1, tr2) = typeRepeated ps (\t -> invalidName t $ global s)
     when (isJust tr1) $ throwIO (pos, TypeRepeated $ fromJust tr1)
     when (isJust tr2) $ throwIO (pos, ExistE $ fromJust tr2)
     lift $ modify $ modifyGlobal $ addFreeVars ps

definitionCommand :: LinePos -> String -> BodyDef -> ProverInputState ()
definitionCommand pos name body = 
  do s <- lift get
     when (proofStarted s) $ throwIO (pos, PNotFinished)
     when (invalidName name $ global s) $ throwIO (pos, ExistE name)
     defCommand pos name body

tacticCommand :: Bool -> LinePos -> Tactic -> ProverInputState () 
tacticCommand printing pos (Print x) =
 do printCommand pos x
    if printing
      then printCommandPrinting x
      else return ()
tacticCommand printing pos (Infer x) =
  do ty <- inferCommand pos x
     if printing
       then inferCommandPrinting ty
       else return ()
tacticCommand printing pos ta =
  do (op, ty, pc) <- otherTacticsCommand pos ta
     if printing
       then otherTacticsCPrinting op ty pc
       else return ()

       
-- Procesa todas las tácticas que no son "Print" ni "Infer".
otherTacticsCommand :: LinePos -> Tactic -> ProverInputState (FOperations, DoubleType, ProofConstruction)
otherTacticsCommand _ (Print _) =
  error "error: otherTacticsCommand, no debería pasar."
otherTacticsCommand _ (Infer _) =
  error "error: otherTacticsCommand, no debería pasar."
otherTacticsCommand pos ta =
  do s <- lift get
     when (not $ proofStarted s) $ throwIO (pos, PNotStarted)
     let pc = getProofC s
         typ = getTypeProof s
     (_ , pc') <- returnInput pos $ runStateExceptions (habitar ta) pc
     lift $ modify $ setProofC pc'
     if isFinalTerm pc'
       then reloadProver 
       else return ()
     return (opers $ global s, getTypeProof s, pc')

printCommand :: LinePos -> String -> ProverInputState ()
printCommand pos x =
  do s <- lift get
     let g = global s
     when (not $ isTheorem x g) $ throwIO (pos, NotExistE x)

inferCommand :: LinePos -> LTerm1 -> ProverInputState DoubleType
inferCommand pos x =
  do s <- lift get
     let g = global s
     te <- returnInput pos $ basicWithoutName (opers g) (fTypeContext g) (theorems g) x
     returnInput pos $ basicTypeInference (theorems g) (opers g) te

printCommandPrinting :: String -> ProverInputState ()
printCommandPrinting x =
  do s <- lift get
     let g = global s
     outputStrLn $ renderNoNameLTerm (opers g) $ getLTermFromTheorems x g

inferCommandPrinting :: DoubleType -> ProverInputState ()
inferCommandPrinting ty =
  do s <- lift get
     outputStrLn $ renderType (opers $ global s) ty

otherTacticsCPrinting :: FOperations ->  DoubleType ->  ProofConstruction
                      -> ProverInputState ()
otherTacticsCPrinting op ty pc
  | isFinalTerm pc = outputStrLn $ "Prueba completa.\n" ++
                     renderNoNameLTerm op (getLTermFromProof pc ty)
  | otherwise = outputStrLn $ renderProof pc
  

-- Tratamiento de los comandos.
checkCommand :: [(LinePos, Command)] -> ProverInputState ()
checkCommand [] = proverFromCLI
checkCommand [(pos, Ty name ty)] =
  do theoremCommand pos name ty
     s <- lift get
     outputStrLn $ renderProof $ getProofC s
     proverFromCLI
checkCommand [(pos, Ta ta)] =
  do tacticCommand True pos ta
     proverFromCLI
checkCommand ((pos,Ty name ty):cs) =
  do theoremCommand pos name ty
     checkCommand cs
checkCommand ((pos, Types ps):cs) =
  do typesVarCommand pos ps
     checkCommand cs
checkCommand ((pos, Definition name body):cs) =
  do definitionCommand pos name body
     checkCommand cs
checkCommand ((pos, Ta ta):cs) =
  do tacticCommand False pos ta
     checkCommand cs

-- Trata el comando de definición.
-- Define el término dado por el 2º argumento.
defCommand :: LinePos -> String -> BodyDef -> ProverInputState ()
defCommand pos name (Type (body, n, args, isInfix)) =
  do s <- lift get
     let glo = global s   
     t <- returnInput pos $ renamedType3 args (fTypeContext glo) (opers glo) (theorems glo) body
     --outputStrLn $ renderType (opers glo) $ fst t
     typeDefinition name t n isInfix
defCommand pos name (LTerm body) =
  do s <- lift get
     let glo = global s
     te  <- returnInput pos $ basicWithoutName (opers glo) (fTypeContext glo) (theorems glo) body
     --outputStrLn $ "Renombramiento: " ++ (renderLTerm (opers glo) $ fst te)
     lamTermDefinition pos name te
defCommand pos name (Ambiguous ap) =
  do s <- lift get
     let glo = global s
     t <- returnInput pos $ basicDisambiguatedTerm (fTypeContext glo) (opers glo) ap
     case t of
       Left ty ->
         do --outputStrLn $ renderType (opers glo) $ fst ty
            typeDefinition name ty 0 False
       Right te ->
         do --outputStrLn $ "Renombramiento: " ++ (renderLTerm (opers glo) $ fst te)
            lamTermDefinition pos name te

-- Función auxiliar de defCommand
typeDefinition :: String -> DoubleType -> Int -> Bool -> ProverInputState ()
typeDefinition name t n isInfix =
  do lift $ modify $ modifyGlobal $ addOperator (name, t, n, isInfix)
     when isInfix $ lift $ modify $ modifyUsrParser $ usrInfixParser name . getParser

-- Función auxiliar de defCommand
lamTermDefinition :: LinePos -> String -> DoubleLTerm -> ProverInputState ()
lamTermDefinition pos name te =
  do s <- lift get
     let glo = global s
     ty <- returnInput pos $ basicTypeInference (theorems glo) (opers glo) te
     lift $ modify $ newTheorem name (toNoName te ::: ty)

-- Función auxiliar del comando "Props/Types".
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
                            

-- Impresión de lambda término sin nombre, y tipos con nombres.
renderNoNameLTerm :: FOperations -> LTerm2 -> String
renderNoNameLTerm op = render . printLTermNoName op

-- Impresión de lambda término con nombre, y tipos con nombres.
-- renderLTerm :: FOperations -> LamTerm -> String
-- renderLTerm op  = render . printLamTerm op

-- Impresión de tipo con nombre.
renderType :: FOperations -> DoubleType -> String
renderType op = render . printType op

-- Impresión de la prueba en construcción
renderProof :: ProofConstruction -> String
renderProof p = render $ printProof (tsubp p) (conflict $ cglobal p) (opers $ cglobal p) (fTypeContext $ cglobal p) (subps p)


returnInput :: LinePos -> Either ProofException a -> ProverInputState a
returnInput pos (Left exception) = throwIO (pos, exception)
returnInput pos (Right x) = return x
