import Common hiding (catch)
import System.Console.Haskeline
import Control.Monad.State.Strict
import Data.Maybe
import Data.List (isPrefixOf)
import qualified Data.Sequence as S
import Tactics (habitar)
import Parser (isLoadCommand, commandsFromFiles, reservedWords, getCommand)
import Text.PrettyPrint (render)
import PrettyPrinter (help, printLTerm, printProof, printType, printPrintComm, printPrintAllComm)
import Transformers
import ErrorMsj (printError)
import TypeInference (basicTypeInference)
import ProverState
import GlobalState
import Proof (ProofConstruction, getLTermFromProof, isFinalTerm, cglobal, tsubp, subps)
import Data.List (isSuffixOf)
import TypeDefinition (TypeDefs, showTypeTable) -- SACAR SHOW
import LambdaTermDefinition (showLamTable) -- QUITAR

type ProverInputState a = InputT (StateT ProverState IO) a


-- Aborta la prueba.
resetProof :: ProverInputState ()
resetProof = lift $ modify $ finishProof
                
-- Finaliza la prueba.
reloadProver :: ProverInputState ()
reloadProver = lift $ modify $ finishProof . newLamDefFromProof


main :: IO ()
main = evalStateT (runInputT settings startProver) initialProver

searchCompl :: String -> String -> StateT ProverState IO [Completion]
searchCompl prev str
  | isLoadCommand $ reverse prev = getProofFile <$> listFiles str
  | otherwise = return $ map simpleCompletion $ filter (str `isPrefixOf`) reservedWords


getProofFile :: [Completion] -> [Completion]
getProofFile = filter (\(Completion x _ _) -> isSuffixOf ".pr" x)

settings :: Settings (StateT ProverState IO)
settings = Settings { historyFile = Nothing
                    , complete = completeWordWithPrev Nothing " \t" $ searchCompl
                    , autoAddHistory = True
                    }

prompt :: ProverState -> String
prompt s = if proofStarted s
           then theoremName s ++ " < "
           else "> "

startProver :: ProverInputState ()
startProver = proverFromFiles ["Prelude.pr"] 

proverFromCLI :: ProverInputState ()
proverFromCLI =
  do lift $ modify addCount
     s <- lift get
     minput <- getInputLine $ prompt s
     case minput of
       Nothing -> return ()
       Just "" -> proverFromCLI
       Just x ->
         catch (do command <- returnInputFromParser $ getCommand x (getCounter s)
                   checkCliCommand command)
         (\e -> outputStrLn (render $ printError (typeDef $ global s) e)
                >> proverFromCLI)

proverFromFiles :: [String] -> ProverInputState ()
proverFromFiles files =
  do s <- lift get
     r <- lift $ lift $ commandsFromFiles files
     catch (do commands <- returnInputFromParser r
               checkCommand commands)
       (\e -> outputStrLn (render $ printError (typeDef $ global s) e)
              >> proverFromCLI)

-- TERMINAR help
checkCliCommand :: (EPosition, CLICommand) -> ProverInputState ()
checkCliCommand (_, Escaped Exit) =
  outputStrLn "Saliendo."
checkCliCommand (_, Escaped Reset) =
  resetProof >> proverFromCLI
checkCliCommand (_, Escaped (Load files)) =
  proverFromFiles files
checkCliCommand (_, Escaped Help) =
  outputStrLn help >> proverFromCLI
checkCliCommand (pos, Lang c) =
  checkCommand [(pos, c)]


theoremCommand :: EPosition -> String -> Type1 -> ProverInputState ()
theoremCommand pos name ty =
  do s <- lift get
     when (proofStarted s) $ throwSemanError pos PNotFinished
     let g = global s
     when (invalidName name g) $ throwSemanError pos $ ExistE name
     tyr <- returnInput pos $ renamedType1 (fTypeContext g) (typeDef g) (lamDef g) ty
     ty' <- returnInput pos $ basicTypeWithoutName (fTypeContext g) (typeDef g) ty
     lift $ modify $ newProof name ty' tyr

axiomCommand :: EPosition -> String -> Type1 -> ProverInputState ()
axiomCommand pos name ty =
  do s <- lift get
     let g = global s
     when (invalidName name g) $ throwSemanError pos $ ExistE name
     emptyLTermDefinition pos name ty
     
typesVarCommand :: EPosition -> S.Seq TypeVar -> ProverInputState ()
typesVarCommand pos ps =
  do s <- lift get
     when (proofStarted s) $ throwSemanError pos PNotFinished
     let (tr1, tr2) = typeRepeated ps (\t -> invalidName t $ global s)
     when (isJust tr1) $ throwSemanError pos $ TypeRepeated $ fromJust tr1
     when (isJust tr2) $ throwSemanError pos $ ExistE $ fromJust tr2
     lift $ modify $ modifyGlobal $ addFreeVars ps

definitionCommand :: EPosition -> String -> BodyDef -> ProverInputState ()
definitionCommand pos name body = 
  do s <- lift get
     when (proofStarted s) $ throwSemanError pos $ PNotFinished
     when (invalidName name $ global s) $ throwSemanError pos $ ExistE name
     defCommand pos name body

tacticCommand :: Bool -> EPosition -> Tactic -> ProverInputState () 
tacticCommand printing pos (Print x) =
 do printCommand pos x
    if printing
      then printCommandPrinting x
      else return ()
tacticCommand printing pos PrintAll =
 if printing
 then printCommandPrintingAll
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
otherTacticsCommand :: EPosition -> Tactic -> ProverInputState (TypeDefs, DoubleType, ProofConstruction)
otherTacticsCommand _ (Print _) =
  error "error: otherTacticsCommand, no debería pasar."
otherTacticsCommand _ (Infer _) =
  error "error: otherTacticsCommand, no debería pasar."
otherTacticsCommand pos ta =
  do s <- lift get
     when (not $ proofStarted s) $ throwSemanError pos PNotStarted
     let pc = getProofC s
         typ = getTypeProof s
     (_ , pc') <- returnInput pos $ runStateExceptions (habitar ta) pc
     lift $ modify $ setProofC pc'
     if isFinalTerm pc'
       then reloadProver 
       else return ()
     return (typeDef $ global s, getTypeProof s, pc')

printCommand :: EPosition -> String -> ProverInputState ()
printCommand pos x =
  do s <- lift get
     let g = global s
     when (not $ isLamDef x g) $ throwSemanError pos $ NotExistE x

inferCommand :: EPosition -> LTerm1 -> ProverInputState DoubleType
inferCommand pos x =
  do s <- lift get
     let g = global s
     te <- returnInput pos $ basicWithoutName (typeDef g) (fTypeContext g) (lamDef g) x
     returnInput pos $ basicTypeInference (lamDef g) (typeDef g) te

printCommandPrinting :: String -> ProverInputState ()
printCommandPrinting x =
  do s <- lift get
     let g = global s
     outputStrLn $ render $ printPrintComm (typeDef g) x (getLamTerm x g) (getLamTermType x g)

printCommandPrintingAll :: ProverInputState ()
printCommandPrintingAll =
  do s <- lift get
     let g = global s
     outputStrLn $ render $ printPrintAllComm (lamDef g) (typeDef g)

inferCommandPrinting :: DoubleType -> ProverInputState ()
inferCommandPrinting ty =
  do s <- lift get
     outputStrLn $ renderType (typeDef $ global s) ty

otherTacticsCPrinting :: TypeDefs ->  DoubleType ->  ProofConstruction
                      -> ProverInputState ()
otherTacticsCPrinting op ty pc
  | isFinalTerm pc = outputStrLn $ "Prueba completa.\n" ++
                     renderLTerm op (getLTermFromProof pc ty)
  | otherwise = outputStrLn $ renderProof pc
  

-- Tratamiento de los comandos.
checkCommand :: [(EPosition, Command)] -> ProverInputState ()
checkCommand [] =
  do s <- lift get
     -- outputStrLn $ showLamTable (lamDef $ global s) ++ "\n"
     -- outputStrLn $ showTypeTable (typeDef $ global s) ++ "\n"
     proverFromCLI
checkCommand [(pos, Theorem name ty)] =
  do theoremCommand pos name ty
     s <- lift get
     outputStrLn $ renderProof $ getProofC s
     proverFromCLI     
checkCommand [(pos, Tac ta)] =
  do tacticCommand True pos ta
     proverFromCLI
checkCommand ((pos, Theorem name ty):cs) =
  do theoremCommand pos name ty
     checkCommand cs
checkCommand ((pos, Axiom name ty):cs) =
  do axiomCommand pos name ty
     checkCommand cs
checkCommand ((pos, Types ps):cs) =
  do typesVarCommand pos ps
     checkCommand cs
checkCommand ((pos, Definition name body):cs) =
  do definitionCommand pos name body
     checkCommand cs
checkCommand ((pos, Tac ta):cs) =
  do tacticCommand False pos ta
     checkCommand cs

-- Trata el comando de definición.
-- Define el término dado por el 2º argumento.
defCommand :: EPosition -> String -> BodyDef -> ProverInputState ()
defCommand pos name (Type ((body, args), n, isInfix)) =
  do s <- lift get
     let glo = global s   
     t <- returnInput pos $ renamedType3 args (fTypeContext glo) (typeDef glo) (lamDef glo) body
       --outputStrLn $ show t
     typeDefinition name t n isInfix
defCommand pos name (LTerm body) =
  do s <- lift get
     let glo = global s
     te  <- returnInput pos $ basicWithoutName (typeDef glo) (fTypeContext glo) (lamDef glo) body
     --outputStrLn $ "Renombramiento: " ++ show te ++ "\n" --(renderLTerm (typeDef glo) $ fst te)
     lamTermDefinition pos name te
defCommand pos name (EmptyLTerm ty) =
  emptyLTermDefinition pos name ty
defCommand pos name (Ambiguous ap) =
  do s <- lift get
     let glo = global s
     t <- returnInput pos $ basicDisambiguatedTerm (fTypeContext glo) (typeDef glo) ap
     case t of
       Left ty ->
         do --outputStrLn $ renderType (typeDef glo) $ fst ty
            typeDefinition name ty 0 False
       Right te ->
         do --outputStrLn $ "Renombramiento: " ++ (renderLTerm (typeDef glo) $ fst te)
            lamTermDefinition pos name te

-- Función auxiliar de defCommand
typeDefinition :: String -> DoubleType -> Int -> Bool -> ProverInputState ()
typeDefinition name t n isInfix =
  lift $ modify $ modifyGlobal $ addType name (t, n, isInfix)

-- Función auxiliar de defCommand
lamTermDefinition :: EPosition -> String -> DoubleLTerm -> ProverInputState ()
lamTermDefinition pos name te =
  do s <- lift get
     let glo = global s
     --outputStrLn $ show te ++ "\n"
     ty <- returnInput pos $ basicTypeInference (lamDef glo) (typeDef glo) te
     --outputStrLn $ (show $ toNoName te) ++ "\n"
     lift $ modify $ newLamDefinition name te ty

emptyLTermDefinition :: EPosition -> String -> Type1 -> ProverInputState ()
emptyLTermDefinition pos name ty =
  do s <- lift get
     let g = global s
     ty' <- returnInput pos $ basicTypeWithoutName (fTypeContext g) (typeDef g) ty
     lift $ modify $ newEmptyLamDefinition name ty'

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
-- renderLTermNoName :: TypeDefs -> LTerm2 -> String
-- renderLTermNoName op = render . printLTermNoName op

-- Impresión de lambda término con nombre, y tipos con nombres.
renderLTerm :: TypeDefs -> DoubleLTerm -> String
renderLTerm op  = render . printLTerm op

-- Impresión de tipo con nombre.
renderType :: TypeDefs -> DoubleType -> String
renderType op = render . printType op

-- Impresión de la prueba en construcción
renderProof :: ProofConstruction -> String
renderProof p = render $ printProof (tsubp p) (conflict $ cglobal p) (typeDef $ cglobal p) (fTypeContext $ cglobal p) (subps p)


returnInput :: EPosition -> Either SemanticException a -> ProverInputState a
returnInput pos (Left exception) = throwIO $ SemanticE (pos, exception)
returnInput pos (Right x) = return x

returnInputFromParser :: Either ProverException a -> ProverInputState a
returnInputFromParser (Left (SemanticE e)) = error "error: returnInputFromParser, no debería suceder."
returnInputFromParser (Left (SyntaxE e)) = throwIO (SyntaxE e :: ProverExceptionPos)
returnInputFromParser (Left (FileE e)) = throwIO (FileE e :: ProverExceptionPos)
returnInputFromParser (Right x) = return x

throwSemanError :: EPosition -> SemanticException -> ProverInputState ()
throwSemanError pos e = throwIO $ SemanticE (pos, e)
