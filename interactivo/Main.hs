import Common hiding (catch)
import System.Console.Haskeline
import Control.Monad.State.Strict
import Data.Maybe
import Data.List (isPrefixOf)
import qualified Data.Sequence as S
import Tactics (habitar)
import Parser (isLoadOrSaveCommand, commandsFromFiles, reservedWords, getCommand)
import Text.PrettyPrint (render)
import PrettyPrinter (help, printLTerm, printProof, printType, printPrintComm, printPrintAllComm, printTheorem)
import Transformers
import ErrorMsj (printError)
import TypeInference (basicTypeInference)
import ProverState
import GlobalState
import Proof (ProofConstruction, getLTermFromProof, isFinalTerm, cglobal, tsubp, subps)
import Data.List (isSuffixOf)
import TypeDefinition (TypeDefs, showTypeTable) -- SACAR SHOW
import LambdaTermDefinition (showLamTable) -- QUITAR
import System.IO (hClose, openFile, hPutStrLn, IOMode (AppendMode))

type ProverInputState a = InputT (StateT ProverState IO) a


-- Aborta la prueba.
abortProof :: ProverInputState ()
abortProof = lift $ modify $ finishProof
                
-- Finaliza la prueba.
reloadProver :: ProverInputState ()
reloadProver = do s <- lift get
                  writeHistory $ render $ printTheorem (typeDef $ global s) (theoremName s)
                    (getTypeProof s) (getLastCommand s : getProofCommands s)
                    --unlines$ reverse $ writeProof (theoremName s) getLastCommand s : getProofCommands s
                  lift $ modify $ finishProof . newLamDefFromProof

-- Comienza a guardar un historial de los comandos exitosos.
withHistory :: String -> ProverInputState ()
withHistory file = do f <- lift $ lift $ openFile file AppendMode
                      lift $ modify $ saveHistory f

-- Mantiene el último comando.
setLastComm :: String -> ProverInputState ()
setLastComm c = lift $ modify $ setLastCommand c

main :: IO ()
main = evalStateT (runInputT settings startProver) initialProver

searchCompl :: String -> String -> StateT ProverState IO [Completion]
searchCompl prev str
  | isLoadOrSaveCommand $ reverse prev = getProofFile <$> listFiles str
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
                   when (isWithHistory s) $ setLastComm x --CHEQUEAR
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
  do s <- lift get
     when (isWithHistory s) $ lift $ lift $ hClose $ getHistoryFile s
     outputStrLn "Saliendo."
checkCliCommand (_, Escaped Abort) =
  abortProof >> proverFromCLI
checkCliCommand (pos, Escaped (Load files)) =
  do s <- lift get
     when (proofStarted s) $ throwSemanError pos PNotFinished
     proverFromFiles files
checkCliCommand (pos, Escaped (Save file)) =
  do s <- lift get
     when (proofStarted s) $ throwSemanError pos PNotFinished
     withHistory file >> proverFromCLI
checkCliCommand (_, Escaped Help) =
  outputStrLn help >> proverFromCLI
checkCliCommand (pos, Lang c) =
  checkCommand [(pos, c)]


theoremCommand :: Bool -> EPosition -> String -> Type1 -> ProverInputState ()
theoremCommand printing pos name ty =
  do theoremCommand' pos name ty
     s <- lift get
     when printing (outputStrLn $  renderProof $ getProofC s)

theoremCommand' :: EPosition -> String -> Type1 -> ProverInputState ()
theoremCommand' pos name ty =
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
    when printing $ printCommandPrinting x
tacticCommand printing pos PrintAll =
 when printing printCommandPrintingAll
tacticCommand printing pos (Infer x) =
  do ty <- inferCommand pos x
     when printing $ inferCommandPrinting ty
tacticCommand printing pos ta =
  do (op, ty, pc) <- otherTacticsCommand pos ta
     when printing $ otherTacticsCPrinting op ty pc
       
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
     outputStrLn $ show te ++ "\n"
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
  | isFinalTerm pc = do outputStrLn $ "Prueba completa.\n" ++
                          renderLTerm op (getLTermFromProof pc ty)
                        outputStrLn $ show (getLTermFromProof pc ty) ++ "\n"
  | otherwise = outputStrLn $ renderProof pc
  

-- Tratamiento de los comandos.
checkCommand :: [(EPosition, Command)] -> ProverInputState ()
checkCommand [x] =
  do checkCommand' True x
     saveCommand $ snd x
     proverFromCLI
checkCommand xs =
  checkCommand'' xs

checkCommand' :: Bool -> (EPosition, Command) -> ProverInputState ()     
checkCommand' printing (pos, Theorem name ty) =
  theoremCommand printing pos name ty    
checkCommand' printing (pos, Tac ta) =
  tacticCommand printing pos ta
checkCommand' _ (pos, Axiom name ty) =
  axiomCommand pos name ty
checkCommand' _ (pos, Types ps) =
  typesVarCommand pos ps
checkCommand' _ (pos, Definition name body) =
  definitionCommand pos name body

-- Chequeo de comandos dados desde un archivo.
checkCommand'' :: [(EPosition, Command)] -> ProverInputState ()     
checkCommand'' [] =
  proverFromCLI
checkCommand'' (x:xs) =
  do checkCommand' False x
     checkCommand'' xs

saveCommand :: Command -> ProverInputState ()
saveCommand (Theorem _ _) =
  return ()
saveCommand (Tac t) =
  do s <- lift get
     when (isWithHistory s)
       (lift $ modify addLastComm)
saveCommand _ =
  do s <- lift get
     writeHistory $ getLastCommand s

-- Escribe el/los comando/s al archivo de historial de comandos.
writeHistory :: String -> ProverInputState ()
writeHistory h =
  do s <- lift get
     when (isWithHistory s)
       (lift $ lift $ hPutStrLn (getHistoryFile s) h) 

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
renderProof p = render $ printProof (tsubp p) (typeDef $ cglobal p) (fTypeContext $ cglobal p) (subps p)


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
