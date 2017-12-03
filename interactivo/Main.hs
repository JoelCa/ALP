import Common hiding (catch)
import System.Console.Haskeline
import Control.Monad.State.Strict
import Tactics (habitar)
import Parser ( isLoadOrSaveCommand, commandsFromFiles, reservedWords
              , getCommands, getIndividualCommand)
import Hypothesis (isHypothesis)
import Text.PrettyPrint (render)
import PrettyPrinter ( help, printLTerm, printProof, printType, printPrintComm
                     , printPrintAllComm, printTheorem, printLTermWithType
                     , printCommType, msjFilesOk, msjVarsOk)
import Transformers
import ErrorMsj (printError)
import TypeInference (basicTypeInference)
import ProverState
import GlobalState
import Proof (ProofConstruction, getLTermFromProof, isFinalTerm, cglobal, tsubp, subps)
import TypeDefinition (TypeDefs)
import PreludePath
import System.IO (hClose, openTempFile, hPutStrLn, openFile, IOMode (AppendMode))
import System.Directory (getCurrentDirectory, copyFile, removeFile)
import Data.Foldable (toList)
import Data.Maybe
import Data.List (isPrefixOf, isSuffixOf)
import qualified Data.Sequence as S

type ProverInputState a = InputT (StateT ProverState IO) a


main :: IO ()
main = do dir <- getCurrentDirectory
          temp <- openTempFile dir ".temporary.pr"
          evalStateT (runInputT settings startProver) (initialProver temp)

settings :: Settings (StateT ProverState IO)
settings = Settings { historyFile = Nothing
                    , complete = completeWordWithPrev Nothing " \t" $ searchCompl
                    , autoAddHistory = True
                    }

searchCompl :: String -> String -> StateT ProverState IO [Completion]
searchCompl prev str
  | isLoadOrSaveCommand $ reverse prev = getProofFile <$> listFiles str
  | otherwise = return $ map simpleCompletion $ filter (str `isPrefixOf`) reservedWords


getProofFile :: [Completion] -> [Completion]
getProofFile = filter (\(Completion x _ _) -> isSuffixOf ".pr" x)


prompt :: ProverState -> String
prompt s
  | proofStarted s = theoremName s ++
                     if hasIncompleteInp s
                     then " <* "
                     else " < "
  | otherwise = if hasIncompleteInp s
                then ">* "
                else "> "

proverFromCLI :: ProverInputState ()
proverFromCLI =
  do lift $ modify addCount
     s <- lift get
     minput <- getInputLine $ prompt s
     case minput of
       Nothing -> return ()
       Just "" -> proverFromCLI
       Just x ->
         catch (do command <- returnInputFromParser $ getCommands x (getCounter s)
                   checkCommandsLine command)
         (\e -> outputStrLn (render $ printError (typeDef $ global s) e) >>
                (lift $ modify $ cleanInput) >>
                proverFromCLI)

prelude = "Prelude.pr"

startProver :: ProverInputState ()
startProver =
  do s <- lift get
     name <- lift $ lift $ getDataFileName prelude
     r <- lift $ lift $ commandsFromFiles [prelude]
     catch (do commands <- returnInputFromParser r
               checkCommands commands
               proverFromCLI)
       (\e -> outputStrLn (render $ printError (typeDef $ global s) e))


proverFromFiles :: [String] -> ProverInputState ()
proverFromFiles files =
  do s <- lift get
     r <- lift $ lift $ commandsFromFiles files
     catch (do commands <- returnInputFromParser r
               checkCommands commands
               outputStrLn $ render $ msjFilesOk files
               proverFromCLI)
       (\e -> outputStrLn (render $ printError (typeDef $ global s) e)
              >> proverFromCLI)

--------------------------------------------------------------------------------------
-- Procesamiento de los comandos

checkCommandsLine :: CLICommands -> ProverInputState ()
checkCommandsLine (Simple c) = checkSimpleCommand c
checkCommandsLine (Compound c) = checkCompoundCommands c


checkCompoundCommands :: PCompoundCommand -> ProverInputState ()
checkCompoundCommands (Nothing, cs, Nothing) =         -- Entrada "compuesta" completa
  do s <- lift get
     when (hasIncompleteInp s) (throwSemanError ((\(x,_,_) -> x) $ head $ cs) InvalidCompComm)
     langCommands cs
     proverFromCLI  
checkCompoundCommands (Nothing, cs, Just ic) =         -- Inicio de una entrada compuesta
  (lift $ modify $ (addIncompleteInput ic) . (addCommands cs)) >>
  proverFromCLI
checkCompoundCommands (Just (pos, x), cs, Just ic) =   -- Entrada incompleta
  do s <- lift get
     command <- returnInputFromParser $ getIndividualCommand (joinIncompleteComm x s) (snd pos)
     command' <- getLangCommand command
     lift $ modify $ (setIncompleteInput ic) . (addCommands $ command' : cs)
     proverFromCLI
checkCompoundCommands (Just (pos, x), cs, Nothing) =   -- Fin de entrada compuesta
  do s <- lift get
     command <- returnInputFromParser $ getIndividualCommand (joinIncompleteComm x s) (snd pos)
     command' <- getLangCommand command
     let cs' = getCompleteCommands s
     langCommands cs'
     checkIndCommand command'
     langCommands cs
     lift $ modify $ cleanInput
     proverFromCLI

langCommands :: [PComm] -> ProverInputState ()
langCommands = foldr (\x r -> checkIndCommand x >> r) (return ())

getLangCommand :: PExtComm -> ProverInputState PComm
getLangCommand (pos, s, Lang x) = return (pos, s, x) 
getLangCommand (pos, _, _) = throwSemanError pos InvalidCompComm  


checkSimpleCommand :: PExtComm -> ProverInputState ()
checkSimpleCommand x@(pos, _, _) =
  do s <- lift get
     when (hasIncompleteInp s) (throwSemanError pos InvalidCompComm)
     checkSimpleCommand' x
     

checkSimpleCommand' :: PExtComm -> ProverInputState ()
checkSimpleCommand' (_, _, Escaped Exit) =
  do s <- lift get
     lift $ lift (
       do let (temp, h) = getTempFile s
          hClose h
          removeFile temp)
     outputStrLn "Saliendo."
checkSimpleCommand' (pos, _, Escaped Abort) =
  do s <- lift get
     unless (proofStarted s) $ throwSemanError pos PNotStarted
     abortProof
     outputStrLn "Prueba abortada."
     proverFromCLI
checkSimpleCommand' (pos, _, Escaped (Load files)) =
  do s <- lift get
     when (proofStarted s) $ throwSemanError pos PNotFinished
     proverFromFiles files
checkSimpleCommand' (pos, _, Escaped (Save file)) =
  do s <- lift get
     when (proofStarted s) $ throwSemanError pos PNotFinished
     saveCommand file
     proverFromCLI
checkSimpleCommand' (_, _, Escaped Help) =
  outputStrLn help >>
  proverFromCLI
checkSimpleCommand' (pos, s, Lang c) =
  checkIndCommand (pos, s, c) >>
  proverFromCLI


-- Tratamiento de comandos del lenguaje, dados desde un archivo.
checkCommands :: [PCommand] -> ProverInputState ()
checkCommands [] =
  return () 
checkCommands [(pos, x)] =
  checkIndCommand' False pos x
checkCommands ((pos, x):xs) =
  checkIndCommand' False pos x >>
  checkCommands xs

-- Tratamiento de un solo comando del lenguaje.
-- Se añade al historial de comandos.
checkIndCommand :: PComm -> ProverInputState ()
checkIndCommand  (pos, s, Tac ta) =
  tacticCommand True pos ta >>
  saveIndCommand0 s >>
  finishProof
checkIndCommand (pos, _, x@(Theorem _ _)) =
  checkIndCommand' True pos x
checkIndCommand (pos, s, x) =
  checkIndCommand' True pos x >>
  saveIndCommand1 s

-- Tratamiento de un solo comando del lenguaje.
-- NO se añade al historial de comandos.
checkIndCommand' :: Bool -> EPosition -> Command -> ProverInputState ()    
checkIndCommand' printing pos (Theorem name ty) =
  theoremCommand printing pos name ty
checkIndCommand' printing pos (Tac ta) =
  tacticCommand printing pos ta >>
  finishProof
checkIndCommand' printing pos (Axiom name ty) =
  axiomCommand pos name ty >>
  (when printing $ outputStrLn $ msjDefOk name)
checkIndCommand' printing pos (Vars ps) =
  typesVarCommand pos ps >>
  (when printing $ outputStrLn $ render $ msjVarsOk $ toList ps)
checkIndCommand' printing pos (Definition name body) =
  definitionCommand pos name body >>
  (when printing $ outputStrLn $ msjDefOk name)

--------------------------------------------------------------------------------------
-- Mantenimiento del historial de comandos

-- Proceso de guardado. Luego de que se halla ingresado una táctica.
saveIndCommand0 :: String -> ProverInputState ()
saveIndCommand0 input =
  do s <- lift get
     if proofStarted s
       then if isFinalTerm $ getProofC s
            then do let (name, commands, ty) = (theoremName s, getProofCommands s, getTypeProof s)
                    writeHistory $ render $
                      printTheorem (typeDef $ global s) name ty (input : commands)
            else lift $ modify $ addInput input
       else writeHistory input

-- Proceso de guardado. Luego de que NO se halla ingresado una táctica.
saveIndCommand1 :: String -> ProverInputState ()
saveIndCommand1 input = writeHistory input

-- Escribe el/los comando/s al archivo de historial de comandos.
writeHistory :: String -> ProverInputState ()
writeHistory h =
  do s <- lift get
     lift $ lift $ hPutStrLn (snd $ getTempFile s) h 

--------------------------------------------------------------------------------------
-- Comandos

-- Guarda en el archivo dado por el primer argumento
-- el historial de los comandos exitosos.
saveCommand :: String -> ProverInputState ()
saveCommand file = do s <- lift get
                      let (temp, h) = getTempFile s
                      t <- lift $ lift $ (do hClose h
                                             copyFile temp file
                                             openFile temp AppendMode)
                      lift $ modify $ setTempHandle t

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
     let (tr1, tr2, conflicts) = typeCheckNames ps s
     when (isJust tr1) $ throwSemanError pos $ TypeRepeated $ fromJust tr1
     when (isJust tr2) $ throwSemanError pos $ ExistE $ fromJust tr2
     lift $ modify $ modifyGlobal $ addConflictNames conflicts . addFreeVars ps

definitionCommand :: EPosition -> String -> BodyDef -> ProverInputState ()
definitionCommand pos name body = 
  do s <- lift get
     when (proofStarted s) $ throwSemanError pos $ PNotFinished
     when (invalidName name $ global s) $ throwSemanError pos $ ExistE name
     defCommand pos name body

-- Procesa una táctica.
tacticCommand :: Bool -> EPosition -> Tactic -> ProverInputState ()
tacticCommand printing pos (Print x) =
  printCommand pos x >>
  (when printing $ printCommandPrinting x)
tacticCommand printing _ PrintAll =
  when printing printCommandPrintingAll
tacticCommand printing pos (Infer x) =
  do (te, ty) <- inferCommand pos x
     when printing $ inferCommandPrinting te ty
tacticCommand printing pos ta =
  otherTacticsCommand pos ta >>
  (when printing $ otherTacticsCPrinting)
       
-- Procesa todas las tácticas que no son "Print" ni "Infer".
otherTacticsCommand :: EPosition -> Tactic -> ProverInputState ()
otherTacticsCommand _ (Print _) =
  error "error: otherTacticsCommand, no debería pasar."
otherTacticsCommand _ (Infer _) =
  error "error: otherTacticsCommand, no debería pasar."
otherTacticsCommand pos ta =
  do s <- lift get
     when (not $ proofStarted s) $ throwSemanError pos PNotStarted
     let pc = getProofC s
     (_ , pc') <- returnInput pos $ runStateExceptions (habitar ta) pc
     lift $ modify $ setProofC pc'

printCommand :: EPosition -> String -> ProverInputState ()
printCommand pos x =
  do s <- lift get
     let g = global s
     when (not $ isLamDef x g || isType x g) $ throwSemanError pos $ NotExistE x

inferCommand :: EPosition -> LTerm1 -> ProverInputState (DoubleLTerm, DoubleType)
inferCommand pos x =
  do s <- lift get
     let g = global s
     te <- returnInput pos $ basicWithoutName (typeDef g) (fTypeContext g) (lamDef g) x
     ty <- returnInput pos $ basicTypeInference (lamDef g) (typeDef g) te
     return (te, ty)

printCommandPrinting :: String -> ProverInputState ()
printCommandPrinting x =
  do s <- lift get
     let g = global s
     when (isLamDef x g) (outputStrLn $ render $ printPrintComm (typeDef g) (lambTermVar x)
                          (getLamTerm x g) (getLamTermType x g))
     when (isType x g) (outputStrLn $ render $ printCommType x)

printCommandPrintingAll :: ProverInputState ()
printCommandPrintingAll =
  do s <- lift get
     let g = global s
     outputStrLn $ render $ printPrintAllComm (lamDef g) (typeDef g)

inferCommandPrinting :: DoubleLTerm -> DoubleType -> ProverInputState ()
inferCommandPrinting te ty =
  do s <- lift get
     outputStrLn $ render $ printLTermWithType te ty (typeDef $ global s)

otherTacticsCPrinting :: ProverInputState ()
otherTacticsCPrinting =
  do s <- lift get
     let (op, ty, pc) = (typeDef $ global s, getTypeProof s, getProofC s)
     if isFinalTerm pc
       then (outputStrLn $ (msjDefOk $ theoremName s) ++ "\n" ++
             renderLTerm op (getLTermFromProof pc ty))
       else outputStrLn $ renderProof pc

--------------------------------------------------------------------------------------
-- Procesamiento de las definiciones de lambda términos y tipos.

-- Trata el comando de definición.
-- Define el término dado por el 2º argumento y 3º argumento.
defCommand :: EPosition -> String -> BodyDef -> ProverInputState ()
defCommand pos name (Type ((body, args), n, isInfix)) =
  do s <- lift get
     let glo = global s   
     t <- returnInput pos $ renamedType3 args (fTypeContext glo) (typeDef glo) (lamDef glo) body
     typeDefinition name t n isInfix
defCommand pos name (LTerm body) =
  do s <- lift get
     let glo = global s
     te  <- returnInput pos $ basicWithoutName (typeDef glo) (fTypeContext glo) (lamDef glo) body
     lamTermDefinition pos name te
defCommand pos name (EmptyLTerm ty) =
  emptyLTermDefinition pos name ty
defCommand pos name (Ambiguous ap) =
  do s <- lift get
     let glo = global s
     t <- returnInput pos $ basicDisambiguatedTerm (fTypeContext glo) (typeDef glo) ap
     case t of
       Left ty ->
         typeDefinition name ty 0 False
       Right te ->
         lamTermDefinition pos name te

-- Función auxiliar de "defCommand"
typeDefinition :: String -> DoubleType -> Int -> Bool -> ProverInputState ()
typeDefinition name t n isInfix =
  lift $ modify $ modifyGlobal $ addConflictName name . addType name (t, n, isInfix)

-- Función auxiliar de "defCommand"
lamTermDefinition :: EPosition -> String -> DoubleLTerm -> ProverInputState ()
lamTermDefinition pos name te =
  do s <- lift get
     let glo = global s
     ty <- returnInput pos $ basicTypeInference (lamDef glo) (typeDef glo) te
     lift $ modify $ newLamDefinition name te ty

emptyLTermDefinition :: EPosition -> String -> Type1 -> ProverInputState ()
emptyLTermDefinition pos name ty =
  do s <- lift get
     let g = global s
     ty' <- returnInput pos $ basicTypeWithoutName (fTypeContext g) (typeDef g) ty
     lift $ modify $ newEmptyLamDefinition name ty'

--------------------------------------------------------------------------------------

-- Aborta la prueba.
abortProof :: ProverInputState ()
abortProof = lift $ modify $ cleanInput . deleteProof
                
-- Finaliza la prueba.
finishProof :: ProverInputState ()
finishProof =
  do s <- lift get
     when (proofStarted s) $ when (isFinalTerm $ getProofC s) reloadProver

reloadProver :: ProverInputState ()
reloadProver = lift $ modify $ cleanInput . deleteProof . newLamDefFromProof


-- Función auxiliar de "typesVarCommand".
-- Determina si hay nombres de variables conflictivos en el primer argumento.
typeCheckNames :: S.Seq TypeVar -> ProverState -> (Maybe String, Maybe String, [String])
typeCheckNames ps s = checkSeq ps elem (\t -> invalidName t $ global s) isHypothesis

checkSeq :: S.Seq a -> (a -> S.Seq a -> Bool)
          -> (a -> Bool) -> (a -> Bool)
          -> (Maybe a, Maybe a, [a])
checkSeq ps f g h
  | S.null ps = (Nothing, Nothing, [])
  | otherwise = let p = S.index ps 0
                    ps' = S.drop 1 ps
                in if f p ps'
                   then (return p, Nothing, [])
                   else if g p
                        then (Nothing, return p, [])
                        else let (x,y,z) = checkSeq ps' f g h
                             in if h p
                                then (x,y,p:z)
                                else (x,y,z)
                                
-- Impresión de lambda término con nombre, y tipos con nombres.
renderLTerm :: TypeDefs -> DoubleLTerm -> String
renderLTerm op  = render . printLTerm op

-- Impresión de tipo con nombre.
renderType :: TypeDefs -> DoubleType -> String
renderType op = render . printType op

-- Impresión de la prueba en construcción.
renderProof :: ProofConstruction -> String
renderProof p = render $ printProof (tsubp p) (typeDef $ cglobal p) (fTypeContext $ cglobal p) (subps p)

msjDefOk :: String -> String
msjDefOk name = "'" ++ name ++ "' definido" 

returnInput :: EPosition -> Either SemanticException a -> ProverInputState a
returnInput pos (Left exception) = throwIO $ SemanticE (pos, exception)
returnInput _ (Right x) = return x

returnInputFromParser :: Either ProverException a -> ProverInputState a
returnInputFromParser (Left (SemanticE _)) = error "error: returnInputFromParser, no debería suceder."
returnInputFromParser (Left (SyntaxE e)) = throwIO (SyntaxE e :: ProverExceptionPos)
returnInputFromParser (Left (FileE e)) = throwIO (FileE e :: ProverExceptionPos)
returnInputFromParser (Right x) = return x

throwSemanError :: EPosition -> SemanticException -> ProverInputState a
throwSemanError pos e = throwIO $ SemanticE (pos, e)
