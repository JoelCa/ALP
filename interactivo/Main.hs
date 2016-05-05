import System.Environment
import System.Console.Haskeline
import Asistente
import Parser
import Common
import Text.PrettyPrint.HughesPJ (render)
import PrettyPrinter (printTerm, printProof)
import System.Console.Haskeline.MonadException


main :: IO ()
main = do args <- getArgs
          if args == []
            then runInputT defaultSettings (loop Nothing)
            else do putStrLn "aviso: hay argumentos!" --Tratar
                    runInputT defaultSettings (loop Nothing)


loop :: Maybe (Int, Context, Type, Maybe EmptyTerm) -> InputT IO ()
loop state = do minput <- getInputLine "> "
                case minput of
                  Nothing -> return ()
                  Just "-quit" -> return ()
                  Just x -> catch (do command <- returnInput $ getCommand x
                                      analizadorTyTa command state) (\e -> errorMessage e >> loop state)
             

analizadorTyTa :: Command -> Maybe (Int, Context, Type, Maybe EmptyTerm) -> InputT IO ()
analizadorTyTa (Ty ty) (Just s) = throwIO PNotFinished
analizadorTyTa (Ty ty) Nothing = do outputStrLn $ render $ printProof 0 [] ty
                                    loop $ Just (0,[],ty, Nothing)
analizadorTyTa (Ta ta) (Just s)= do s' <- returnInput $ habitar s ta
                                    habitarCheck s s'
analizadorTyTa (Ta ta) Nothing = throwIO PNotStarted


habitarCheck ::  (Int, Context, Type, Maybe EmptyTerm) -> (Int, Context, Type, Either Term EmptyTerm) -> InputT IO ()
habitarCheck _ (_,_,_, Left term) = do outputStrLn "prueba terminada"
                                       outputStrLn $ render $ printTerm term
                                       loop Nothing
habitarCheck _ (n,c,ty,Right empTerm) = do outputStrLn $ render $ printProof n c ty
                                           loop $ Just (n, c, ty, Just empTerm)
   

returnInput :: Either ProofExceptions a -> InputT IO a
returnInput (Left exception) = throwIO exception
returnInput (Right x) = return x

errorMessage :: ProofExceptions -> InputT IO ()
errorMessage SyntaxE = outputStrLn "error sintaxis"
errorMessage PNotFinished = outputStrLn "error: prueba no terminada"
errorMessage PNotStarted = outputStrLn "error: prueba no comenzada"
errorMessage AssuE = outputStrLn "error: comando assumption mal aplicado"
errorMessage IntroE = outputStrLn "error: comando intro mal aplicado"
errorMessage ApplyE1 = outputStrLn "error: comando apply mal aplicado, función no coincide tipo"
errorMessage ApplyE2 = outputStrLn "error: comando apply mal aplicado, no es función"
errorMessage ApplyE3 = outputStrLn "error: comando apply, hipótesis incorrecta"
errorMessage CommandInvalid = outputStrLn "error: comando inválido"
