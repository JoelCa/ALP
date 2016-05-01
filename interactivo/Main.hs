import System.Environment
import System.Console.Haskeline
import Asistente
import Parser
import Common
import Text.PrettyPrint.HughesPJ (render)
import PrettyPrinter (printTerm)

main :: IO ()
main = do args <- getArgs
          if args == []
            then runInputT defaultSettings (loop Nothing)
            else do putStrLn "aviso: hay argumentos!" --Tratar
                    runInputT defaultSettings (loop Nothing)

loop :: Maybe (Context, Type, Maybe EmptyTerm) -> InputT IO ()
loop state = do minput <- getInputLine "> "
                case minput of
                  Nothing -> return ()
                  Just "-quit" -> return ()
                  Just x -> do case getCommand x of
                                 Left error -> do outputStrLn error
                                                  loop state
                                 Right command -> do outputStrLn $ show command
                                                     analizadorTyTa command state
                              

analizadorTyTa :: Command -> Maybe (Context, Type, Maybe EmptyTerm) -> InputT IO ()
analizadorTyTa (Ty ty) (Just s) = do outputStrLn "error: prueba no terminada"
                                     loop $ Just s
analizadorTyTa (Ty ty) Nothing = loop $ Just ([],ty, Nothing)
analizadorTyTa (Ta ta) (Just s)= habitarCheck s $ habitar s ta
analizadorTyTa (Ta ta) Nothing = do outputStrLn "error: prueba no comenzada"
                                    loop Nothing                                        
                                        
                                        
habitarCheck ::  (Context, Type, Maybe EmptyTerm) -> Either String (Context, Type, Either Term EmptyTerm) -> InputT IO ()
habitarCheck s (Left error) = do outputStrLn error
                                 loop $ Just s
habitarCheck _ (Right (_,_, Left term)) = do outputStrLn "prueba terminada"
                                             outputStrLn $ render $ printTerm term
                                             loop Nothing
habitarCheck _ (Right (c,ty,Right empTerm)) = loop $ Just (c, ty, Just empTerm)

                         
