import System.Environment
import System.Console.Haskeline
import Asistente
import Parser
import Common
import Text.PrettyPrint.HughesPJ (render)
import PrettyPrinter (printTerm, printProof)

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
                  Just x -> do case getCommand x of
                                 Left error -> do outputStrLn error
                                                  loop state
                                 Right command -> analizadorTyTa command state
                              

analizadorTyTa :: Command -> Maybe (Int, Context, Type, Maybe EmptyTerm) -> InputT IO ()
analizadorTyTa (Ty ty) (Just s) = do outputStrLn "error: prueba no terminada"
                                     loop $ Just s
analizadorTyTa (Ty ty) Nothing = do outputStrLn $ render $ printProof 0 [] ty
                                    loop $ Just (0,[],ty, Nothing)
analizadorTyTa (Ta ta) (Just s)= habitarCheck s $ habitar s ta
analizadorTyTa (Ta ta) Nothing = do outputStrLn "error: prueba no comenzada"
                                    loop Nothing                                        
                                        
                                        
habitarCheck ::  (Int, Context, Type, Maybe EmptyTerm) -> Either String (Int, Context, Type, Either Term EmptyTerm) -> InputT IO ()
habitarCheck s (Left error) = do outputStrLn error
                                 loop $ Just s
habitarCheck _ (Right (_,_,_, Left term)) = do outputStrLn "prueba terminada"
                                               outputStrLn $ render $ printTerm term
                                               loop Nothing
habitarCheck _ (Right (n,c,ty,Right empTerm)) = do outputStrLn $ render $ printProof n c ty
                                                   loop $ Just (n, c, ty, Just empTerm)
                                                   
                                                   
-- do (n,c,ty,w) <- habitar s ta
--    case w of
--      Left term -> return Nothing
--      Right empTerm -> return Just (n, c, ty, Just empTerm)
   
