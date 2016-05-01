import System.Environment
import System.Console.Haskeline
import Asistente_archivo
import Parser_archivo
import Text.PrettyPrint.HughesPJ (render)


main :: IO ()
main = do args <- getArgs
          if args == []
            then runInputT defaultSettings loop
            else do maybe (putStrLn "Error: argumento incorrecto")
                      (\fileDir -> 
                        do file <- readFile fileDir
                           maybe (putStrLn "Error aaa")
                             (\(ty,tac)-> putStrLn $ render $ eval ty tac) $
                             getCommand file) $ getFile args

getFile :: [String] -> Maybe String
getFile ("-load":[x]) = return x
getFile _ = Nothing

loop :: InputT IO ()
loop = do minput <- getInputLine "> "           
          case minput of
            Nothing -> return ()
            Just "quit" -> return ()
            Just _ -> return ()
            -- Just input -> do maybe (outputStrLn "Error")
            --                    (\(ty,tac)-> outputStrLn $ render $ eval ty tac) $
            --                    getCommand input
            --                  loop