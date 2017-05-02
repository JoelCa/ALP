import System.Environment
import System.Console.Haskeline
import Commands
import Parser
import Common hiding (State, catch, get)
import Text.PrettyPrint.HughesPJ (render)
import PrettyPrinter (printTerm, printProof, printType, printTType, printTermTType, printLamTerm)
import System.Console.Haskeline.MonadException
import Control.Monad.Trans.Class
import Control.Monad.State.Strict
import Control.Monad.IO.Class
import Data.Maybe
import qualified Data.Map as Map
import Data.List (find, findIndex, elemIndex)
import qualified Data.Vector as V
import Rules
import Transformers
import ErrorMsj
  
type ProverInputState a = InputT (StateT ProverState IO) a

-- Teoremas iniciales.
initialT' = [ ("intro_and", intro_and),
              ("elim_and", elim_and),
              ("intro_or1", intro_or1),
              ("intro_or2", intro_or2),
              ("elim_or", elim_or),
              ("intro_bottom", intro_bottom),
              ("elim_bottom", elim_bottom)
            ]

initialT = Map.fromList initialT'


-- Estado inicial.
initProverState :: ProverState
initProverState = PSt { global = PGlobal { teorems = initialT
                                         , fTypeContext = []
                                         , opers = V.fromList [ not_op
                                                              , iff_op
                                                              ]
                                         , parsers = [ PP emptyParser        -- const
                                                     , PP emptyParser        -- unary y binary
                                                     , PP basicInfixParser   -- infixOps
                                                     ]
                                         }
                      , proof = Nothing
                      }

main :: IO ()
main = do args <- getArgs
          if args == []
            then evalStateT (runInputT defaultSettings prover) initProverState
            else do putStrLn "aviso: hay argumentos!" --Tratar
                    evalStateT (runInputT defaultSettings prover) initProverState


prover :: ProverInputState ()
prover = do s <- lift get
            minput <- getInputLine "> "
            case minput of
              Nothing -> return ()
              Just "-quit" -> do outputStrLn "Saliendo."
                                 return ()
              Just "-r" -> resetProof
              Just "" -> prover
              Just x -> catch (do command <- returnInput $ getCommand x (parsers $ global s)
                                  checkCommand command)
                        (\e -> outputStrLn (errorMessage (opers $ global s) (e :: ProofExceptions))
                               >> prover)


-- Aplicación de los comandos.
checkCommand :: Command -> ProverInputState ()
checkCommand (Ty name ty) =
  do s <- lift get
     when (isJust $ proof s) (throwIO PNotFinished)
     let glo = global s
     when (Map.member name (teorems $ glo)) (throwIO $ PExist name)
     (tyr,tty) <- returnInput $ rename (fTypeContext glo) (opers glo) ty
     let p = newProof glo name tyr tty
     lift $ put $ PSt {global=glo, proof=Just p}
     outputStrLn $ renderProof $ constr p
     prover                          
checkCommand (Props ps) =
  do s <- lift get
     when (isJust $ proof s) (throwIO PNotFinished)
     let gps = fTypeContext $ global s
         pr1 = propRepeated1 ps
         pr2 = propRepeated2 ps gps
     when (isJust pr1) (throwIO $ PropRepeated1 $ fromJust pr1)
     when (isJust pr2) (throwIO $ PropRepeated2 $ fromJust pr2)
     lift $ put $ s {global = (global s) {teorems=teorems $ global s, fTypeContext=ps++gps}}
     prover
checkCommand (TypeDef (op, body, operands, isInfix)) =
  do s <- lift get
     let glo = global s
     when (isJust $ V.find (\(x,_,_,_)-> x == op) $ opers glo) (throwIO $ DefE op)
     t <- returnInput $ rename (fTypeContext glo) (opers glo) body
     let [p1, p2, p3] = parsers glo
     case (operands, isInfix) of
       (Empty, False) ->
         lift $ put $ s {global = glo { opers = V.snoc (opers glo) (op, t, operands, isInfix)
                                      , parsers = [ PP $ usrConstParser op $ runParser p1
                                                  , p2
                                                  , p3 ] }}
       (Unary, False) ->
         lift $ put $ s {global = glo { opers = V.snoc (opers glo) (op, t, operands, isInfix)
                                      , parsers = [ p1
                                                  , PP $ usrUnaryPrefixParser op $ runParser p2
                                                  , p3 ] }}
       (Binary, False) ->
         lift $ put $ s {global = glo { opers = V.snoc (opers glo) (op, t, operands, isInfix)
                                      , parsers = [ p1
                                                  , PP $ usrBinaryPrefixParser op $ runParser p2
                                                  , p3 ] }}
       (Binary, True) ->
         lift $ put $ s {global = glo { opers = V.snoc (opers glo) (op, t, operands, isInfix)
                                      , parsers = [ p1
                                                  , p2
                                                  , PP $ usrInfixParser op $ runParser p3 ] }}
       _ -> error "error: checkCommand, no debería pasar."
     prover
checkCommand (Ta (Print x)) =
  do s <- lift get
     let ter = teorems $ global s
     when (Map.notMember x ter) (throwIO $ PNotExist x)
     let t = ter Map.! x
     outputStrLn $ render $ printTerm (opers $ global s) $ t
     --outputStrLn $ render $ printType (opers $ global s) $ fst $ snd t
     prover
checkCommand (Ta (Infer x)) =
  do s <- lift get
     let op = opers $ global s
     (te,te') <- returnInput $ withoutName op (fTypeContext $ global s) (V.empty) 0 x
     outputStrLn $ "Renombramiento: " ++ (render $ printLamTerm (opers $ global s) te)
     (ty,ty') <- returnInput $ inferType 0 V.empty (teorems $ global s) op (te,te')
     --outputStrLn $ "Renombramiento: " ++ (render $ printTerm (opers $ global s) te')
     outputStrLn $ render $ printType op ty
     --outputStrLn $ show x ++ "\n"
     --outputStrLn $ show te ++ "\n"
     --outputStrLn $ render $ printTermTType (opers $ global s) te
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
       else (outputStrLn (renderProof p) >> (outputStrLn $ show $ length $ term p))
     prover

-- Funciones auxiliares del comando "Props".
propRepeated2 :: [String] -> [String] -> Maybe String
propRepeated2 _ [] = Nothing
propRepeated2 [] _ = Nothing
propRepeated2 (p:ps) ps'
  | elem p ps' = return p
  | otherwise = propRepeated2 ps ps'
                
propRepeated1 :: [String] -> Maybe String
propRepeated1 [] = Nothing
propRepeated1 (p:ps)
  | elem p ps = return p
  | otherwise = propRepeated1 ps

-- Funciones auxiliares:
-- Chequea si la prueba a terminado.
isFinalTerm :: ProofConstruction -> Bool
isFinalTerm (PConstruction {term=[Term _]}) = True
isFinalTerm _ = False

-- Obtiene el lambda término final de la prueba construida.
getTermFromProof :: ProofConstruction -> (Type, TType) -> Term
getTermFromProof (PConstruction {term=[Term t]}) ty = t ::: ty
getTermFromProof _ _ = error "getTermFromProof: no debería pasar"


-- Crea una prueba.
newProof :: ProverGlobal -> String -> Type -> TType -> ProofState
newProof pglobal name ty tty =
  let s = SP { termContext = V.empty
             , bTypeContext = V.empty
             , lsubp = 1
             , tvars = length $ fTypeContext $ pglobal
             , ty = [Just (ty, tty)]
             }
      c = PConstruction { tsubp = 1
                        , subps = [s]
                        , cglobal = pglobal
                        , term = [HoleT id]
                        }
  in PState { name = name
            , types = (ty, tty)
            , constr = c
            }

-- Aborta la prueba.
resetProof :: ProverInputState ()
resetProof = do s <- lift get
                lift $ put $ PSt {global=global s, proof=Nothing}
                prover
                
-- Finaliza la prueba.
reloadProver :: ProverInputState ()
reloadProver = do s <- lift get
                  let p = fromJust $ proof s
                  lift $ put $ PSt { global= (global s)
                                             {teorems=Map.insert (name p)
                                                    (getTermFromProof (constr p) (types p))
                                                    (teorems $ global s)}
                                   , proof = Nothing
                                   }

-- Impresión del lambda término final.
renderFinalTerm :: FOperations -> Term -> String
renderFinalTerm op t = render $ printTerm op t

-- Impresión del lambda término final sin nombres (a modo de prueba).
renderFinalTermWithoutName :: FOperations -> Term -> String
renderFinalTermWithoutName op t = render $ printTermTType op t

-- Impresión de la prueba en construcción
renderProof :: ProofConstruction -> String
renderProof p = render $ printProof (tsubp p) (opers $ cglobal p) (fTypeContext $ cglobal p) (subps p)


returnInput :: Either ProofExceptions a -> ProverInputState a
returnInput (Left exception) = throwIO exception
returnInput (Right x) = return x
