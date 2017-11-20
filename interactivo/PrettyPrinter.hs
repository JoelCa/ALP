module PrettyPrinter where

import Common
import Proof
import TypeDefinition (TypeDefs, getTypeData, getTypesNames)
import LambdaTermDefinition (LamDefs, getLamTable)
import Text.PrettyPrint
import Data.Maybe (isJust)
import qualified Data.Sequence as S

-----------------------
--- pretty printer
-----------------------

parenIf :: Bool -> Doc -> Doc
parenIf False d   = d
parenIf True d    = parens d

-- Precedencias
pAs :: Int
pAs = 0

pApp :: Int
pApp = 1

pBApp :: Int
pBApp = 1

pLam :: Int
pLam = 2

pBLam :: Int
pBLam = 2

pEPack :: Int
pEPack = 2

pEUnpack :: Int
pEUnpack = 2

-- Pretty-printer de lambda término con nombre, y tipos con nombres.
printLTerm :: TypeDefs -> DoubleLTerm -> Doc
printLTerm op = printLTerm' op (1, False)

printLTerm' :: TypeDefs -> (Int, Bool) -> DoubleLTerm -> Doc
printLTerm' _ _ (LVar (x,_)) =
  text x
printLTerm' op (i,j) (Abs x t e) =
  parenIf (i < pLam) $
  sep $
  text "\\" <> 
  text x <> 
  text ":" <> 
  printType op t <>
  text "." :
  [nest 2 $ printLTerm' op (pLam,j) e]
printLTerm' op (i, j) (t :@: u) =
  parenIf ((i < pApp) || ((i == pApp) && j)) $  
  sep $
  printLTerm' op (pApp, False) t :
  [printLTerm' op (pApp, True) u]
printLTerm' op (i, j) (BAbs x u) =
  parenIf (i < pBLam) $
  sep $
  text "\\" <> 
  text x <> 
  text "." :
  [nest 2 $ printLTerm' op (pBLam,j) u]
printLTerm' op (i, j) (x :!: ty) =
  parenIf ((i < pBApp) || ((i == pBApp) && j)) $
  sep $
  printLTerm' op (pBApp, False) x :
  [ nest 2 $
    text "[" <>
    printType op ty <>
    text "]" ]
printLTerm' op (i, j) (EPack ty e tty) =
  parenIf (i < pEPack) $
  sep $
  text "{*" <>
  printType op ty <>
  text "," :
  printLTerm' op (pEPack, j) e <>
  text "}" :
  [ nest 2 $
    text "as" <+>
    printType op tty ]
printLTerm' op (i, j) (EUnpack x y e u) =
  parenIf (i < pEUnpack) $
  sep $
  text "let" :
  text "{" <>
  text x <>
  text "," :
  text y <>
  text "}" <+>
  text "=" :
  [ nest 2 $
    printLTerm' op (pEUnpack, j) e <+>
    text "in" <+>
    printLTerm' op (pEUnpack, j) u ]
printLTerm' op (i, j) (t ::: ty) =
  parenIf (i == pAs) $
  sep $
  printLTerm' op (pAs, j) t :
  [ nest 2 $
    text "as" <+>
    parens (printType op ty) ]

--------------------------------------------------------------------------------------------  
-- Pretty-printer de tipos con nombres.
-- Consideramos que las operaciones "custom", son a lo suma binaria.
-- Además, que las operaciones unaria solo se imprimen de forma prefija.
-- Obs: Basta con que la primera componente de la tripleta, que se pasa como argumento a
-- printType', sea mayor o igual a 7, para asegurar que no aparescan paréntesis "externos".
printType :: TypeDefs -> DoubleType -> Doc
printType = printType' (7,False)

-- Argumentos:
-- 1. Si el argumento número 3 "x", es un argumento de una operación "op",
-- estonces la componente número uno de la túpla indica la precedencia
-- de "op", mientras que el argumento número 2, nos dice si "x" es la
-- componente izquierda de "op".
-- 2. Operaciones foldeables.
-- 3. Tipo.
printType' :: (Int, Bool) -> TypeDefs -> DoubleType -> Doc
printType' _ _ (TVar (v, _)) =
  text v
printType' prec op (Fun t1 t2) =
  printBinInfix (\x t -> printType' x op t) "->" prec 5 t1 t2
printType' (p,left) op (ForAll v t) =
  parenIf (p < 7) $
  sep $
  text "forall" <+>
  text v <>
  text "," :
  [nest 2 $ printType' (7,left) op t]
printType' (p,left) op (Exists v t) =
  parenIf (p < 7) $
  sep $
  text "exists" <+>
  text v <>
  text "," :
  [nest 2 $ printType' (7,left) op t]
printType' prec op (RenamedType s [t1, t2])
  | s == and_id = printBinInfix (\x t -> printType' x op t) s prec 3 t1 t2
  | s == or_id = printBinInfix (\x t -> printType' x op t) s prec 4 t1 t2
  | s == iff_id = printBinInfix (\x t -> printType' x op t) s prec 6 t1 t2
  | otherwise = case getTypeData s op of
                  Just (_,_,False) ->
                    printPrefix (\x t -> printType' x op t) s prec [t1,t2]
                  Just (_,_,True) ->
                    printBinInfix (\x t -> printType' x op t) s prec 2 t1 t2
                  _ -> error "error: printType' no debería pasar."
printType' prec op (RenamedType s ts) =
  printPrefix (\x t -> printType' x op t) s prec ts


printBinInfix :: ((Int, Bool) -> a -> Doc) -> String
              -> (Int, Bool) -> Int -> a -> a -> Doc              
printBinInfix f s (p,left) n t1 t2 =
  parenIf (p < n || ( (p == n) && left)) $
  sep $
  f (n, True) t1 :
  [ text s <+>
    f (n, False) t2 ]


printPrefix :: ((Int, Bool) -> a -> Doc) -> String
            -> (Int, Bool) -> [a] -> Doc
printPrefix _ s _ [] 
  | s == bottom_id = text $ bottom_id
  | otherwise = text s
printPrefix f s (p, left) [t]
  | s == not_id = parenIf (p < 1) $
                  text s <+>
                  f (1, left) t
  | otherwise = parenIf (p == 0) $
                text s <+>
                f (0, left) t
printPrefix f s (p, left) ts =
  parenIf (p == 0) $
  text s <+>
  foldl (\r t -> r <+> f (0,left) t) empty ts
  
--------------------------------------------------------------------------------------------  
-- Pretty-printer de la prueba.
printProof :: Int -> TypeDefs -> FTypeContext -> [SubProof] -> Doc
printProof tp op ftc sb =
  (text $ "Hay " ++ show tp ++ " sub pruebas.\n") $$
  printContext op (ftc, bTypeContext s) (termContext s) $$
  printGoals tp op sb
  where s = head sb

-- Imprime el tipo objetivo de cada subprueba.
printGoals :: Int -> TypeDefs -> [SubProof] -> Doc
printGoals = printGoals' 1

printGoals' :: Int -> Int -> TypeDefs -> [SubProof] -> Doc
printGoals' _ _ _ [] = empty
printGoals' i tp op (s:sb) =
  printLevelGoals i tp op (ty s) $$
  printGoals' (i+(lsubp s)) tp op sb

-- Imprime los tipos objetivos de cada nivel.
printLevelGoals :: Int -> Int -> TypeDefs -> [Maybe DoubleType] -> Doc
printLevelGoals _ _ _ [] =
  empty
printLevelGoals i tp op (t:ts) =
  (text $ "___________________["++(show i)++"/"++(show tp)++"]") $$
  printGoal op t $$
  printLevelGoals (i+1) tp op ts

printGoal :: TypeDefs -> Maybe DoubleType -> Doc
printGoal op (Just ty) = printType op ty
printGoal _ Nothing = text "*"

printContext :: TypeDefs -> (FTypeContext, BTypeContext) -> TermContext -> Doc
printContext op (ftc,btc) c =
  printFTypeContext ftc $$
  printRestContext op btc c

printFTypeContext :: FTypeContext -> Doc
printFTypeContext = foldr (\x r -> printFTypeVar x $$ r) empty

printFTypeVar :: FTypeVar -> Doc
printFTypeVar x = text x

printRestContext :: TypeDefs -> BTypeContext -> TermContext -> Doc
printRestContext op btc c
  | S.null btc = printRestTermC op c
  | S.null c = printRestBTypeC btc
  | otherwise = let x = S.index btc 0
                    y = S.index c 0
                in if snd x > (\(_,w,_,_) -> w) y
                   then printRestContext op (S.drop 1 btc) c $$
                        printBTypeVar x
                   else printRestContext op btc (S.drop 1 c) $$
                        printTermVar op y

printRestTermC :: TypeDefs -> TermContext -> Doc
printRestTermC op c
  | S.null c = empty
  | otherwise = printRestTermC op (S.drop 1 c) $$
                printTermVar op (S.index c 0)

printRestBTypeC :: BTypeContext -> Doc
printRestBTypeC btc
  | null btc = empty
  | otherwise = printRestBTypeC (S.drop 1 btc) $$
                printBTypeVar (S.index btc 0)

printTermVar :: TypeDefs -> TermVarWithType -> Doc
printTermVar op (h,_,_,Just t) =
  text h <+>
  text ":" <+>
  printType op t

printBTypeVar :: BTypeVar -> Doc
printBTypeVar (x, _) = text x

--------------------------------------------------------------------------------------------  
-- Comando Help

--TERMINAR
helpMessage :: [(String, String)]
helpMessage = [("Variables <var>, <var>, ...",
               "Declaración de variables proposicionales.\n"),
               ("<op> <var> <var> ... = <logic term>",
               "Declaración de un operador lógico prefijo.\n"),
               ("<var> <sym> <var> = <logic term>",
               "Declaración de un operador lógico binario infijo.\n"),
               ("<name> = <lambda term>",
               "Declaración de un lambda término.\n"),
               ("<name> : <logic term>",
               "Declaración de un lambda término vacio.\n"),
               ("Theorem <name> : <logic term>",
               "Inicia la prueba de un teorema.\n"),
               ("<tactic>",
               "Táctica de una prueba.\n"),
               ("Axiom <name> : <logic term>",
               "Se asume un axioma.\n"),
               ("Print <name>",
               "Imprime el lambda término asociado.\n"),
               ("Check <lambda term>",
               "Infiere el tipo del lambda término.\n"),
               (":load <files>",
               "Carga de archivos.\n"),
               (":save <file>",
                "Guarda el historial de comandos exitosos.\n"),
               (":abort",
               "Cancela la prueba de un teorema.\n"),
               (":quit",
               "Salir.\n"),
               (":help",
               "Imprime este mensaje de ayuda.\n"),
               ("Todos los comandos no escapados deben finalizar con ';'","")
               ]

help :: String
help =
  concat $ map (\(x,y) -> x ++ replicate ((40 - length x) `max` 2) ' ' ++ y) helpMessage  

--------------------------------------------------------------------------------------------  
-- Comando Print

printPrintComm :: TypeDefs -> DoubleLTerm -> Maybe DoubleLTerm -> DoubleType -> Doc
printPrintComm = printComm

printComm :: TypeDefs -> DoubleLTerm -> Maybe DoubleLTerm -> DoubleType -> Doc
printComm tyd var (Just te) ty =
  sep $
  printLTerm tyd var <+>
  text "=" :
  [printLTermWithType te ty tyd] 
printComm tyd var Nothing ty =
  printLTermWithType var ty tyd


printLTermWithType :: DoubleLTerm -> DoubleType -> TypeDefs -> Doc
printLTermWithType te ty op =
  sep $
  printLTerm op te <+>
  text ":" :
  [printType op ty]

printPrintAllComm :: LamDefs -> TypeDefs -> Doc
printPrintAllComm ted tyd =
  foldr (\name r -> (text "." <+> printCommType name) $$ r ) empty (getTypesNames tyd) $$
  foldr (\(name, (mte, ty)) r -> printPrintAllComm' tyd (lambTermVar name) (isJust mte) ty $$ r)
  empty (getLamTable ted)

printPrintAllComm' :: TypeDefs -> DoubleLTerm -> Bool -> DoubleType -> Doc
printPrintAllComm' tyd name theorem ty =
  (if theorem then text "-" else text "*") <+>
  printComm tyd name Nothing ty

printCommType :: String -> Doc
printCommType name =
  text name <+>
  text ":: *"

--------------------------------------------------------------------------------------------  
-- Impresión de la prueba de un teorema.

printTheorem :: TypeDefs -> String -> DoubleType -> [String] -> Doc
printTheorem td name t xs =
  text "Theorem" <+>
  text name <+>
  text ":" <+>
  printType td t <>
  text ";" $$
  nest 2 (printTactics xs)
  
printTactics :: [String] -> Doc
printTactics xs = foldl (\r x -> text x $$ r) empty xs

--------------------------------------------------------------------------------------------  
-- Impresión de mensajes exitosos de comandos.
msjFilesOk :: [String] -> Doc
msjFilesOk files =
  sep $
  text "Archivos cargados:" :
  commaSeparate files

commaSeparate :: [String] -> [Doc]
commaSeparate [] = [empty]
commaSeparate [x] =
  [text x]
commaSeparate (x:xs) =
  text x <>
  text "," :
  commaSeparate xs

msjVarsOk :: [String] -> Doc
msjVarsOk vars =
  sep $
  text "Variables asumidas:" :
  commaSeparate vars
