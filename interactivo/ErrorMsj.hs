module ErrorMsj where

import Common
import TypeDefinition (TypeDefs)
import Text.PrettyPrint
import PrettyPrinter (printType, printLTerm)
import Text.Megaparsec (parseErrorPretty)

printError :: TypeDefs -> ProverExceptionPos -> Doc
printError op (SemanticE ((file,pos), e)) =  
  filePos file pos $$
  errorMessage op e 
printError _ (SyntaxE e) =
  sep $
  (text $ parseErrorPretty e) :
  [text "error de sintaxis."]
printError _ (FileE e) =
  text $ show $ e


filePos :: String -> Int -> Doc
filePos file line =
  text file <>
  colon <>
  int line <>
  colon <>
  int 1 <>
  colon
  
-- Mensajes de errores.
errorMessage :: TypeDefs -> SemanticException -> Doc
errorMessage _ PNotFinished =
  text "error: prueba no terminada."
errorMessage _ PNotStarted =
  text "error: prueba no comenzada."
errorMessage _ (ExistE s) =
  text "error:" <+>
  quotes (text s) <+>
  text "ya existe."
errorMessage _ (NotExistE s) =
  text "error:" <+>
  quotes (text s) <+>
  text "no existe."
errorMessage _ AssuE =
  text "error: comando assumption mal aplicado."
errorMessage _ IntroE1 =
  text "error: comando intro mal aplicado."
errorMessage op (ApplyE1 t1 t2) =
  sep $
  text "error: comando apply mal aplicado." :
  quotes (printType op t1) :
  [ text "no coincide con " <+>
    quotes (printType op t2) <>
    char '.' ]
errorMessage _ Unif1 =
  text "error: unificación inválida 1."
errorMessage _ Unif2 =
  text "error: unificación inválida 2."
errorMessage _ Unif3 =
  text "error: unificación inválida 3."
errorMessage _ Unif4 =
  text "error: unificación inválida 4."
errorMessage _ ElimE1 =
  text "error: comando elim mal aplicado."
errorMessage _ InvalidCommand =
  text "error: comando inválido."
errorMessage _ EmptyType =
  text "error: comando inválido. Debe ingresar un tipo."
errorMessage _ (TypeRepeated s) =
  text "error:" <+>
  quotes (text s) <+>
  text "repetida."
errorMessage _ (OpE1 s) =
  text "error: cantidad de operandos en la operación" <+>
  quotes (text s) <>
  char '.'
errorMessage _ (OpE2 s) =
  text "error: la operación" <+>
  quotes (text s) <+>
  text "no existe."
errorMessage _ (TermVarE s) =
  text "error: se esperaba una variable de lambda término." <+> 
  quotes (text s) <+>
  text "es una variable tipo."  
errorMessage _ (TypeVarE s) =
  text "error: se esperaba una variable de tipo." <+>
  quotes (text s) <+>
  text "es una variable de lambda término."
errorMessage op (ExactE1 ty) =
  text "error: el término ingresado no tiene el tipo" <+>
  quotes (printType op ty) <>
  char '.'
errorMessage op (ExactE2 ty) =
  text "error: debe ingresar un término de tipo" <+>
  quotes (printType op ty) <>
  char '.'
errorMessage _ ExactE3 =
  text "error: lo ingresado no es válido."
errorMessage _ (TypeE x) =
  text "error: el tipo" <+>
  quotes (text x) <+>
  text "no fue declarado."
errorMessage op (InferE te e) =
  sep $
  text "error: en el término" <+>
  quotes (printLTerm op te) <>
  char '.' :
  [errorInfer op e]
errorMessage _ (UnfoldE1 s) =
  text "error:" <+>
  quotes (text s) <+>
  text "no es un operador."
errorMessage _ (HypoE i) =
  text "error: la hipótesis" <+>
  quotes (text $ printHypo i) <+>
  text "no existe."
errorMessage _ InvalidCompComm =
  text "error: comando compuesto inválido."
  
errorInfer :: TypeDefs -> InferException -> Doc
errorInfer _ (InferE1 x) =
  text "La variable de lambda término" <+>
  quotes (text x) <+>
  text "no fue declarada."
errorInfer op (InferE2 te ty) =
  errorInfer' op te $ printType op ty
errorInfer op (InferE3 te s) =
  errorInfer' op te $ text s
errorInfer op (InferE4 te) =
  text "error: tipo inesperado, en el término" <+>
  quotes (printLTerm op te) <>
  char '.'

errorInfer' :: TypeDefs -> DoubleLTerm -> Doc -> Doc
errorInfer' op te s =
  sep $
  text "Se esperaba el tipo" <+>
  quotes s <+>
  comma <+>
  text "en el término" :
  [ quotes (printLTerm op te) <>
    char '.' ]

printHypo :: Int -> String
printHypo i = "H" ++ show i
