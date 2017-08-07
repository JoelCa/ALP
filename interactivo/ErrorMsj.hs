module ErrorMsj where

import Common
import Text.PrettyPrint
import PrettyPrinter (printType, printLTerm)
import Hypothesis (printHypothesis)
import Text.Megaparsec (parseErrorPretty)

printError :: FOperations -> ExceptionPos -> Doc
printError op (_, e@(SyntaxE _)) =
  errorMessage op e
printError op ((file,pos), e) =  
  filePos file pos $$
  errorMessage op e 

printErrorNoPos :: FOperations -> ExceptionPos -> Doc
printErrorNoPos op (_, e) = errorMessage op e 

filePos :: String -> Int -> Doc
filePos file line =
  text file <>
  colon <>
  int line <>
  colon

-- Mensajes de error.
errorMessage :: FOperations -> ProofException -> Doc
errorMessage _ (SyntaxE e) = sep $
                             text "error de sintaxis." :
                             [text $ parseErrorPretty e]
errorMessage _ (FileE e) = text $ show $ e
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
errorMessage _ CommandInvalid =
  text "error: comando inválido."
errorMessage _ EmptyType =
  text "error: comando inválido. Debe ingresar un tipo."
errorMessage _ (TypeRepeated s) =
  text "error:" <+>
  quotes (text s) <+>
  text "repetida."
errorMessage _ (TypeNotExists s) =
  text "error:" <+>
  quotes (text s) <+>
  text "no existe en el entorno."
errorMessage _ (OpE1 s) =
  text "error: cantidad de operandos en la operación" <+>
  quotes (text s) <>
  char '.'
errorMessage _ (OpE2 s) =
  text "error: la operación" <+>
  quotes (text s) <+>
  text "no existe."
errorMessage op (ExactE1 ty) =
  text "error: el término ingresado no tiene el tipo" <+>
  printType op ty <>
  char '.'
errorMessage op (ExactE2 ty) =
  text "error: debe ingresar una prueba de" <+>
  printType op ty <>
  char '.'
errorMessage _ ExactE3 =
  text "error: lo ingresado no es válido."
errorMessage _ PSE =
  text "error: operación sobre el estado interno inválida."
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
  text "no es un operador foldeable."
errorMessage _ (HypoE i) =
  text "error: la hipótesis" <+>
  quotes (text $ printHypothesis i) <+>
  text "no existe."

  
errorInfer :: FOperations -> InferException -> Doc
errorInfer _ (InferE1 x) =
  text "La variable de término" <+>
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

errorInfer' :: FOperations -> DoubleLTerm -> Doc -> Doc
errorInfer' op te s =
  sep $
  text "Se esperaba el tipo" <+>
  quotes s <+>
  comma <+>
  text "en el término" :
  [ quotes (printLTerm op te) <>
    char '.' ]
