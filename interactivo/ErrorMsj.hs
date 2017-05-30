module ErrorMsj where

import Common
import Text.PrettyPrint.HughesPJ (render)
import PrettyPrinter (printType, printLamTerm)
import Hypothesis (printHypothesis)

-- Mensajes de error.
errorMessage :: FOperations -> ProofExceptions -> String
errorMessage _ SyntaxE = "error de sintaxis."
errorMessage _ PNotFinished = "error: prueba no terminada."
errorMessage _ PNotStarted = "error: prueba no comenzada."
errorMessage _ (ExistE s) = "error: \""++ s ++"\" ya existe."
errorMessage _ (NotExistE s) =  "error: \""++ s ++"\" no existe."
errorMessage _ AssuE = "error: comando assumption mal aplicado."
errorMessage _ IntroE1 = "error: comando intro mal aplicado."
errorMessage op (ApplyE1 t1 t2) =
  "error: comando apply mal aplicado, \"" ++
  (render $ printType op t1) ++  "\" no coincide con \"" ++
  (render $ printType op t2) ++ "\"."
errorMessage _ Unif1 = "error: unificación inválida 1."
errorMessage _ Unif2 = "error: unificación inválida 2."
errorMessage _ Unif3 = "error: unificación inválida 3."
errorMessage _ Unif4 = "error: unificación inválida 4."
errorMessage _ ElimE1 = "error: comando elim mal aplicado."
errorMessage _ CommandInvalid = "error: comando inválido."
errorMessage _ EmptyType = "error: comando inválido (debe añadir una fórmula mediante \"exact\")."
errorMessage _ (TypeRepeated s) = "error: \""++ s ++"\" repetida."
errorMessage _ (TypeNotExists s) =  "error: \""++ s ++"\" no existe en el entorno."
errorMessage _ (OpE1 s) = "error: cantidad de operandos en la operación \""++ s ++"\"."
errorMessage _ (OpE2 s) = "error: la operación \""++ s ++"\" no existe."
errorMessage op (ExactE1 ty) =
  "error: el término ingresado no tiene el tipo \"" ++
  render (printType op ty) ++ "\". "
errorMessage op (ExactE2 ty) =
  "error: debe ingresar una prueba de \"" ++
  render (printType op ty) ++ "\"."
errorMessage _ ExactE3 =
  "error: lo ingresado no es válido."
errorMessage _ PSE = "error: operación sobre el estado interno inválida."
errorMessage _ (TypeE x) =  "error: el tipo \"" ++ x ++ "\" no fue declarado."
errorMessage op (InferE te e) =
  "error: en el término \"" ++
  render (printLamTerm op te) ++
  "\". " ++
  errorInfer op e
errorMessage op (DefE1 s) = "error: " ++ s ++ " es un operador que ya existe."
errorMessage op DefE2 = "error: lo ingresado no es válido."
errorMessage _ (UnfoldE1 s) =  "error: " ++ s ++ " no es un operador foldeable."
errorMessage _ (HypoE i) = "error: la hipótesis " ++ printHypothesis i ++ " no existe."
  

errorInfer :: FOperations -> InferExceptions -> String
errorInfer _ (InferE1 x) =
  "La variable de término \"" ++ x ++ "\" no fue declarada."
errorInfer op (InferE2 te ty) =
  errorInfer' op te $ render $ printType op ty
errorInfer op (InferE3 te s) =
  errorInfer' op te s
errorInfer op (InferE4 te) =
  "error: tipo inesperado, en el término \""
  ++ render (printLamTerm op te) ++ "\"."

errorInfer' :: FOperations -> LamTerm -> String -> String
errorInfer' op te s =
  "Se esperaba el tipo \"" ++ s ++
  "\", en el término \"" ++
  render (printLamTerm op te) ++ "\"."
