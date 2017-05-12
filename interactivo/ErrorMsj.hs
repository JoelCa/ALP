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
errorMessage _ (PExist s) = "error: " ++ s ++ " ya existe."
errorMessage _ (PNotExist s) =  "error: " ++ s ++ " no existe."
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
errorMessage _ (TypeRepeated1 s) = "error: \""++ s ++"\" repetida."
errorMessage _ (TypeRepeated2 s) = "error: \""++ s ++"\" ya existe."
errorMessage _ (TypeNotExists s) =  "error: \""++ s ++"\" no existe en el entorno."
errorMessage _ (OpE1 s) = "error: cantidad de operandos en la operación \""++ s ++"\"."
errorMessage _ (OpE2 s) = "error: la operación \""++ s ++"\" no existe."
errorMessage op (ExactE1 ty) =
  "error: el término ingresado no tiene el tipo \"" ++
  render (printType op ty) ++ "\". "
errorMessage op (ExactE2 ty) =
  "error: debe ingresar una prueba de \"" ++
  render (printType op ty) ++ "\". "
errorMessage _ PSE = "error: operación sobre el estado interno inválida"
errorMessage _ (TypeE x) =  "error: el tipo \"" ++ x ++ "\" no fue declarado."
errorMessage _ (InferE1 x) = "error: la variable de término \"" ++ x ++ "\" no fue declarada."
errorMessage op (InferE2 te ty) = errorInferPrintTerm op te $ render (printType op ty)
errorMessage op (InferE3 te s) = errorInferPrintTerm op te s
errorMessage op (InferE4 te) =
  "error: tipo inesperado, en el término \""
  ++ render (printLamTerm op te) ++ "\"."
errorMessage op (DefE s) = "error: " ++ s ++ " es un operador que ya existe."
errorMessage _ (UnfoldE1 s) =  "error: " ++ s ++ " no es un operador foldeable."
errorMessage _ (HypoE i) = "error: la hipótesis " ++ printHypothesis i ++ " no existe."

errorInferPrintTerm :: FOperations -> LamTerm -> String -> String
errorInferPrintTerm op te s =
  "error: se esperaba el tipo \"" ++ s ++
  "\", en el término \"" ++
  render (printLamTerm op te) ++ "\"."
