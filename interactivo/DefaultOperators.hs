module DefaultOperators where

import Common
import Data.Sequence (Seq)


  -- Conjunto de operaciones NO "foldeables".
notFoldeableOps :: [NotFoldeableOp]
notFoldeableOps = [and_, or_, bottom_]

  -- Operaciones por default, NO "foldeables", donde:
  -- 1. Texto de la operación.
  -- 2. Código que identifica a la operación.
  -- 3. Cantidad de operandos (a lo sumo 2).
and_ = (['/','\\'] , -1, 2)
or_ = (['\\','/'], -2, 2)
bottom_ = ("False", -3, 0)

and_text = fst3 and_
or_text = fst3 or_
bottom_text = fst3 bottom_

and_code = snd3 and_
or_code = snd3 or_
bottom_code = snd3 bottom_

  -- Operaciones por default, "foldeables".
not_text = "~"
iff_text = "<->"

iff_code = 1 :: Int
not_code = 0 :: Int
