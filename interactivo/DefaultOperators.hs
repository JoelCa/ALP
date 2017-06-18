module DefaultOperators where

import Common

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

not_op :: FoldeableOp
not_op = (not_text,
          (ForAll "a" $ Fun (B "a") $ RenameTy bottom_text 0 []
          , TForAll $ TFun (TBound 0) $ RenameTTy bottom_code [])
         , 1
         , False)

iff_op :: FoldeableOp
iff_op = (iff_text
         , (ForAll "a" $ ForAll "b" $ RenameTy and_text 1
            [Fun (B "a") (B "b"), Fun (B "b") (B "a")]
           , TForAll $ TForAll $ RenameTTy and_code
             [TFun (TBound 1) (TBound 0), TFun (TBound 0) (TBound 1)])
         , 2
         , True)

