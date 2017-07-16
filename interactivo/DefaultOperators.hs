module DefaultOperators where

import Common

  -- Conjunto de operaciones NO "foldeables".
notFoldeableOps :: [NotFoldeableOp]
notFoldeableOps = [and_, or_, bottom_]

isNotFoldeableOp :: String -> Bool
isNotFoldeableOp name = any (\(x,_) -> x == name) notFoldeableOps

  -- Operaciones por default, NO "foldeables", donde:
  -- 1. Nombre de la operación.
  -- 2. Cantidad de operandos (a lo sumo 2).
and_ = (['/','\\'] , 2)
or_ = (['\\','/'], 2)
bottom_ = ("False", 0)

and_id = fst and_
or_id = fst or_
bottom_id = fst bottom_

  -- Operaciones por default, "foldeables".  
not_id = "~"
iff_id = "<->"

not_op :: FoldeableOp
not_op = ( not_id
         , ForAll "a" $ Fun (TVar ("a", Bound 0)) $ RenamedType bottom_id []
         , 1
         , False
         )

iff_op :: FoldeableOp
iff_op = ( iff_id
         , ForAll "a" $ ForAll "b" $ RenamedType and_id
           [ Fun (TVar ("a", Bound 1)) (TVar ("b", Bound 0))
           , Fun (TVar ("b", Bound 0)) (TVar ("a", Bound 1))
           ]
         , 2
         , True
         )

