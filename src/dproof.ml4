open Pp
open Reproof
open Constrarg

VERNAC COMMAND EXTEND DProof CLASSIFIED AS QUERY
  | [ "DProof" ]  -> [ record () ]
  | [ "DAbort"] -> [ stop (); reset () ]
  | [ "DEnd" ] -> [ stop (); start (); reset () ]
  | [ "Set" "Term" ] -> [ term := not !term ]
END