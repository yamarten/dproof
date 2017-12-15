open Pp
open Reproof
open Constrarg
open Stdarg

VERNAC COMMAND EXTEND DProof CLASSIFIED AS QUERY
  | [ "DProof" ]  -> [ record () ]
  | [ "DAbort"] -> [ stop (); reset () ]
  | [ "DEnd" ] -> [ stop (); start (); reset () ]
  | [ "Set" "DProof" "Term" ] -> [ term := not !term ]
  | [ "Set" "DProof" "File" string(p) ] -> [file := Some (open_out (p^".v"))]
  | [ "Set" "DProof" "Stdout" ] -> [file := None]
END