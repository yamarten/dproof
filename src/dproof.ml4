open Pp
open Reproof
open Constrarg

VERNAC COMMAND EXTEND DProof CLASSIFIED AS QUERY
  | [ "DProof" ]  -> [ record () ]
  | [ "DAbort"] -> [ stop (); reset () ]
  | [ "DEnd" ] -> [ stop (); start (); reset () ]
  | [ "DQed" ] -> [ stop (); (if !term then start_term else start) (); reset (); Vernacentries.interp (Loc.dummy_loc,  VernacEndProof (Proved (Opaque None,None)))]
  | [ "Set" "Term" ] -> [ term := not !term ]
END