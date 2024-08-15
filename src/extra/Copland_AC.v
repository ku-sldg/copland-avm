Require Import Manifest Term_Defs_Core.

Inductive Permission: Set :=
| READ
| WRITE
| EXECUTE.
    
Inductive Object: Set :=
| asp_obj:  Plc -> ASP_ID -> Object
| plc_obj:  Plc -> Object
| targ_obj: Plc -> TARG_ID -> Object.

(* 
    asp:
        READ - view all incoming EvidenceT to specific ASP
        WRITE - corrupt specific asp (including tampering w/ EvidenceT)
        EXECUTE - invoke specific ASP via CVM

    plc:
        READ - view everything at a place
        WRITE - corrupt everything at a place
        EXECUTE - invoke an AM (all of its ASPs)

    targ:
        READ - view a specific target (e.g. eavesdrop, measure, ...)
        WRITE - corrupt specific target
        EXECUTE - ?
   
 *)


Definition AC_Policy := Permission -> Object -> bool.
