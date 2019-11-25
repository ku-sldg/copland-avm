Require Import ConcreteEvidence.

Require Import List.
Import ListNotations.

Inductive App_Instr: Set :=
| asp_app: ASP_ID -> (list Arg) -> BS -> App_Instr
| g_app: EvidenceC -> BS -> Plc -> App_Instr
| h_app: EvidenceC -> BS -> App_Instr
| n_app: Plc -> N_ID -> BS -> App_Instr.

Fixpoint app_compile (e:EvidenceC) : list App_Instr :=
  match e with
  | mtc => []
  | uuc i args bs e' => [asp_app i args bs] ++ (app_compile e')
  | ggc e' bs => [g_app e' bs
  | _ => []
  end.
    