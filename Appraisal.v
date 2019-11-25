Require Import ConcreteEvidence.
Require Import Maps OptMonad.

Require Import List.
Import ListNotations.

Inductive App_Instr: Set :=
| asp_app: ASP_ID -> (list Arg) -> BS -> App_Instr
| g_app: Plc -> BS -> EvidenceC -> App_Instr
| h_app: BS -> EvidenceC -> App_Instr
| n_app: N_ID -> BS -> App_Instr.

Fixpoint app_compile (e:EvidenceC) : list App_Instr :=
  match e with
  | mtc => []
  | uuc i args bs e' => [asp_app i args bs] ++ (app_compile e')
  | ggc p bs e' => [g_app p bs e'] ++ (app_compile e')                   
  | hhc bs e' => [h_app bs e'] ++ (app_compile e')
  | nnc n_id bs e' => [n_app n_id bs] ++ (app_compile e')
  | ssc e1 e2 => (app_compile e1) ++ (app_compile e2)
  | ppc e1 e2 => (app_compile e1) ++ (app_compile e2)
  end.

Notation Pri_Key := nat (only parsing).

Definition pri_keys : Map Plc Pri_Key. Admitted.
Definition golden_measurements : Map (ASP_ID*list Arg) BS. Admitted.
Definition nonce_map : Map N_ID BS. Admitted.

(* params: id -> golden -> actual *)
Definition check_measurement : (ASP_ID*list Arg) -> BS -> BS -> bool. Admitted.
Definition encode_ev : EvidenceC -> BS. Admitted.
(* params: encoded payload -> private key -> signature *)
Definition check_sig : BS -> Pri_Key -> BS -> bool. Admitted.

Definition check_ev_sig (e:EvidenceC) (k:Pri_Key) (sig:BS) : bool :=
  let payload := encode_ev e in
  check_sig payload k sig.

(* params: payload -> hash *)
(* TODO: incorporate hash algorithm choice (policy) here? *)
Definition check_hash : BS -> BS -> bool. Admitted.

Definition check_ev_hash (e:EvidenceC) (bs:BS) : bool :=
  let payload := encode_ev e in
  check_hash payload bs.

Check Nat.eqb.

Definition check_nonce (n : N_ID) (bs:BS) : option bool :=
  g_bs <- map_get nonce_map n ;;
       ret (Nat.eqb bs g_bs).  


Definition check_asp (x:ASP_ID*list Arg) (m:BS) : option bool :=
  g_bs <- (map_get golden_measurements x) ;;
       ret (check_measurement x g_bs m).

Fixpoint appraise (e:EvidenceC) : option bool :=
  match e with
  | mtc => Some true
  | uuc i args bs e =>
    b <- check_asp (i,args) bs ;;
      res <- appraise e ;;
      ret (andb b res)
  | ggc p sig e =>
    k <- map_get pri_keys p ;;
      let b := check_ev_sig e k sig in
      res <- appraise e ;;
          ret (andb b res)
  | hhc h e =>
    let b := check_ev_hash e h in
      res <- appraise e ;;
          ret (andb b res)
  | nnc n_id bs e =>
    b <- check_nonce n_id bs ;;
      res <- appraise e ;;
      ret (andb b res)
  | ssc e1 e2 =>
    res1 <- appraise e1 ;;
         res2 <- appraise e2 ;;
         ret (andb res1 res2)
  | ppc e1 e2 =>
    res1 <- appraise e1 ;;
         res2 <- appraise e2 ;;
         ret (andb res1 res2)
  end.
    
    

