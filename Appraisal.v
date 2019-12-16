Require Import ConcreteEvidence.
Require Import Maps OptMonad.

Require Import List.
Import ListNotations.

Inductive App_Instr: Set :=
| asp_app: ASP_ID -> BS -> App_Instr
| g_app: Plc -> BS -> EvidenceC -> App_Instr
| h_app: BS -> EvidenceC -> App_Instr
| n_app: N_ID -> BS -> App_Instr.

Fixpoint app_compile (e:EvidenceC) : list App_Instr :=
  match e with
  | mtc => []
  | uuc i bs e' => [asp_app i bs] ++ (app_compile e')
  | ggc p bs e' => [g_app p bs e'] ++ (app_compile e')                   
  | hhc bs e' => [h_app bs e'] ++ (app_compile e')
  | nnc n_id bs e' => [n_app n_id bs] ++ (app_compile e')
  | ssc e1 e2 => (app_compile e1) ++ (app_compile e2)
  | ppc e1 e2 => (app_compile e1) ++ (app_compile e2)
  end.

Notation Pri_Key := nat (only parsing).

Definition pri_keys : Map Plc Pri_Key. Admitted.
Definition golden_measurements : Map ASP_ID BS. Admitted.
Definition nonce_map : Map N_ID BS. Admitted.

(* params: id -> golden -> actual *)
Definition check_measurement : ASP_ID -> BS -> BS -> bool. Admitted.
Definition encode_ev : EvidenceC -> BS. Admitted.
(* params: encoded payload -> private key -> signature *)
Definition check_sig : BS -> Pri_Key -> BS -> bool. Admitted.

Definition check_ev_sig (e:EvidenceC) (k:Pri_Key) (sig:BS) : bool :=
  let payload := encode_ev e in
  check_sig payload k sig.

Definition check_ev_pl (e:EvidenceC) (p:Plc) (sig:BS) : option bool :=
  k <- map_get pri_keys p ;;
    ret (check_ev_sig e k sig).

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


Definition check_asp (x:ASP_ID) (m:BS) : option bool :=
  g_bs <- (map_get golden_measurements x) ;;
       ret (check_measurement x g_bs m).

Fixpoint appraise (e:EvidenceC) : option bool :=
  match e with
  | mtc => Some true
  | uuc i bs e =>
    b <- check_asp i bs ;;
      res <- appraise e ;;
      ret (andb b res)
  | ggc p sig e =>
    b <- check_ev_pl e p sig ;;
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

Definition appraiseI' (i:App_Instr): option bool :=
  match i with
  | asp_app x bs => check_asp x bs
  | g_app p bs e' => check_ev_pl e' p bs
  | h_app bs e' => Some (check_ev_hash e' bs)
  | n_app nid bs => check_nonce nid bs
  end.

Fixpoint appraiseI (o:option bool) (i:App_Instr): option bool :=
  b <- o ;;
    b' <- appraiseI' i ;;
    ret (andb b b').
    
Check fold_left.
Definition run_app (il:list App_Instr) : option bool :=
  fold_left appraiseI il (Some true).
    

Theorem app_eq_appI: forall e,
    let il := app_compile e in
    appraise e = run_app il.
Abort.

Require Import StVM Instr VmSemantics.

Definition mt_st := mk_st mtc [] [] 0 [].

Theorem can_app: forall t,
    let att_il := instr_compiler t in
    let ev_res := run_vm_t t mt_st in
    let app_il := app_compile (st_ev ev_res) in
    let optB := run_app app_il in
    exists b, optB = Some b.
Abort.
    