(* Encoding of the RESOLUTE logic (and RESOLUTE to Copland translator) in coq *)

Require Export String Maps EqClass ResultT.
Require Export List.

Require Import Term_Defs_Core Term_Defs_Core_Ops Cvm_Utils.

Require Import ID_Type.

Import ListNotations.


Definition TargetT := ID_Type.

Inductive Resolute : Type :=
  | R_False
  | R_True
  | R_Goal (t:TargetT) (* (args:list Args) *)
  | R_And (G1 : Resolute) (G2 : Resolute)
  | R_Or (G1 : Resolute) (G2 : Resolute)
  | R_Imp (G1 : Resolute) (G2 : Resolute).
  (*
  | R_Forall (ls:list TargetT)  (G : TargetT -> Resolute)
  | R_Exists (ls:list TargetT) (G : TargetT -> Resolute).
  *)

Definition Assumption := Resolute.
Definition Assumptions := list (Assumption).

(* Extending Assumptions operation (Comma operator in Sequent Calculus).  
   Leaving its implementation abstract for now... *)
Definition Comma (ls:Assumptions) (ls':Assumptions) : Assumptions.
Admitted.

Inductive Reval : Assumptions -> Resolute -> Prop :=
  | Reval_L : forall A R,
    In R_False A -> Reval A R

  | Reval_R : forall A,
    Reval A R_True

  | Reval_ID : forall A R, 
    Reval (Comma A [R]) R
 
  | Reval_And_Intro : forall A R1 R2,
    Reval A R1 -> Reval A R2 -> Reval A (R_And R1 R2)
  
  | Reval_And_Elim : forall A R1 R2 R3,  
    Reval (Comma A [R1;R2]) R3 -> 
    Reval (Comma A [(R_And R1 R2)]) R3

  | Reval_Or_Intro_L : forall A R1 R2,
    (Reval A R1) -> Reval A (R_Or R1 R2)

  | Reval_Or_Intro_R : forall A R1 R2,
    (Reval A R2) -> Reval A (R_Or R1 R2)

  | Reval_Or_Elim : forall A R1 R2 R3, 
    Reval (Comma A [R1]) R3 -> 
    Reval (Comma A [R2]) R3 -> 
    Reval (Comma A [R_Or R1 R2]) R3

  | Reval_Imp_Intro : forall A R1 R2, 
    Reval (Comma A [R1]) R2 -> 
    Reval A (R_Imp R1 R2)

  | Reval_Imp_Elim : forall A R1 R2 R3, 
    Reval A R1 -> 
    Reval (Comma A [R2]) R3 -> 
    Reval (Comma A [R_Imp R1 R2]) R3.

    (*
  | Reval_Forall_Intro : forall (A:Assumptions) 
    (tp:list TargetT) (pred: TargetT -> Resolute),      
      (forall (v:TargetT), 
        In v tp -> 
        Reval A (pred v)) ->
      
      Reval A (R_Forall tp pred)

  | Reval_Forall_Elim : forall (A:Assumptions) 
      (tp:list TargetT) (pred: TargetT -> Resolute) R3,    
        (forall (v:TargetT), 
          In v tp -> 
          Reval (Comma A [pred v]) R3) -> 

        Reval (Comma A [(R_Forall tp pred)]) R3

  | Reval_Exists_Intro : forall (A:Assumptions)
    (tp:list TargetT) (pred: TargetT -> Resolute),      
      (exists (v:TargetT), 
        In v tp -> 
        Reval A (pred v)) ->
      Reval A (R_Exists tp pred)

  | Reval_Exists_Elim : forall (A:Assumptions)
    (tp:list TargetT) (pred: TargetT -> Resolute) R3,      
      (exists (v:TargetT), 
        In v tp -> 
        Reval (Comma A [(pred v)]) R3) ->
      Reval (Comma A [(R_Exists tp pred)]) R3.

    *)

Open Scope string.

Definition mt_ASP_ID : ASP_ID := "mtTerm".
Definition mt_Plc : Plc := "mtPlc".
Definition mt_TARG_ID : Plc := "mtTarg".

Close Scope string.

Definition mtTerm : Term := 
  asp (ASPC (asp_paramsC mt_ASP_ID [] mt_Plc mt_TARG_ID)).


Record Model := {
  conc : TargetT -> Term ;
  spec : TargetT -> (Evidence -> bool) ;
  context : GlobalContext
}.

(*
Global Instance EqClass_TargetT : EqClass TargetT.
Admitted.
*)

(*
Inductive Evidence :=
| evc: RawEv -> EvidenceT -> Evidence.
*)

Import ResultNotation.

Definition err_str_split_evidence_not_split' := "Error in split_t*, type of evidence passed into a split is not a split evidence type"%string.

Definition split_t1 (M:Model) (e:Evidence) : ResultT Evidence string :=
  match e with 
  | evc rawEv et => 
    match et with 
    | split_evt et1 et2 => 
      n <- et_size (context M) et1 ;;
      '(rawEv1, _) <- peel_n_rawev n rawEv ;;
      resultC (evc rawEv1 et1)
    | _ => errC err_str_split_evidence_not_split'
    end 
  end.

Definition split_t2 (M:Model) (e:Evidence) : ResultT Evidence string :=
match e with 
| evc rawEv et => 
  match et with 
  | split_evt et1 et2 => 
    n <- et_size (context M) et1 ;;
    '(_, rawEv2) <- peel_n_rawev n rawEv ;;
    resultC (evc rawEv2 et2)
  | _ => errC err_str_split_evidence_not_split'
  end 
end.

Definition split_t1_default (M:Model) (e:Evidence) : Evidence :=
  match (split_t1 M e) with 
  | resultC e' => e' 
  | _ => evc [] (get_et e)
  end.

Definition split_t2_default (M:Model) (e:Evidence) : Evidence :=
  match (split_t2 M e) with 
  | resultC e' => e' 
  | _ => evc [] (get_et e)
  end.


Fixpoint res_to_copland (M : Model) (r:Resolute) (m:Map TargetT Evidence) 
  : (Term * (Evidence -> bool)) :=
  match r with 
  | R_False => (mtTerm, fun _ => false)
  | R_True =>  (mtTerm, fun _ => true)

  | (R_Goal tid) => 
     match (map_get tid m) with 
     | None => (conc M tid, fun e => (spec M tid e))
     | Some e => (mtTerm, fun _ => (spec M tid e))
     end

  | R_And r1 r2 => 
    let '(t1, pol1) := res_to_copland M r1 m in
    let '(t2, pol2) := res_to_copland M r2 m in
    ((bseq (NONE,NONE) t1 t2), fun e => 
      andb (pol1 (split_t1_default M e)) (pol2 (split_t2_default M e)))

  | R_Or r1 r2 => 
    let '(t1, pol1) := res_to_copland M r1 m in
    let '(t2, pol2) := res_to_copland M r2 m in
    (bseq (NONE,NONE) t1 t2, fun e => 
      orb (pol1 (split_t1_default M e)) (pol2 (split_t2_default M e)))

  | R_Imp r1 _ => 
    (* TODO:  should we check assumptions/prior evidence cache here? *)
    let '(t1, pol1) := res_to_copland M r1 m in
    (t1, fun e => pol1 e)
    end.
