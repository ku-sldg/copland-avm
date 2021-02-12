Require Import Term_Defs ConcreteEvidence.

Require Import Maps.
Require Import EqClass.

Require Import List.
Import ListNotations.

(*
Require Import RecordSet.
Import RecordSetNotations.
*)

Inductive Prim_Instr: Set :=
| copy: Prim_Instr
| umeas: ASP_ID -> list Arg -> Prim_Instr
| sign: Prim_Instr
| hash: Prim_Instr.

Inductive AnnoInstr: Set :=
| aprimInstr: nat -> Prim_Instr -> AnnoInstr
| aReq: nat -> nat -> VM_ID -> AnnoInstr
| aseq: AnnoInstr -> AnnoInstr -> AnnoInstr.

Definition asp_instr (a:ASP) : Prim_Instr :=
  match a with
  | CPY => copy
  | ASPC i args => umeas i args
  | SIG => sign
  | HSH => hash
  end.

Fixpoint instr_compiler (t:AnnoTerm) : AnnoInstr :=
  match t with
  | aasp (i,_) a => aprimInstr i (asp_instr a)
  | aatt (i,j) p q _ =>
    (aReq i (Nat.pred j) q)
  | alseq _ t1 t2 => aseq (instr_compiler t1) (instr_compiler t2)
  end.
    
Definition ev_asp_instr (x:nat) (pi:Prim_Instr) (e:EvidenceC) : EvidenceC :=
  match pi with
  | copy => e
  | umeas asp_id _ => (uuc asp_id x e)
  | sign => (ggc x e)
  | hash => (hhc x e)
  end.

Definition tr_asp_instr (x:nat) (p:Plc) (pi:Prim_Instr) :=
  match pi with
  | copy => Term_Defs.copy x p
  | umeas asp_id args => (Term_Defs.umeas x p asp_id args)
  | sign => Term_Defs.sign x p
  | hash => Term_Defs.hash x p
  end.


Inductive InstrSt: Set :=
| istop: VM_ID -> EvidenceC -> InstrSt
| iconf: AnnoInstr -> VM_ID -> EvidenceC -> InstrSt
| iWaitReq: VM_ID -> VM_ID -> AnnoInstr -> InstrSt
| iDoRem: InstrSt -> VM_ID -> InstrSt
| irpyWait: nat -> VM_ID -> VM_ID -> InstrSt.
(*| ils: InstrSt -> AnnoInstr -> InstrSt. *)

Fixpoint instrStID (iSt: InstrSt): VM_ID :=
  match iSt with
  | istop me _ => me
  | iconf _ me _ => me
  | iWaitReq _ me _ => me
  | iDoRem iSt' _ => instrStID iSt'
  | irpyWait _ me _ => me
  (*| ils iSt' _ => instrStID iSt' *)
  end.

Fixpoint instrStEvidence (iSt: InstrSt): EvidenceC :=
  match iSt with
  | istop _ e => e
  | iconf _ _ e => e
  | iWaitReq _ _ _ => mtc
  | iDoRem iSt' _ => instrStEvidence iSt'
  | irpyWait _ _ _ => mtc
  (*| ils iSt' _ => instrStEvidence iSt' *)
  end.
    



  

(*
Inductive AnnoInstr: Set :=
| aprimInstr: nat -> Prim_Instr -> AnnoInstr
| aReq: nat -> nat -> VM_ID -> VM_ID -> AnnoInstr
| aseq: AnnoInstr -> AnnoInstr -> AnnoInstr.
*)

Inductive hLoc : Set :=
| Empty : hLoc
| Full: (VM_ID * EvidenceC) -> hLoc.
    
Definition heap := hLoc.

Inductive Instr_step: InstrSt -> heap -> option Ev -> InstrSt -> heap -> Prop :=
| primStep: forall x pi p e h,
    Instr_step (iconf (aprimInstr x pi) p e) h
               (Some (tr_asp_instr x p pi))
               (istop p (ev_asp_instr x pi e)) h
| atReqStep: forall i p q e h j,
    Instr_step (iconf (aReq i j q) p e) h
               (Some (req i p q))
               (irpyWait j p q) (Full (q,e))
| atRpyStep: forall j p q e,
    Instr_step (irpyWait j p q) (Full (p,e))
               (Some (rpy j p q))
               (istop p e) Empty
| atWaitReq: forall p q ai e,
    Instr_step (iWaitReq p q ai) (Full (q,e))
               None
               (iDoRem (iconf ai q e) p) Empty
| atDoRemStep: forall iSt iSt' h h' ev them,
    Instr_step iSt h ev iSt' h' ->
    Instr_step (iDoRem iSt them) h ev (iDoRem iSt' them) h'
| atDoRemStop: forall p e them h,
    Instr_step (iDoRem (istop p e) them) h
               None
               (istop p e) (Full (them,e)).
(*| seqStart: forall x y p e h,
    Instr_step (iconf (aseq x y) p e) h
               None
               (ils (iconf x p e) y) h
| seqStep: forall st0 st1 ev x h h',
    Instr_step st0 h ev st1 h' ->
    Instr_step (ils st0 x) h ev (ils st1 x) h'
| seqStop: forall y p e h,
    Instr_step (ils (istop p e) y) h None (iconf y p e) h. *)
Hint Constructors Instr_step : core.

Require Import Coq.Arith.PeanoNat.


Definition add_server_at (fromPl:VM_ID) (toPl:VM_ID) (t:AnnoTerm)
           (s:MapC VM_ID InstrSt) : MapC VM_ID InstrSt :=
  let newServerSt := (iWaitReq fromPl toPl (instr_compiler t)) in
  map_set s toPl newServerSt.  (* TODO:  use map replace instead of set? *)
    
Fixpoint copland_compliment (t:AnnoTerm) (s:MapC VM_ID InstrSt): MapC VM_ID InstrSt :=
  match t with
  | aasp r a => s
                   
  | aatt (i,j) p q t' =>
    let s' := add_server_at p q t' s in
    copland_compliment t' s'
                 
  | alseq _ t1 t2 =>
    let s1 := copland_compliment t1 s in
    copland_compliment t2 s1
  end.

(* Indicates all servers bound in the map are in a "stop" state *)
Definition servers_done (servs:MapC VM_ID InstrSt) : Prop :=
  forall p s,
    bound_to servs p s ->
    exists e, s = istop p e.

Require Import Coq.Arith.EqNat.

Open Scope nat_scope.

Definition orchestrate_servers (t:AnnoTerm) : (MapC VM_ID InstrSt) :=
  copland_compliment t [].

Definition setup_main_code (t:AnnoTerm) (p:Plc) (e:EvidenceC) : InstrSt :=
  iconf (instr_compiler t) p e.

Definition WorldTerm := MapC VM_ID InstrSt.

Definition build_world_term_anno (t:AnnoTerm) (p:Plc) (e:EvidenceC) : WorldTerm :=
  let main := setup_main_code t 0 e in
  let servers := orchestrate_servers t p in
  map_set servers 0 main.

Require Import Place_Facts.

Definition fromSome{A:Type} (default:A) (o:option A) : A :=
  match o with
  | Some v => v
  | None => default
  end.


(*
Definition build_world_term (t:Term) (p:Plc) (e:EvidenceC):
  WorldTerm :=
  let term := fromSome (flatten_term t (flatten_places t)) in
  build_world_term_anno (annotated t p) p e.
*)

Inductive platStep : WorldTerm -> heap -> option Ev ->
                     WorldTerm -> heap -> Type :=
| platStepServer: forall i i' ev h h' p servs,
    bound_to servs p i ->
    Instr_step i h ev i' h' ->
    platStep servs
             h ev
             (map_replace servs p i')
             h'.

Inductive lstar_world: WorldTerm -> heap -> list Ev -> WorldTerm -> heap -> Prop :=
| lstar_refl: forall w h, lstar_world w h [] w h
| lstar_tran: forall e tr wt wt' wt'' h h' h'',
    platStep wt h (Some e) wt' h' ->
    lstar_world wt' h' tr wt'' h'' ->
    lstar_world wt h (e :: tr) wt'' h''
| lstar_silent_tran: forall wt wt' wt'' h h' h'' tr,
    platStep wt h None wt' h' ->
    lstar_world wt' h' tr wt'' h'' ->
    lstar_world wt h tr wt'' h''.
Hint Resolve lstar_refl : core.

Require Import LTS.

Check annotated.

Definition get_flattened_term (t:Term) : Term :=
  fromSome (asp CPY) (flatten_term t (flatten_places t)).

Require Import Coq.Program.Tactics.
Require Import Auto.


(* (* TODO:  I don't think this holds ... *)
Lemma unique_reqs: forall t p p',
  term_places_r t p ->
  term_places_r t p' ->
  p <> p'.
Proof.
Admitted.
 *)

Definition reqs_mono_starting_at (t:Term) (n:nat) : Prop.
Admitted.

Definition reqs_mono_starting_at_anno (t:AnnoTerm) (n:nat) : Prop.
Admitted.

Lemma mono_if_flattened: forall t,
    reqs_mono_starting_at (get_flattened_term t) 1.
Proof.
Admitted.

Lemma reqs_mono_anno: forall t,
    reqs_mono_starting_at t 1 ->
    reqs_mono_starting_at_anno (annotated t 0) 0.
Proof.
Admitted.


(*
(build_world_term_anno (annotated (get_flattened_term t') p) p e)
*)
Lemma world_refines_lts_event_ordering:
  forall t p e h' tr servs',
    reqs_mono_starting_at_anno t 0 ->
    lstar_world (build_world_term_anno t p e)  Empty tr servs'  h' ->
    servers_done servs' ->
    LTS.lstar (conf t p mt) tr (stop p (aeval t p mt)).
Proof.
  intros.

  (*
  assert (exists x, flatten_term t' (flatten_places t') = Some x).
  eapply flatten_some; eauto.
  destruct_conjs.
  unfold get_flattened_term in *.
  unfold fromSome in *.
  rewrite H2 in *.
  assert (well_formed_r (annotated H1 p)). admit.
*)

  generalizeEverythingElse t.
  induction t; intros.
  -
    df.
    unfold build_world_term_anno in *.
    unfold orchestrate_servers in *.
    unfold copland_compliment in *.
    unfold setup_main_code in *.
    df.
    unfold map_set in *.

    destruct a.
    +
      invc H0.
      ++
        unfold servers_done in *.

        pose (H1 0 (iconf (aprimInstr (fst r) (asp_instr CPY)) p e)).
        edestruct e0.
        econstructor.
        df.
        tauto.
        solve_by_inversion.
      ++
        admit.

      ++
        admit.
    +
      admit.
    +
      admit.
    +
      admit.
  -

Abort.




HERE

  
 





















Inductive is_waiting: Plc -> VM_ID -> InstrSt -> Prop :=
| immedWaitReq: forall i p q vmid,
    is_waiting q vmid (iWaitReq p (q,vmid) i).

(* | willDo: forall fromPair iSt,
    (* TODO: do we need to recurse on iSt here? *)
    will_respond fromPair (iDoRem iSt fromPair). *)
                           




Inductive ws_instr: AnnoInstr -> (Plc*VM_ID) -> MapC (Plc*VM_ID) InstrSt -> Prop :=
| wsi_prim: forall i p pr m,
    ws_instr (aprimInstr i p) pr m
| wsi_req: forall i j req_loc rpy_loc p q vmi m iSt,
    bound_to m (q,vmi) iSt ->
    is_waiting q vmi iSt ->
    p <> q -> (* TODO: is this necessary? *) 
    ws_instr (aReq i j req_loc rpy_loc p (q,vmi)) (p,vmi) m
| wsi_seq: forall a1 a2 pr m,
    ws_instr a1 pr m ->
    ws_instr a2 pr m ->
    ws_instr (aseq a1 a2) pr m.

(*
Inductive will_request_instr: (Plc*VM_ID) -> AnnoInstr -> Prop :=
| wreq: forall p q i j req_loc rpy_loc vmi,
    will_request_instr (q,vmi) (aReq i j req_loc rpy_loc p (q,vmi))
| wseql: forall pr a1 a2,
    will_request_instr pr a1 ->
    will_request_instr pr (aseq a1 a2)
| wseqr: forall pr a1 a2,
    will_request_instr pr a2 ->
    will_request_instr pr (aseq a1 a2).


Inductive will_request: (Plc*VM_ID) -> InstrSt -> Prop :=
| wrconf: forall i p e pr,
    will_request_instr pr i ->
    will_request pr (iconf i p e)
| will_request 
 *)

Inductive will_request_instr:  (Plc*VM_ID) -> AnnoInstr -> MapC (Plc*VM_ID) InstrSt -> Prop :=
| wriReq:
    forall q vmi i j x y p m,
      will_request_instr (q,vmi) (aReq i j x y p (q,vmi)) m
| wrseql: forall q q' a1 m a2 vmi,
    will_request_instr (q',vmi) a1 m ->
    q <> q' ->
    (forall iSt, bound_to m (q',vmi) iSt -> is_waiting q' vmi iSt) ->
    will_request_instr (q,vmi) (aseq a1 a2) m.


Inductive will_request: (Plc*VM_ID) -> InstrSt -> MapC (Plc*VM_ID) InstrSt -> Prop :=
| will_request (q,vmi) (


Inductive ws_world: MapC (Plc*VM_ID) InstrSt (*-> heap*) -> Prop :=
| wsw_stop: forall m,
    servers_done m ->
    ws_world  m
| wsw_conf: forall i m vmi e p,
    bound_to m (p,vmi) (iconf i p e) ->
    ws_instr i (p,vmi) m -> 
    ws_world m
| wsw_waitReq: forall p q vmi ai iSt m,
    bound_to m (q,vmi) (iWaitReq p (q,vmi) ai) ->
    bound_to m (p,vmi) iSt ->
    p <> q ->
    will_request (q,vmi) iSt m -> 
    ws_world m.



| wsw_rpyWait: forall m p q iSt j rpy_loc,
    bound_to m q iSt ->
    will_respond p iSt ->
    ws_world (irpyWait j rpy_loc p q) m
| wsw_ls: forall m m' iSt ai,
    ws_world iSt m ->
    advance_servers_ist iSt m m' ->
    ws_instr ai m' -> (* TODO:  pl (iSt)? *)
    servers_done m' ->
    ws_world (ils iSt ai) m.

Set Nested Proofs Allowed.


Lemma well_structured_world_init: forall t p e,
    well_formed t ->
    ws_world (iconf (instr_compiler t) p e) (copland_compliment t []).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      df;
      repeat econstructor.
  -
    df.
    subst.
    unfold map_set in *.
    df.
    apply wsw_conf.
    
    econstructor.
    econstructor.
    +
      unfold map_set in *.
      unfold map_get in *.

    rewrite Nat.eqb_refl in *.
    eauto.
    +
      
    econstructor.
  -
    do_wf_pieces.
    econstructor.

    assert (ws_world (iconf (instr_compiler t1) p e) (copland_compliment t1 [])) by eauto.

    assert (ws_world (iconf (instr_compiler t2) p e) (copland_compliment t2 [])) by eauto.

    eapply compliment_alseq_skip'.

    repeat find_inversion.

    invc H2.
    invc H3.
    df.
    eapply compliment_focus; eauto.

    df.
    eapply advance_assoc; eauto.
    solve_by_inversion.
Defined.
*)









Lemma platStep_ws: forall wt h ev wt' h',
  well_structured_world wt ->
  platStep wt h ev wt' h' ->
  well_structured_world wt'.
Proof.
  intros.
  destruct wt.
  destruct wt'.

  invc X.
  admit.
  admit.
  admit.

  generalizeEverythingElse i.
  induction i; intros.
  -
    invc H.
    invc X; try solve_by_inversion.
    econstructor.
    econstructor.
    econstructor.
  -
    invc H.
    invc X.
    +
      invc H7.
      ++
        econstructor.
      ++
        invc H4.
        econstructor.
        eassumption.
        eassumption.
      ++
        invc H4.
        
        econstructor.
        +++
          econstructor.
          eassumption.
        +++
          eapply advance_ist_iff; eauto.
        +++
          eassumption.
        +++
          eassumption.
    +
      econstructor.
      admit.
    +
      econstructor.
      admit.
    +
      econstructor.
      
      
          
          
    
        
        
          
          
          
        
        invc H4.
        apply H7.
    




  
  generalizeEverythingElse H.
  induction H; intros.
  -
    invc X; try solve_by_inversion.
    econstructor.
    econstructor.
    econstructor.
    
  -
    invc X; try solve_by_inversion.
    +
      invc H7; try solve_by_inversion.
      ++
        econstructor.
      ++
        invc H.
        econstructor.
        eassumption.
        eassumption.
      ++
        invc H.
        econstructor.
        econstructor.
        eassumption.



        eapply advance_ist_iff; eauto.

        eassumption.
        eassumption.
        
        
    +
      invc H7.
      econstructor.
      admit.
    +
      econstructor.
      admit.
    +
      econstructor.
      
      
    
    
    inversion H.
    inversion X; try solve_by_inversion.
    econstructor.
    rewrite H10.
    subst.
    invc X

  


(*
| platStepOneDone: forall i h h' ev p e,
    Instr_step i h ev (istop p e) h' ->
    platStep_l (onePlat i) h ev (donePlat p e) h'
| platStepPar_l: forall wt1 wt1' wt2 h h' ev,
    platStep_l wt1 h ev wt1' h' ->
    platStep_l (parPlats wt1 wt2) h ev (parPlats wt1' wt2) h'
| platStepPar_r: forall wt1 wt2 wt2' h h' ev,
    platStep_l wt2 h ev wt2' h' ->
    platStep_l (parPlats wt1 wt2) h ev (parPlats wt1 wt2') h'
| platStepDone: forall p q h e e',
    platStep_l (parPlats (donePlat p e) (donePlat q e')) h None (donePlat p e) h.
*)

(*
Inductive platStep : InstrSt -> configs -> heap -> option Ev ->
                     InstrSt -> configs -> heap -> Type :=
| mainStep: forall i i' ev w h h',
    Instr_step i h ev i' h' ->
    platStep i w h ev i' w h'
| worldStep: forall p w wi wi' ev i h h',
    bound_to w p wi ->
    Instr_step wi h ev wi' h' ->
    platStep i w h ev i (map_set w p wi') h'.
*)

(*
Definition world_config := (InstrSt*configs*heap)%type.
 *)



(*

Inductive lstar_world: world_config -> list Ev -> world_config -> Prop :=
| lstar_refl: forall w, lstar_world w [] w
| lstar_tran: forall e tr i i' c c' h h' st2,
    platStep i c h (Some e) i' c' h' ->
    lstar_world (i',c',h') tr st2 ->
    lstar_world (i,c,h) (e :: tr) st2
| lstar_silent_tran: forall tr i i' c c' h h' st2,
    platStep i c h None i' c' h' -> lstar_world (i',c',h') tr st2 ->
    lstar_world (i,c,h) tr st2.
Hint Resolve lstar_refl : core.
 *)

Require Import LTS Auto.

Definition asp1 := asp (ASPC 1 []).
Definition asp2 := asp (ASPC 2 []).

Definition ex1_term :=
  lseq (att 1 asp1) asp2. (*(att 1 asp2)*)
  (*att 1 asp1 *) 

Definition ex1_term_annotated :=
  snd (anno' ex1_term 0 [42;43] 2 ).

(*
Definition ex1_heap := [(42,Empty);(43,Empty)].
Check ex1_heap.
*)

Compute ex1_term_annotated.

Compute (orchestrate_l_servers ex1_term_annotated).
Compute (build_world_term ex1_term_annotated 2 mtc).

Compute (copland_compliment_l (snd (anno' (att 1 asp1) 0 [42;43] 2)) []).

Compute (copland_compliment_l ex1_term_annotated []).

Compute (build_world_term ex1_term_annotated 2 mtc).

(*
Ltac inv_lstar :=
  match goal with
  (*|[H: locContains (?C) _ _  |- _ ] => invc H
  | [H: locEmpty (?C) (*(put_heap _ _ _)*) _  |- _ ] => invc H *)
  | [H: Instr_step (?C _) _ _ _ _  |- _ ] => invc H
                                                (*
  | [H: platStep
          (onePlat (?C _)) _ _ _ _ |- _ ] => invc H
  | [H: platStep
          (parPlats (?C _) _) _ _ _ _ |- _ ] => invc H
  | [H: lstar_world
          (parPlats (?C _) _) _ _ _ _ |- _] => invc H
*)
  end;
  df;
  try solve_by_inversion.
*)


Set Nested Proofs Allowed.

  Ltac do_eqb_reflect :=
    let H_eq := fresh in
    match goal with
    | [H: eqb ?p ?n = true |- _] =>
      assert_new_proof_as_by
        (p = n)
        ltac:(eapply eqb_leibniz; apply H)
               H_eq;
      clear H
    end;
    rewrite H_eq in *;
    clear H_eq.

  Ltac bound_facts :=
    match goal with
    | [H: bound_to [] _ _ |- _] =>
      invc H; unfold map_get in *; solve_by_inversion
    | [H: bound_to _ _ _ |- _] =>
      invc H
    end;
    unfold map_get in *;
    break_if; try solve_by_inversion;
    do_eqb_reflect;
    unfold map_replace in *;
    unfold map_remove in *;
    subst;
    df;
    unfold map_set in *;
    repeat rewrite Nat.eqb_refl in *;
    df.


  
  (*
  Ltac bound_facts :=
    match goal with
    | [H: bound_to _ _ _ |- _] =>
      invc H
    end;
    unfold map_get in *;
    break_if; try solve_by_inversion;
    do_eqb_reflect;
    unfold map_replace in *;
    unfold map_remove in *;
    subst;
    df;
    unfold map_set in *;
    df.
*)

  Ltac inv_lstar :=
  match goal with
  (*|[H: locContains (?C) _ _  |- _ ] => invc H
  | [H: locEmpty (?C) (*(put_heap _ _ _)*) _  |- _ ] => invc H *)
  | [H: Instr_step (?C _) _ _ _ _  |- _ ] => invc H

  | [H:
       platStep
        (worldTermC (?C _) (*(iconf _ _ _)*) _)
        _ _ _ _ |- _] => invc H
  (*
  | [H: platStep
          (parPlats (?C _) _) _ _ _ _ |- _ ] => invc H
*)
  | [H: lstar_world
          (worldTermC (?C _) _) _ _ _ _ |- _] => invc H
  end;
  (*try unfold wrap_server_config in *; *)
  df;
  try solve_by_inversion.

Ltac unfold_world_defs :=
  unfold build_world_term in *;
  unfold orchestrate_l_servers in *;
  unfold setup_main_code in *;
  df;
  unfold wrap_server_config in *;
  df.

Definition ex1_heap : heap := Empty. (* option (Plc*EvidenceC) := None. *)

Definition ex1_world : WorldTerm := (build_world_term ex1_term_annotated 2 mtc).

(*
Lemma world_refines_lts_event_ordering_ex1:
  forall (*t p e*) e' (*h*) h' tr servs' (*et*) (*(wt:WorldTerm)*) ,
    (*well_formed t -> *)
    (* let wt := build_world_term t p e in (*(InstrSt*configs)*) *)
    
    lstar_world ex1_world ex1_heap tr (worldTermC (istop 2 e') servs')  h' ->
    LTS.lstar (conf ex1_term_annotated 2 mt) tr (stop 2 (aeval ex1_term_annotated 2 mt)).
Proof.
  intros.
  unfold ex1_world in *.
  unfold ex1_term_annotated in *.
  unfold_world_defs.

  (*
  unfold build_world_term in *.
  unfold orchestrate_l_servers in *.
  unfold setup_main_code in *.
  (*
  unfold build_world_term' in *.
  unfold build_world_term'' in *. *)
  unfold ex1_term_annotated in *.
  df.
  unfold wrap_server_config in *.
  df.
  (*
  unfold combineInstrSt in *. *)
  unfold ex1_heap in *.

  (*
  unfold wrap_server_config in *. *)
  (*unfold build_one' in *. *)

  df.
*)

  repeat (inv_lstar; try bound_facts).


  -
  eapply lstar_silent_tran.
  econstructor.

  eapply lstar_tran.
  econstructor.

  econstructor.

  eapply lstar_tran.
  econstructor.
  eapply stattstep.
  econstructor.

  eapply lstar_tran.
  econstructor.
  eapply stattstop.

  eapply lstar_silent_tran.
  eapply stlseqstop.

  eapply lstar_tran.
  econstructor.
  econstructor.
  -
      eapply lstar_silent_tran.
  econstructor.

  eapply lstar_tran.
  econstructor.

  econstructor.

  eapply lstar_tran.
  econstructor.
  eapply stattstep.
  econstructor.

  eapply lstar_tran.
  econstructor.
  eapply stattstop.

  eapply lstar_silent_tran.
  eapply stlseqstop.

  eapply lstar_tran.
  econstructor.
  econstructor.
  -
      eapply lstar_silent_tran.
  econstructor.

  eapply lstar_tran.
  econstructor.

  econstructor.

  eapply lstar_tran.
  econstructor.
  eapply stattstep.
  econstructor.

  eapply lstar_tran.
  econstructor.
  eapply stattstop.

  eapply lstar_silent_tran.
  eapply stlseqstop.

  eapply lstar_tran.
  econstructor.
  econstructor.
  -
      eapply lstar_silent_tran.
  econstructor.

  eapply lstar_tran.
  econstructor.

  econstructor.

  eapply lstar_tran.
  econstructor.
  eapply stattstep.
  econstructor.

  eapply lstar_tran.
  econstructor.
  eapply stattstop.

  eapply lstar_silent_tran.
  eapply stlseqstop.

  eapply lstar_tran.
  econstructor.
  econstructor.
  -
      eapply lstar_silent_tran.
  econstructor.

  eapply lstar_tran.
  econstructor.

  econstructor.

  eapply lstar_tran.
  econstructor.
  eapply stattstep.
  econstructor.

  eapply lstar_tran.
  econstructor.
  eapply stattstop.

  eapply lstar_silent_tran.
  eapply stlseqstop.

  eapply lstar_tran.
  econstructor.
  econstructor.
  -
      eapply lstar_silent_tran.
  econstructor.

  eapply lstar_tran.
  econstructor.

  econstructor.

  eapply lstar_tran.
  econstructor.
  eapply stattstep.
  econstructor.

  eapply lstar_tran.
  econstructor.
  eapply stattstop.

  eapply lstar_silent_tran.
  eapply stlseqstop.

  eapply lstar_tran.
  econstructor.
  econstructor.
  Defined.
    
    
    
    
    


  (*
  econstructor.
  apply 

  apply stattstep.
  econstructor.
  eapply lstar_tran.
  econstructor.

  eapply stattstep.

  
  apply stattstop.

  eapply lstar_tran

  
  econstructor.
  econstructor.
  apply stattstop.

  simpl.

  econstructor
  
  
  eapply statt.
  eapply lstar_tran.
  eapply stattstep.
  econstructor.
  eapply lstar_tran.
  apply stattstop.
  apply lstar_refl.
  

  eapply lstar_tran.
  eapply statt.
  eapply lstar_tran.
  eapply stattstep.
  econstructor.
  eapply lstar_tran.
  apply stattstop.
  apply lstar_refl.

  eapply lstar_tran.
  eapply statt.
  eapply lstar_tran.
  eapply stattstep.
  econstructor.
  eapply lstar_tran.
  apply stattstop.
  apply lstar_refl.

  eapply lstar_tran.
  eapply statt.
  eapply lstar_tran.
  eapply stattstep.
  econstructor.
  eapply lstar_tran.
  apply stattstop.
  apply lstar_refl.
*)

 *)

(*
    Ltac bound_facts' :=
    match goal with
    | [H: bound_to [] _ _ |- _] =>
      invc H; unfold map_get in *; solve_by_inversion
    | [H: bound_to _ _ _ |- _] =>
      invc H
    end;
    unfold map_get in *;
    break_if; try solve_by_inversion;
    do_eqb_reflect;
    unfold map_replace in *;
    unfold map_remove in *;
    subst;
    df;
    unfold map_set in *;
    df.
 *)


Lemma combine_lem{A B:Type} `{H : EqClass A} : forall (prs:(list (A*B))),
    combine (map_dom prs) (map_vals prs) = prs.
Proof.
  intros.
  induction prs.
  -
    tauto.
  -
    simpl.
    repeat break_let.
    subst.
    simpl.
    rewrite IHprs.
    tauto.
Defined.

Lemma lstar_world_lseq_decomp: forall t1 t2 p e e'' h' servs' tr l r,

    (*
    lstar_world
      (worldTermC (iconf (aseq (instr_compiler t1) (instr_compiler t2)) p e)
                  (combine (map_dom (copland_compliment_l t2 (copland_compliment_l t1 [])))
                           (map wrap_server_config (copland_compliment_l t2 (copland_compliment_l t1 []))))) Empty tr
      (worldTermC (istop p e'') servs') h' -> 
     *)

    well_formed (alseq r l t1 t2) ->


    lstar_world
         (worldTermC (iconf (instr_compiler (alseq r l t1 t2)) p e)
            (combine (map_dom (copland_compliment_l (alseq r l t1 t2) []))
               (map wrap_server_config (copland_compliment_l (alseq r l t1 t2) [])))) Empty tr
         (worldTermC (istop p e'') servs') h' ->

    exists (tr1: list Ev) e_mid servs_mid (*(h_mid:heap)*),
      lstar_world
        (worldTermC (iconf (instr_compiler t1) p e)
                    (combine (map_dom (copland_compliment_l t1 [])) (map wrap_server_config (copland_compliment_l t1 [])))) Empty tr1
        (worldTermC (istop p e_mid) servs_mid) Empty /\
      servers_done servs_mid /\
      exists (tr2: list Ev),
        lstar_world
          (worldTermC (iconf (instr_compiler t2) p e_mid)
                      (combine (map_dom (copland_compliment_l t2 [])) (map wrap_server_config (copland_compliment_l t2 [])))) Empty (*h_mid*) tr2
          (worldTermC (istop p e'') servs') h' /\
        servers_done servs' /\
        tr = tr1 ++ tr2.
Proof.
  intros.
  df.
  do_wf_pieces.
  df.
  repeat eexists.
  
  inv_lstar.
  admit.

Abort.

Lemma evshape_trace_irrel : forall t p et et' et2 et2' tr,
    lstar (conf t p et)  tr (stop p et') ->
    lstar (conf t p et2) tr (stop p et2').
Proof.
Admitted.

Require Import Coq.Program.Tactics.

Check bound_to.



(*
Lemma at_world_decomp :
  forall t n0 e tr0 n4 n2 st1 servs_res e_res h' h'0 n,

    lstar_world
      (worldTermC
         (irpyWait (Init.Nat.pred n2) n4 n0 n0)
         [(n0, ils st1 (aResp (Nat.pred n2) n))])
      h'0
      tr0
      (worldTermC (istop n0 e_res) servs_res) h' -> 
    Instr_step (iconf (instr_compiler t) n0 e) Empty None st1 h'0 -> 
    

    
    exists tr e' servs' h',
      lstar_world
        (worldTermC (iconf (instr_compiler t) n0 e)
                    (combine (map_dom (copland_compliment_l t [])) (map wrap_server_config (copland_compliment_l t [])))) Empty tr
        (worldTermC (istop n0 e') servs') h' /\
      servers_done servs' /\
      (tr0 = tr ++ [(rpy (Init.Nat.pred n2) n4 n0 n0)]).
Proof.
Admitted.
 *)

Lemma at_world_decomp' : forall t n1 n2 n3 n4 n0 p0 e n tr e' servs' h',
    lstar_world
      (worldTermC
         (iconf (aReq n1 (Init.Nat.pred n2) n3 n4 n0) p0 e)
         [(n0,
           (iconf
              (aseq
                 (aseq (aWaitReq n1) (instr_compiler t))
                 (aResp (Nat.pred n2) n)) n0 mtc))])
      Empty
      tr
      (worldTermC (istop p0 e') servs') h' ->
    lstar_world
      (worldTermC
         (iconf (aReq n1 (Init.Nat.pred n2) n3 n4 n0) p0 e)
         [(n0,
           (iconf
              (aseq
                 (aseq (aWaitReq n1) (instr_compiler t))
                 (aResp (Nat.pred n2) n)) n0 mtc))])
      Empty
      [(req n1 n3 p0 n0)]
      (worldTermC
         (irpyWait (Init.Nat.pred n2) n4 n0 p0)
         [(n0,
           ils (iconf (instr_compiler t) n0 e)
               (aResp (Nat.pred n2) n))])
      Empty /\
    exists s_ev t_tr,
      lstar_world
        (worldTermC
           (irpyWait (Init.Nat.pred n2) n4 n0 p0)
           [(n0,
             ils (iconf (instr_compiler t) n0 e)
                 (aResp (Nat.pred n2) n))])
        Empty
        t_tr
        (worldTermC
           (irpyWait (Init.Nat.pred n2) n4 n0 p0)
           [(n0, (istop n0 s_ev))])
        (Full (p0,s_ev)) /\
      tr = [(req n1 n3 p0 n0)] ++ t_tr ++ [(rpy (Init.Nat.pred n2) n4 p0 n0)]. 
Proof.
Admitted.

Lemma remote_same: forall n2 n4 n0 p0 e n H4 H3 t,
    lstar_world
      (worldTermC
         (irpyWait (Init.Nat.pred n2) n4 n0 p0)
         [(n0, ils (iconf (instr_compiler t) n0 e) (aResp (Nat.pred n2) n))])
      Empty
      H4
      (worldTermC
         (irpyWait (Init.Nat.pred n2) n4 n0 p0)
         [(n0, istop n0 H3)])
      (Full (p0, H3)) ->
    exists servs'' h'',
      lstar_world
        (worldTermC
           (iconf (instr_compiler t) n0 e)
           (combine (map_dom (copland_compliment_l t [])) (map wrap_server_config (copland_compliment_l t []))))
        Empty
        H4
        (worldTermC (istop n0 H3) servs'') h'' /\
      servers_done servs''.
Proof.
Admitted.


Lemma world_refines_lts_event_ordering:
  forall t p e e' (*h*) h' tr servs' (*et*) (*(wt:WorldTerm)*) ,
    well_formed t ->
    (*let wt := build_world_term t p e in (*(InstrSt*configs)*) *)
    
    lstar_world (build_world_term t p e) Empty tr (worldTermC (istop p e') servs')  h' ->
    servers_done servs' ->
    LTS.lstar (conf t p mt) tr (stop p (aeval t p mt)).
Proof.
  intros.
  unfold_world_defs.

  unfold mapify_server_configs in *.
  unfold init_configs in *.
  df.
  assert (
      (combine (map_dom (copland_compliment_l t [])) (map_vals (copland_compliment_l t []))) =
      (copland_compliment_l t [])).
  {
    eapply combine_lem; eauto.
  }
  repeat rewrite H2 in *; clear H2.
  (*
  unfold wrap_server_config in *.
  unfold map_vals in *.
  unfold copland_compliment_l in *. 
   *)

  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a; df;
      repeat (inv_lstar; try bound_facts; try (econstructor; econstructor; tauto)).
  -
    df.
    (*
    unfold wrap_server_config in *. *)
    df.

    (*
    assert (
        exists ev_res, 
    lstar_world
      (worldTermC
         (iconf (aReq n1 (Init.Nat.pred n2) n3 n4 n0) p0 e)
         [(n0, iconf
                 (aseq
                    (aseq (aWaitReq n1) (instr_compiler t))
                    (aResp (Nat.pred n2) n))
                 n0
                 mtc)])
      Empty
      tr
      (worldTermC
         (istop p0 ev_res)
         [n0,
          ils (ils (iconf (instr_compiler t) n0 e)

      



      
      (worldTermC (istop p0 e') servs') h')
*)





           (*
    lstar_world
      (worldTermC
         (iconf (aReq n1 (Init.Nat.pred n2) n3 n4 n0) p0 e)
         [(n0, iconf
                 (aseq
                    (aseq (aWaitReq n1) (instr_compiler t))
                    (aResp (Nat.pred n2) n))
                 n0
                 mtc)])
      Empty
      tr
      (worldTermC (istop p0 e') servs') h') *)


    subst.
    unfold wrap_server_config in H0.
    df.




    edestruct at_world_decomp'.
    eassumption.
    destruct_conjs.
    subst.



    edestruct remote_same.
    eassumption.
    destruct_conjs.

    eapply lstar_transitive.

    eapply lstar_tran.
    apply statt.
    econstructor.

    eapply lstar_transitive.

    eapply lstar_strem.

    eapply IHt.
    invc H.
    eauto.



    
    

    eassumption.
    eassumption.

    eapply lstar_tran.
    apply stattstop.
    econstructor.

    (*

        H5 : lstar_world (worldTermC (irpyWait (Init.Nat.pred n2) n4 n0 p0) [(n0, ils (iconf (instr_compiler t) n0 e) (aResp (Nat.pred n2) n))]) Empty H4
         (worldTermC (irpyWait (Init.Nat.pred n2) n4 n0 p0) [(n0, istop n0 H3)]) (Full (p0, H3))
  ============================
  lstar_world
    (worldTermC (iconf (instr_compiler t) n0 ?e) (combine (map_dom (copland_compliment_l t [])) (map wrap_server_config (copland_compliment_l t []))))
    Empty H4 (worldTermC (istop n0 ?e') ?servs') ?h'
     *)
    


    (*

    
    eassumption.

    

    
    eassumption.
    

    exfalso.
    eapply at_world_decomp'; eauto.

      
   
      
      
















    

    






    
    inv_lstar.
    inv_lstar.
    inv_lstar.

    unfold wrap_server_config in H2.
    df.

    
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar.

    Ltac servers_done_contra :=
      unfold servers_done in *;
      (*unfold wrap_server_config in *; *)
      df;
      let HH := fresh in
      match goal with
      | [(*H: servers_done [(?C _)], *)
            H: context[
                    bound_to [(?n0, ?s)] _ _ -> _] |- _] =>
        pose (H n0 s) as HH;
        forward HH
      end;
      econstructor;
        df;
        try rewrite Nat.eqb_refl;
        try tauto;
        try (concludes; destruct_conjs; bound_facts).

    servers_done_contra.
    
(*
    concludes.
    destruct_conjs.
    bound_facts.



    forward e.
        


    
    unfold servers_done in *.
    unfold wrap_server_config in *.
    df.
    specialize H1 with (p:=n0) (s:=(iconf (aseq (aseq (aWaitReq n1) (instr_compiler t)) (aResp (Nat.pred n2) n)) n0 mtc)).
    destruct_conjs.

    forward H1.
    econstructor.
    df.
    Search (_ =? _).
    rewrite Nat.eqb_refl.
    tauto.
    concludes.
    destruct_conjs.
    bound_facts.
 *)
    

    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    servers_done_contra.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    servers_done_contra.
    inv_lstar.
    bound_facts.
    inv_lstar.

    fold wrap_server_config in IHt.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.  
    bound_facts.
    inv_lstar.

    inv_lstar.
    bound_facts.
    inv_lstar.

    (*
    Require Import Coq.Arith.PeanoNat. *)

    destruct (Nat.eq_dec p0 n0).
    +
      subst.
      (*
      repeat (inv_lstar; try bound_facts; try servers_done_contra; try bound_facts; try servers_done_contra).
       *)
      
      inv_lstar.
      
      (* Main thread grabbed evidence *)
      inv_lstar.
      inv_lstar.
      inv_lstar.
      servers_done_contra.
      inv_lstar.
      bound_facts.
      inv_lstar.
      inv_lstar.
      bound_facts.
      inv_lstar.
      inv_lstar.
      inv_lstar.
      servers_done_contra.
      inv_lstar.
      bound_facts.
      inv_lstar.
      inv_lstar.
      inv_lstar.
      bound_facts.
      inv_lstar.
      inv_lstar.

      (* Servers grabbed evidence *)
      bound_facts.
      inv_lstar.

      
      inv_lstar.
      (* Servers grabbed the evidence *)
      bound_facts.
      inv_lstar.
      inv_lstar.

      (* aseq is peeled off on the server *)
      inv_lstar.
      inv_lstar.
      
      (* Main thread grabbed evidence again *)
      inv_lstar.
      inv_lstar.
      servers_done_contra.
      inv_lstar.
      bound_facts.
      inv_lstar.
      inv_lstar.

      (* Server grabbed evidence in correct sequence *)
      inv_lstar.
      bound_facts.
      inv_lstar.
      inv_lstar.
      bound_facts.
      inv_lstar.
      inv_lstar.
      inv_lstar.
      bound_facts.
      inv_lstar.
      inv_lstar.
      inv_lstar.

      (* Server done processing request *)
      inv_lstar.
      admit.  (* Cannot be a Some event *)

      (* Now execution must proceed on server *)
      inv_lstar.
      bound_facts.
      inv_lstar.
      inv_lstar.

      (* Must now start processing t on Server 
         ils (iconf (instr_compiler t) n0 e) (aResp ...) n *)
      inv_lstar.
      admit.  (* Cannot be Some e *)
    
      inv_lstar.
      (* Entered ils on server for evaulating subterm *)
      bound_facts.
      inv_lstar.

      assert (well_formed t).
      {
        admit.
      }



      edestruct at_world_decomp.
      eassumption.
      eassumption.
      destruct_conjs.

      assert (lstar (conf t n0 mt) x (stop n0 (aeval t n0 mt))).
      {
        eapply IHt.
        eassumption.
        eassumption.
        eassumption.
      }

      subst.

      admit. 
    +
      admit.
      
    +

      
      bound_facts.
      inv_lstar.
    +
      inv_lstar.
      bound_facts.
      inv_lstar.

      inv_lstar.
      Focus 2.

      inv_lstar.
      bound_facts.
      inv_lstar.
      inv_lstar.

      
      inv_lstar.
      inv_lstar.
      
      
      

      

      

      edestruct IHt.
      eassumption.
      admit.
      admit.
      

      invc H0.
      admit.

      invc X.
      inv_lstar.

      invc H4.
      unfold map_get in *.

      break_if; try solve_by_inversion.
      find_inversion.

      unfold map_replace in *.
      unfold map_remove in *.
      rewrite Heqb in *.
      unfold map_set in *.

      assert (p4 = n0). admit.
      subst. clear Heqb.

      assert (

      invc H10.
     
      
      admit.
    +
      
      



    
    inv_lstar.
    inv_lstar.
    inv_lstar.
    admit.
    bound_facts.
    inv_lstar.

    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    admit.

    bound_facts.
    unfold wrap_server_config in *.
    df.
    inv_lstar.

    unfold wrap_server_config in *.
    df.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    servers_done_contra.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    servers_done_contra.

    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar
    



    
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    servers_done_contra.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    servers_done_contra.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    servers_done_contra.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    inv_lstar.
    bound_facts.
    inv_lstar.
    invc H0.
    invc X.
    invc H9.
    invc H2.
    servers_done_contra.
    invc X.
    invc H9.
    invc H0.
    df.
    bound_facts.
    servers_done_contra.
    df.
    bound_facts.
    inv_lstar.
    df.
    invc X.
    inv_lstar.
    df.
    bound_facts.
    invc H2.
    servers_done_contra.
    invc X.
    solve_by_inversion.
    df.
    bound_facts.
    invc H0.
    unfold servers_done in *.
    pose (H1 n0 i'0).
    forward e2.
    econstructor.
    df.
    try rewrite Nat.eqb_refl in *.
    tauto.
    concludes.
    destruct_conjs.
    subst. 
    inv_lstar.
    





    

    admit.

    admit.

    admit.

    admit.

    admit.

    admit.

    admit.


    
    HEREEEEEE
    admit.
*)
  -
    do_wf_pieces.

    (*
    assert (
        exists (tr1: list Ev) e' servs_mid (h_mid:heap),
          lstar_world
           (worldTermC (iconf (instr_compiler t1) p e)
              (combine (map_dom (copland_compliment_l t1 [])) (map wrap_server_config (copland_compliment_l t1 [])))) Empty tr1
           (worldTermC (istop p e') servs_mid) h_mid /\
          exists (tr2: list Ev) e'',
            lstar_world
           (worldTermC (iconf (instr_compiler t2) p e')
              (combine (map_dom (copland_compliment_l t2 [])) (map wrap_server_config (copland_compliment_l t2 [])))) Empty (*h_mid*) tr2
           (worldTermC (istop p e'') servs') h' /\
            tr = tr1 ++ tr2).
    {
     *)
    
      


    edestruct lstar_world_lseq_decomp.
    eassumption.
    eassumption.
      
    destruct_conjs.

    subst.

    

    pose (IHt1 p e H4 Empty x H5 H2 H6).

    pose (IHt2 p H4 e' h' H8 servs' H3 H9).
    repeat concludes.

    eapply lstar_silent_tran.
    econstructor.

    eapply lstar_transitive.
    Check lstar_stls.
    eapply lstar_stls.
    eassumption.

    eapply lstar_silent_tran.
    apply stlseqstop.

    eapply evshape_trace_irrel; eauto.
    Defined.

    
    
    
    
    


  


















(*
Lemma world_refines_lts_event_ordering:
  forall t p e e' h h' tr et (wt:WorldTerm),
    well_formed t ->
   (* let wt := build_world_term t p e in (*(InstrSt*configs)*) *)
    lstar_world (build_world_term t p e) h tr (donePlat p e') h' ->
    LTS.lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.

  
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a.
    +
      df.
      destruct r.
      df.
      invc H0.
      ++
        df.
        invc H1.
  
Abort.
*)




HERE

Inductive PlatSt: Set :=
| stop: Plc -> Evidence -> St
| conf: AnnoTerm -> Plc -> Evidence -> St
| rem: nat -> Loc -> Plc -> St -> St
| ls: St -> AnnoTerm -> St
(*| bsl: nat -> St -> AnnoTerm -> Plc -> Evidence -> St
| bsr: nat -> Evidence -> St -> St
| bp: nat -> Loc -> Loc -> St -> St -> St*) .





Record PlatformState : Type := mk_plat
                         {plat_pl:Plc ;
                          plat_trace:list Ev ;
                          plat_store:heap}.

Definition start (st:PlatformState) (places:(CVM unit) * setup) : PlatformState.
Admitted.

Definition run_it (me:Plc) (t:AnnoTerm) : PlatformState :=
  start (mk_plat me [] []) (orchestrate t).

Definition getLocs (t:Term) (m:MapC (Plc*Plc) (list Loc)): list Loc.
Admitted.

Definition fromSome{A:Type} (default:A) (opt:option A): A :=
  match opt with
  | Some x => x
  | _ => default
  end.

Definition run_it_term (me:Plc) (t:Term) (m:MapC (Plc*Plc) (list Loc)) : PlatformState :=
  let annt := snd (anno' t 0 (getLocs t m)) in
  run_it me annt.











(** * Transitive Closures *)

Inductive lstar: InstrSt -> list Ev -> InstrSt -> Prop :=
| lstar_refl: forall st, lstar st [] st
| lstar_tran: forall st0 e st1 tr st2,
    Instr_step st0 (Some e) st1 -> lstar st1 tr st2 -> lstar st0 (e :: tr) st2
| lstar_silent_tran: forall st0 st1 tr st2,
    Instr_step st0 None st1 -> lstar st1 tr st2 -> lstar st0 tr st2.
Hint Resolve lstar_refl : core.

Lemma lstar_transitive:
  forall st0 tr0 st1 tr1 st2,
    lstar st0 tr0 st1 ->
    lstar st1 tr1 st2 ->
    lstar st0 (tr0 ++ tr1) st2.
Proof.
  intros.
  induction H.
  - rewrite app_nil_l; auto.
  - apply IHlstar in H0.
    rewrite <- app_comm_cons.
    eapply lstar_tran; eauto.
  - apply IHlstar in H0.
    eapply lstar_silent_tran; eauto.
Qed.

(** Transitive closure without labels. *)

Inductive star: InstrSt -> InstrSt -> Prop :=
| star_refl: forall st, star st st
| star_tran: forall st0 e st1 st2,
    Instr_step st0 e st1 -> star st1 st2 -> star st0 st2.
Hint Resolve star_refl : core.

Lemma star_transitive:
  forall st0 st1 st2,
    star st0 st1 ->
    star st1 st2 ->
    star st0 st2.
Proof.
  intros.
  induction H; auto.
  apply IHstar in H0.
  eapply star_tran; eauto.
Qed.

Lemma lstar_star:
  forall st0 tr st1,
    lstar st0 tr st1 -> star st0 st1.
Proof.
  intros.
  induction H; auto;
    eapply star_tran; eauto.
Qed.

Lemma star_lstar:
  forall st0 st1,
    star st0 st1 -> exists tr, lstar st0 tr st1.
Proof.
  intros.
  induction H; auto.
  - exists []; auto.
  - destruct IHstar as [tr G].
    destruct e.
    + exists (e :: tr).
      eapply lstar_tran; eauto.
    + exists tr.
      eapply lstar_silent_tran; eauto.
Qed.

(*
Lemma star_seval:
  forall st0 st1,
    star st0 st1 -> seval st0 = seval st1.
Proof.
  intros.
  induction H; auto.
  apply step_seval in H; auto.
  rewrite H; auto.
Qed.

Lemma steps_preserves_eval:
  forall t p p' e0 e1,
    star (conf t p e0) (stop p' e1) ->
    aeval t p e0 = e1.
Proof.
  intros.
  apply star_seval in H.
  simpl in H; auto.
Qed.
*)

(** * Correct Path Exists *)

(*
Lemma star_strem:
  forall st0 st1 j p loc,
    star st0 st1 -> star (rem j loc p st0) (rem j loc p st1).
Proof.
  intros.
  induction H; auto.
  eapply star_tran; eauto.
Qed.
*)

Lemma star_stls:
  forall st0 st1 t,
    star st0 st1 -> star (ils st0 t) (ils st1 t).
Proof.
  intros.
  induction H; auto.
  eapply star_tran; eauto.
Qed.

(*
Lemma star_stbsl:
  forall st0 st1 j t p e,
    star st0 st1 ->
    star (bsl j st0 t p e) (bsl j st1 t p e).
Proof.
  intros.
  induction H; auto.
  eapply star_tran; eauto.
Qed.

Lemma star_stbsr:
  forall st0 st1 j e,
    star st0 st1 ->
    star (bsr j e st0) (bsr j e st1).
Proof.
  intros.
  induction H; auto.
  eapply star_tran; eauto.
Qed.
*)

(* Congruence lemmas for Copland LTS semantics *)
Lemma lstar_stls :
  forall st0 st1 t tr,
    lstar st0 tr st1 -> lstar (ils st0 t) tr (ils st1 t).
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Qed.

(*
Lemma lstar_strem : forall st st' tr p r loc,
    lstar st tr
          st' ->
    lstar (rem r loc p st) tr (rem r loc p st').
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Defined.
*)

(*
Lemma lstar_stbsl:
  forall st0 st1 j t p e tr,
    lstar st0 tr st1 ->
    lstar (bsl j st0 t p e) tr (bsl j st1 t p e).
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Defined.

Lemma lstar_stbsr:
  forall st0 st1 j e tr,
    lstar st0 tr st1 ->
    lstar (bsr j e st0) tr (bsr j e st1).
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Defined.

Lemma star_stbp:
  forall st0 st1 st2 st3 j xi yi,
    star st0 st1 ->
    star st2 st3 ->
    star (bp j xi yi st0 st2) (bp j xi yi st1 st3).
Proof.
  intros.
  induction H; auto.
  - induction H0; auto.
    eapply star_tran; eauto.
  - eapply star_tran; eauto.
Qed.
 *)


(*
Inductive InstrSt: Set :=
| istop: cvm_st -> InstrSt
| iconf: AnnoInstr -> cvm_st -> InstrSt
(*| rem: nat -> Loc -> Plc -> St -> St *)
| ils: InstrSt -> AnnoInstr -> InstrSt
(*| bsl: nat -> St -> AnnoTerm -> Plc -> Evidence -> St
| bsr: nat -> Evidence -> St -> St
| bp: nat -> Loc -> Loc -> St -> St -> St*) .
*)

(*
Theorem correct_path_exists:
  forall p e i,
    exists st',
    star (iconf i p e) (istop p st').
Proof.
  induction i; intros; simpl; eauto.
  -
    eexists.

    eapply star_tran; eauto.
    (*
  - destruct p.
    eapply star_tran; eauto.
    eapply star_transitive.
    apply star_strem.
    apply IHt.
    eapply star_tran; eauto. *)
  -
    edestruct IHi1.
    edestruct IHi2.
    eexists.
    eapply star_tran.
    econstructor.
    eapply star_transitive.
    apply star_stls.
    eassumption.
    eapply star_tran.
    apply seqStop.
    Abort.

    (*
    
  - eapply star_tran; eauto.
    eapply star_transitive.
    apply star_stbsl.
    apply IHt1.
    eapply star_tran; eauto.
    eapply star_transitive.
    apply star_stbsr.
    apply IHt2.
    eapply star_tran; eauto.
  -
    repeat dest_range.
    (*destruct p; destruct p0. *)
    eapply star_tran; eauto.
    eapply star_transitive.
    apply star_stbp.
    apply IHt1.
    apply IHt2.
    eapply star_tran; eauto.
Qed.
*)
*)

(** * Progress *)

Definition halt st :=
  match st with
  | istop _ _ _ => True
  | _ => False
  end.

(*
(** The Instr_step relation nevers gets stuck. *)

Theorem never_stuck:
  forall st0,
    halt st0 \/ exists e st1, Instr_step st0 e st1.
Proof.
  induction st0.
  - left; simpl; auto.
    
  - right.
    destruct a.
    + exists (Some (tr_asp_instr n0 n p)).
      eapply ex_intro; eauto.

      (*
    + exists (Some (req (fst r) (fst p) n n0 (unanno a))).
      repeat dest_range.
      eapply ex_intro; eauto. *)
    + exists None.
      eapply ex_intro; eauto.
      (*
      
    + exists (Some (split (fst r) n)).
      eapply ex_intro; eauto.
      
    + exists (Some (splitp (fst r) (fst p) (*(fst p0)*) n)).
      (*destruct p; destruct p0. *)
      repeat dest_range.
      eapply ex_intro; eauto. *)
     
    (*
  - right.
    destruct IHst0.
    + destruct st0; simpl in H; try tauto.
      exists (Some (rpy (pred n) n0 n1 n2)).
      eapply ex_intro; eauto.
    + destruct H as [e H].
      exists e.
      destruct H as [st1 H].
      exists (rem n n0 n1 st1). auto. *)
  - right.
    destruct IHst0.
    + destruct st0; simpl in H; try tauto.
      exists None. eapply ex_intro; eauto.
    + destruct H as [e H].
      exists e.
      destruct H as [st H].
      exists (ils st a). auto.
      (*
      
  - right.
    destruct IHst0.
    + destruct st0; simpl in H; try tauto.
      exists None. eapply ex_intro; eauto.
    + destruct H as [e0 H].
      exists e0.
      destruct H as [st H].
      exists (bsl n st a n0 e). auto.
  - right.
    destruct IHst0.
    + destruct st0; simpl in H; try tauto.
      exists (Some (join (pred n) n0)).
      eapply ex_intro; eauto.
    + destruct H as [e0 H].
      exists e0.
      destruct H as [st H].
      exists (bsr n e st). auto.
      
  - right.
    destruct IHst0_1 as [H|H].
    + destruct st0_1; simpl in H; try tauto.
      clear H.
      destruct IHst0_2.
      * destruct st0_2; simpl in H; try tauto.
        exists (Some (joinp (pred n) n0 n1 n3)).
        eapply ex_intro; eauto.
      * destruct H as [e0 H].
        exists e0.
        destruct H as [st H].
        exists (bp n n0 n1 (stop n2 e) st). auto.
    + destruct H as [e0 H].
      exists e0.
      destruct H as [st H].
      exists (bp n n0 n1 st st0_2). auto.
*)
Qed.
*)

(** * Termination *)

Inductive nstar: nat -> InstrSt -> InstrSt -> Prop :=
| nstar_refl: forall st, nstar 0 st st
| nstar_tran: forall st0 st1 st2 e n,
    nstar n st0 st1 -> Instr_step st1 e st2 -> nstar (S n) st0 st2.
Hint Resolve nstar_refl : core.

Require Import PeanoNat.

Lemma nstar_transitive:
  forall m n st0 st1 st2,
    nstar m st0 st1 ->
    nstar n st1 st2 ->
    nstar (m + n) st0 st2.
Proof.
  intros.
  induction H0.
  rewrite Nat.add_0_r; auto.
  apply IHnstar in H.
  eapply nstar_tran in H; eauto.
  rewrite plus_n_Sm in H.
  eauto.
Qed.

Lemma nstar_star:
  forall n st0 st1,
    nstar n st0 st1 -> star st0 st1.
Proof.
  intros.
  induction H; auto.
  eapply star_transitive; eauto.
  eapply star_tran; eauto.
Qed.

Lemma star_nstar:
  forall st0 st1,
    star st0 st1 ->
    exists n, nstar n st0 st1.
Proof.
  intros.
  induction H.
  - exists 0; auto.
  - destruct IHstar as [n G].
    exists (S n).
    rewrite <- Nat.add_1_l.
    eapply nstar_transitive; eauto.
    eapply nstar_tran; eauto.
Qed.


(*

(** Size of a term (number of steps to reduce). *)

Fixpoint tsize t: nat :=
  match t with
  | aprimInstr _ _ => 1
  (*| aatt _ _ _ _ x => 2 + tsize x *)
  | aseq x y => 2 + tsize x + tsize y
  (*| abseq _ _ _ x y => 3 + tsize x + tsize y
  | abpar _ _ _ _ x y => 2 + tsize x + tsize y *)
  end.

(** Size of a state (number of steps to reduce). *)

Fixpoint ssize s: nat :=
  match s with
  | istop _ _ => 0
  | iconf t _ _ => tsize t
  (*| rem _ _ _ x => 1 + ssize x *)
  | ils x t => 1 + ssize x + tsize t
  (*| bsl _ x t _ _ => 2 + ssize x + tsize t
  | bsr _ _ x => 1 + ssize x
  | bp _ _ _ x y => 1 + ssize x + ssize y *)
  end.

(** Halt state has size 0. *)

Lemma halt_size:
  forall st,
    halt st <-> ssize st = 0.
Proof.
  split; intros.
  - destruct st; simpl in H; try tauto.
  - destruct st; simpl in H; try tauto;
      try discriminate.
    + simpl; auto.
    + destruct a; simpl in H; discriminate.
Qed.

Require Import Lia.
(** A state decreases its size by one. *)

Lemma step_size:
  forall st0 e st1,
    Instr_step st0 e st1 ->
    S (ssize st1) = ssize st0.
Proof.
  intros.
  induction H; simpl; auto; lia.
Qed.

Lemma step_count:
  forall n t p e st,
    nstar n (iconf t p e) st ->
    tsize t = n + ssize st.
Proof.
  induction n; intros.
  - inv H; simpl; auto.
  - inv H.
    apply IHn in H1.
    rewrite H1.
    apply step_size in H2.
    lia.
Qed.

(** Every run terminates. *)

Theorem steps_to_stop:
  forall t p e st,
    nstar (tsize t) (iconf t p e) st ->
    halt st.
Proof.
  intros.
  apply step_count in H.
  apply halt_size.
  lia.
Qed.

(** * Numbered Labeled Transitions *)

Inductive nlstar: nat -> InstrSt -> list Ev -> InstrSt -> Prop :=
| nlstar_refl: forall st, nlstar 0 st [] st
| nlstar_tran: forall n st0 e st1 tr st2,
    Instr_step st0 (Some e) st1 -> nlstar n st1 tr st2 -> nlstar (S n) st0 (e :: tr) st2
| nlstar_silent_tran: forall n st0 st1 tr st2,
    Instr_step st0 None st1 -> nlstar n st1 tr st2 -> nlstar (S n) st0 tr st2.
Hint Resolve nlstar_refl : core.

Lemma nlstar_transitive:
  forall m n st0 tr0 st1 tr1 st2,
    nlstar m st0 tr0 st1 ->
    nlstar n st1 tr1 st2 ->
    nlstar (m + n) st0 (tr0 ++ tr1) st2.
Proof.
  intros.
  induction H.
  - rewrite app_nil_l; auto.
  - apply IHnlstar in H0.
    rewrite <- app_comm_cons.
    eapply nlstar_tran; eauto.
  - apply IHnlstar in H0.
    eapply nlstar_silent_tran; eauto.
Qed.

Lemma nlstar_lstar:
  forall n st0 tr st1,
    nlstar n st0 tr st1 -> lstar st0 tr st1.
Proof.
  intros.
  induction H; auto.
  - eapply lstar_tran; eauto.
  - eapply lstar_silent_tran; eauto.
Qed.

Lemma lstar_nlstar:
  forall st0 tr st1,
    lstar st0 tr st1 ->
    exists n, nlstar n st0 tr st1.
Proof.
  intros.
  induction H.
  - exists 0; auto.
  - destruct IHlstar as [n G].
    exists (S n).
    eapply nlstar_tran; eauto.
  - destruct IHlstar as [n G].
    exists (S n).
    eapply nlstar_silent_tran; eauto.
Qed.

Lemma nlstar_step_size:
  forall n st0 tr st1,
    nlstar n st0 tr st1 ->
    ssize st1 <= ssize st0.
Proof.
  intros.
  induction H; auto;
    apply step_size in H;
    lia.
Qed.

Require Import Minus.

Lemma lstar_nlstar_size:
  forall st0 tr st1,
    lstar st0 tr st1 ->
    nlstar (ssize st0 - ssize st1) st0 tr st1.
Proof.
  intros.
  induction H.
  - rewrite Nat.sub_diag; auto.
  - pose proof H as G.
    apply step_size in G.
    rewrite <- G.
    rewrite <- minus_Sn_m.
    + eapply nlstar_tran; eauto.
    + apply nlstar_step_size in IHlstar; auto.
  - pose proof H as G.
    apply step_size in G.
    rewrite <- G.
    rewrite <- minus_Sn_m.
    + eapply nlstar_silent_tran; eauto.
    + apply nlstar_step_size in IHlstar; auto.
Qed.

(** The reverse version of [nlstar]. *)

Inductive rlstar: nat -> InstrSt -> list Ev -> InstrSt -> Prop :=
| rlstar_refl: forall st, rlstar 0 st [] st
| rlstar_tran: forall n st0 e st1 tr st2,
    rlstar n st0 tr st1 -> Instr_step st1 (Some e) st2 ->
    rlstar (S n) st0 (tr ++ [e]) st2
| rlstar_silent_tran: forall n st0 st1 tr st2,
    rlstar n st0 tr st1 -> Instr_step st1 None st2 ->
    rlstar (S n) st0 tr st2.
Hint Resolve rlstar_refl : core.

Lemma rlstar_transitive:
  forall m n st0 tr0 st1 tr1 st2,
    rlstar m st0 tr0 st1 ->
    rlstar n st1 tr1 st2 ->
    rlstar (m + n) st0 (tr0 ++ tr1) st2.
Proof.
  intros.
  induction H0.
  - rewrite Nat.add_0_r; rewrite app_nil_r; simpl; auto.
  - apply IHrlstar in H.
    rewrite Nat.add_succ_r.
    rewrite app_assoc.
    eapply rlstar_tran; eauto.
  - apply IHrlstar in H.
    rewrite Nat.add_succ_r.
    eapply rlstar_silent_tran; eauto.
Qed.

Lemma rlstar_lstar:
  forall n st0 tr st1,
    rlstar n st0 tr st1 -> lstar st0 tr st1.
Proof.
  intros.
  induction H; auto.
  - eapply lstar_transitive; eauto.
    eapply lstar_tran; eauto.
  - rewrite <- app_nil_r with (l:=tr).
    eapply lstar_transitive; eauto.
    apply lstar_silent_tran with st2; auto.
Qed.

Lemma lstar_rlstar:
  forall st0 tr st1,
    lstar st0 tr st1 ->
    exists n, rlstar n st0 tr st1.
Proof.
  intros.
  induction H.
  - exists 0; auto.
  - destruct IHlstar as [n G].
    exists (S n).
    cut (rlstar (1 + n) st0 ([e] ++ tr) st2).
    simpl; auto.
    eapply rlstar_transitive; eauto.
    cut (rlstar 1 st0 ([] ++ [e]) st1).
    simpl; auto.
    eapply rlstar_tran; eauto.
  - destruct IHlstar as [n G].
    exists (S n).
    cut (rlstar (1 + n) st0 ([] ++ tr) st2).
    rewrite app_nil_l; auto.
    eapply rlstar_transitive; eauto.
    eapply rlstar_silent_tran; eauto.
Qed.

Lemma rlstar_nlstar:
  forall n st0 tr st1,
    rlstar n st0 tr st1 <-> nlstar n st0 tr st1.
Proof.
  split; intros.
  - induction H; auto.
    + rewrite <- Nat.add_1_r.
      eapply nlstar_transitive; eauto.
      eapply nlstar_tran; eauto.
    + rewrite <- Nat.add_1_r.
      rewrite <- app_nil_r with (l:=tr).
      eapply nlstar_transitive; eauto.
      eapply nlstar_silent_tran; eauto.
  - induction H; auto.
    + rewrite <- Nat.add_1_l.
      assert (G: e :: tr = [e] ++ tr).
      simpl; auto.
      rewrite G.
      eapply rlstar_transitive; eauto.
      rewrite <- app_nil_l with (l:=[e]).
      eapply rlstar_tran; eauto.
    + rewrite <- Nat.add_1_l.
      rewrite <- app_nil_l with (l:=tr).
      eapply rlstar_transitive; eauto.
      eapply rlstar_silent_tran in H; eauto.
Qed.

 *)

















(* EXTRA 

Lemma advance_servers_determ: forall ai m m' m'',
    advance_servers ai m m' ->
    advance_servers ai m m'' ->
    m' = m''.
Proof.
Admitted.

Lemma advance_ist_iff: forall x m m' p e,
    advance_servers x m m' ->
    advance_servers_ist (iconf x p e) m m'.
Proof.
Admitted.

Lemma compliment_alseq_skip: forall r l t1 t2 m m',
    (*well_formed (alseq r l t1 t2) -> *)
    ws_instr (instr_compiler (alseq r l t1 t2)) m ->
    advance_servers (instr_compiler t1) m m' ->
    ws_instr (instr_compiler t1) m /\
    ws_instr (instr_compiler t2) m'.
Proof.
  intros.
  invc H.
  split.
  -
    eassumption.
  -
    assert (m' = m'0).
    {
      eapply advance_servers_determ; eauto.
    }
    subst.
    eauto.
Defined.

Lemma compliment_alseq_skip': forall r l t1 t2 m m',
    (*well_formed (alseq r l t1 t2) -> *)
    ws_instr (instr_compiler t1) m ->
    advance_servers (instr_compiler t1) m m' ->
    ws_instr (instr_compiler t2) m' ->
    ws_instr (instr_compiler (alseq r l t1 t2)) m.  
Proof.
Admitted.


Require Import Auto.

Lemma compliment_focus: forall t1 t2,
    ws_instr (instr_compiler t1) (copland_compliment t2 (copland_compliment t1 [])).
Proof.
Admitted.

Lemma advance_assoc: forall t1 t2 m,
    advance_servers (instr_compiler t1) (copland_compliment t2 (copland_compliment t1 m))
                    (copland_compliment t2 m).
Proof.
Admitted.


(*
Fixpoint num_server_req_handles (ai:AnnoInstr) (toPl:Plc) : nat :=
  match ai with
  | aprimInstr i pi => 0
  | aReq _ _ _ _ _ (pl,_) => if (toPl =? pl) then 1 else 0
  | aseq ai1 ai2 =>
    (num_server_req_handles ai1 toPl) +
    (num_server_req_handles ai2 toPl)
  end.

Fixpoint num_server_req_handles_ist (iSt:InstrSt) (toPl:Plc) : nat :=
  match iSt with
  | istop _ _ => 0
  | iconf ai _ _ => (num_server_req_handles ai toPl)
  | iWaitReq _ _ ai => (num_server_req_handles ai toPl)
  | iDoRem iSt' _ => (num_server_req_handles_ist iSt' toPl)
  | iSeqReqWaits iSt1 iSt2 =>
    (num_server_req_handles_ist iSt1 toPl) +
    (num_server_req_handles_ist iSt2 toPl)
  | irpyWait _ _ _ _ => 0
  | ils iSt ai =>
    (num_server_req_handles_ist iSt toPl) +
    (num_server_req_handles ai toPl)
  end.

(* 
   Relates an AnnoInstr + its servers before executing 
   that AnnoInstr, to its servers after.

   Need to map over all instances of (aReq _ _ _ _ toPl) instructions in 
   the client AnnoInstr and skip an iWaitReq at toPl for each. 

   TODO:  use something like num_server_req_handles above to determine a 
   predictable number of new "iWaitReq" instrSts to peel off front of each server st code 
*)
Definition advance_servers :
  AnnoInstr ->
  MapC Plc InstrSt ->
  MapC Plc InstrSt -> Prop.
Admitted.

(* same as advance_servers, but for InstrSt *)
Definition advance_servers_ist :
  InstrSt ->
  MapC Plc InstrSt ->
  MapC Plc InstrSt -> Prop.
Admitted.
*)

*)
