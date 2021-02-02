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

(*
| ireqWait: nat -> Plc -> (*Plc ->*) AnnoInstr -> InstrSt
*)

Inductive AnnoInstr: Set :=
| aprimInstr: nat -> Prim_Instr -> AnnoInstr
| aReq: nat -> nat -> Loc -> Loc -> (*nat ->*) Plc -> (*Loc ->*) (*Loc -> *) AnnoInstr
| aWaitReq: nat -> (*Plc ->*) AnnoInstr
| aResp: nat -> Plc -> AnnoInstr 
(*| aWaitRpy: nat -> Plc -> (*Loc -> bool ->*) AnnoInstr*)
| aseq: AnnoInstr -> AnnoInstr -> AnnoInstr.

Definition asp_instr (a:ASP) : Prim_Instr :=
  match a with
  | CPY => copy
  | ASPC i args => umeas i args
  | SIG => sign
  | HSH => hash
  end.

(*
(*
Definition ev_store := MapC nat EvidenceC.
*)
Record cvm_st : Type := mk_st
                          {
                            st_ev:EvidenceC ;
                            st_pl:Plc ;                 
                            st_trace:list Ev ;
                            (* st_store:ev_store *) } .

Definition empty_vmst := mk_st mtc 0 []. (* mtc [] 0 [] *)

Instance eta_r : Settable _ := settable! mk_st <st_ev; st_pl; st_trace>.

Definition setEv a x := x <| st_ev := a|> <|st_pl := 42|>.

Compute (setEv (ggc 0 mtc) empty_vmst).
 *)

(*
Definition setup := MapC Plc AnnoInstr.
*)

(*
Definition bookend (ai:AnnoInstr) (req_loc rpy_loc:Loc): AnnoInstr :=
  aseq (aPutStore req_loc) (aseq ai (aGetStore rpy_loc)).
 *)

(*
Definition add_at (s:setup) (q:Plc) (comp:AnnoInstr) : setup :=
  let old_instr := map_get s q in
  match old_instr with
  | Some m =>
      let new_comp := aseq m comp in
      map_set s q new_comp
  | _ => map_set s q comp
  end.
*)

Fixpoint instr_compiler (t:AnnoTerm) : AnnoInstr :=
  match t with
  | aasp r l a => aprimInstr (fst r) (asp_instr a)
  | aatt (i,j) _ (req_loc,rpy_loc) _ q _ =>
    (aReq i (Nat.pred j) req_loc rpy_loc q)
         (*(aWaitRpy (Nat.pred j) q)  *)   
  | alseq _ _ t1 t2 => aseq (instr_compiler t1) (instr_compiler t2)
  end.

(*
Fixpoint copland_compliment (t:AnnoTerm) (s:setup): setup :=
  match t with
  (*| aasp r l a => aprimInstr (fst r) (asp_instr a) *)
  | aatt (i,j) _ (req_loc,rpy_loc) q t' =>
    let comp := instr_compiler t' in
    add_at s q (
    aseq (aGetStore (Nat.pred j) q rpy_loc false)
         (aseq comp (aPutStore i q req_loc false)))
(*
    aseq (aPutStore i j q req_loc rpy_loc)
         (aGetStore (Nat.pred j) q rpy_loc)  *)
  | alseq _ _ t1 t2 =>
    let s1 := copland_compliment t1 s in
    let s2 := copland_compliment t2 s1 in
    s2
  | _ => []
  end.
*)
    

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

(*
Definition update_ev_st (st:cvm_st) (e:EvidenceC) : cvm_st :=
  st <| st_ev := e|>.
 *)

(*
Inductive sLoc: Set :=
| Empty : sLoc
| Full : EvidenceC -> sLoc.

Definition heap := list (Loc*sLoc). (*MapC Loc sLoc. *)
Compute map_set map_empty 0 Empty.
Check (MapC Loc Loc).

Definition put_heap (m:heap) (k:Loc)
           (e:EvidenceC) (*(there:bound_to m k Empty)*): heap :=
  map_set m k (Full e).

Definition clear_loc (m:heap) (k:Loc) : heap :=
  map_set m k Empty.

Definition locEmpty (h:heap) (loc:Loc): Prop :=
  bound_to h loc Empty.

Definition locContains (h:heap) (loc:Loc) (e:EvidenceC): Prop :=
  bound_to h loc (Full e).
*)


Inductive InstrSt: Set :=
| istop: Plc -> EvidenceC -> (*heap ->*) InstrSt
| iconf: AnnoInstr -> Plc -> EvidenceC -> (*heap ->*) InstrSt
(*| ireqWait: nat -> Plc -> (*Plc ->*) AnnoInstr -> InstrSt *)
| irpyWait: nat -> Loc -> Plc -> Plc -> InstrSt
| ils: InstrSt -> AnnoInstr -> InstrSt
(*| bsl: nat -> St -> AnnoTerm -> Plc -> Evidence -> St
| bsr: nat -> Evidence -> St -> St
| bp: nat -> Loc -> Loc -> St -> St -> St*) .

(*
Inductive AnnoInstr: Set :=
| aprimInstr: nat -> Prim_Instr -> AnnoInstr
| aReq: nat -> nat -> (*nat ->*) Plc -> (*Loc ->*) (*Loc -> *) AnnoInstr
(*| aWaitReq: nat -> Plc -> AnnoInstr *)
| aResp: nat -> Plc -> AnnoInstr 
(*| aWaitRpy: nat -> Plc -> (*Loc -> bool ->*) AnnoInstr*)
| aseq: AnnoInstr -> AnnoInstr -> AnnoInstr.
*)


(*
Fixpoint instr_heap (iSt: InstrSt) : heap :=
  match iSt with
  | istop _ _ h => h
  | iconf _ _ _ h => h
  | rem _ _ _ _ _ h => h
  | ils i _ => instr_heap i
  end.
 *)

(*
Inductive AnnoInstr: Set :=
| aprimInstr: nat -> Prim_Instr -> AnnoInstr
| aReq: nat -> (*nat ->*) Plc -> (*Loc ->*) (*Loc -> *) AnnoInstr
| aWaitReq: nat -> Plc -> AnnoInstr
| aResp: nat -> Plc -> AnnoInstr
| aWaitRpy: nat -> Plc -> (*Loc -> bool ->*) AnnoInstr
| aseq: AnnoInstr -> AnnoInstr -> AnnoInstr.
 *)

Inductive hLoc : Set :=
| Empty : hLoc
| Full: (Plc*EvidenceC) -> hLoc.
    
Definition heap := hLoc. (*option (Plc*EvidenceC). *)

Print req.
Check req.

Inductive Instr_step: InstrSt -> heap -> option Ev -> InstrSt -> heap -> Prop :=
| primStep: forall x pi p e h,
    Instr_step (iconf (aprimInstr x pi) p e) h
               (Some (tr_asp_instr x p pi))
               (istop p (ev_asp_instr x pi e)) h
| atReqStep: forall i p q e h j req_loc rpy_loc,
    Instr_step (iconf (aReq i j req_loc rpy_loc q) p e) h
               (Some (req i req_loc p q (*(asp CPY)*)))
               (irpyWait j rpy_loc q p) (Full (q,e))
(*(put_heap h req_loc e)*) (* TODO: clear local ev here? *)
(*(rem i j rpy_loc p q) (put_heap h req_loc e) *)
| atRpyStep: forall j me them e rpy_loc,
    (*me = inp ->  *)
    (* h = (Full (me,e)) -> *)
    Instr_step (irpyWait j rpy_loc them me) (Full (me,e))
               (Some (rpy j rpy_loc me them))
               (istop me e) Empty (* TODO: clear local ev here? *)
               (*(rem i j rpy_loc p q) (put_heap h req_loc e) *)
(*| atWaitStep: forall h rpy_loc i j p q,
    locEmpty h rpy_loc ->                
    Instr_step (rem i j rpy_loc p q) h
               None
               (rem i j rpy_loc p q) h *)

| atReqWaitStep: forall e e' i me,
    (*locContains h rpy_loc eres -> *)
    (*me = inp -> *)
    Instr_step (iconf (aWaitReq i) me e') (Full (me,e))
               (*Instr_step (ireqWait i me next) (Some (me,e)) *)
               None
               (istop me e) Empty (* Does it matter if me or me'? *)
| atRespStep: forall h e i p q,
    (*locContains h rpy_loc eres -> *)
    Instr_step (iconf (aResp i q) p e) h
    (*Instr_step (iconf (aGetStore i q rpy_loc true) p e) h*)
               (* (Some (rpy i(*(Nat.pred j)*) 0 p q)) *)
               None
               (istop p e) (Full (q,e))



               (*
| atRpyStep_silent: forall h e eres i p q rpy_loc,
    locContains h rpy_loc eres ->
    Instr_step (iconf (aGetStore i q rpy_loc false) p e) h
               None
               (istop p eres) (clear_loc h rpy_loc)
*)
(*
| atRpyStep: forall h e i j p q rpy_loc,
    locContains h rpy_loc e ->
    Instr_step (rem i j rpy_loc p q) h
               (Some (rpy (Nat.pred j) rpy_loc p q))
               (istop p e) (clear_loc h rpy_loc)
*)
| seqStart: forall x y p e h,
    Instr_step (iconf (aseq x y) p e) h
               None
               (ils (iconf x p e) y) h
| seqStep: forall st0 st1 ev x h h',
    Instr_step st0 h ev st1 h' ->
    Instr_step (ils st0 x) h ev (ils st1 x) h'
| seqStop: forall y p e h,
    Instr_step (ils (istop p e) y) h None (iconf y p e) h.
Hint Constructors Instr_step : core.




(*
Definition orchestrate (t:AnnoTerm): (AnnoInstr * setup) :=
  let main_thread := instr_compiler t in
  let servers := copland_compliment t map_empty in
  (main_thread, servers).
*)


(*
Inductive InstrSt: Set :=
| istop: Plc -> EvidenceC -> heap -> InstrSt
| iconf: AnnoInstr -> Plc -> EvidenceC -> heap -> InstrSt
| rem: nat -> nat -> Loc -> Plc -> Plc -> (*InstrSt ->*) heap -> InstrSt
| ils: InstrSt -> AnnoInstr -> InstrSt
 *)

(*
Definition configs := MapC Plc InstrSt.

Definition code := (AnnoInstr*setup)%type.
*)

(*Definition world := (InstrSt*configs)%type. *)

(*
Definition build_one' (p:Plc) (x:AnnoInstr) : InstrSt :=
  iconf x p mtc.
*)

(*
Definition build_one (pr:Plc*AnnoInstr) : InstrSt :=
  build_one' (fst pr) (snd pr).

Search (list _ -> list _ -> list (_*_)).
Print list_prod.
Print combine.

Check fold_left.
Check map.
Check combine.
*)

(*
Definition build_world' (start_pl:Plc) (init_ev:EvidenceC) (*(h:heap)*)
           (x:code): (InstrSt*configs) :=
  let code_start := (fst x) in
  let env_code := (snd x) in (* :: setup == MapC Plc AnnoInstr *)
  let a := (iconf code_start start_pl init_ev) in
  let places := map_dom env_code in (* :: list Plc *)
  let codes := map_vals env_code in (* :: list AnnoInstr *)
  let both := combine places codes in (* :: list (Plc*AnnoInstr) *)
  let configs := map (build_one) both in (* :: list (InstrSt) *)
  let finals := combine places configs in
  
  (a,finals).
*)

(*
Definition orchestrate (t:AnnoTerm): (AnnoInstr * setup) :=
 *)

(*
Definition build_world (t:AnnoTerm) (p:Plc)
           (e:EvidenceC) (*(h:heap)*) : (InstrSt*configs) :=
  let codes := orchestrate t in
  build_world' p e codes.
*)

(*
Definition build_one' (p:Plc) (x:AnnoInstr) : InstrSt :=
  iconf x p mtc.
*)

(*
Definition add_one_at (q:Plc)(s:list InstrSt) (ai:AnnoInstr) : list InstrSt :=
  let one := build_one' q ai in
  one :: s.
 *)

(*
Definition configs := MapC Plc InstrSt.
 *)

(*
Definition codes := MapC Plc AnnoInstr.
*)

(*
Definition add_st_at (q:Plc) (s:configs) (i:nat) (j:nat) (p:Plc) (comp:AnnoInstr) : configs :=
  let currStMaybe := map_get s q in
  let newComp := (ils (ireqWait i q)
                          (aseq comp
                                (aResp j p))) in
  match currStMaybe with
  | Some (ils currSt ai) => 
    let newSt := ils (ils currSt newComp in
    map_set s q newSt
  | _ => map_set s q newComp
  end.
 *)

Require Import Coq.Arith.PeanoNat.

Search ({_ = _} + {_ <> _}).

Fixpoint remove (k : Plc) (s : MapC Plc AnnoInstr) : MapC Plc AnnoInstr :=
 match s with
  | nil => nil
  | (k',x) :: l =>
    if (Nat.eq_dec k k') then remove k l else (k',x) :: remove k l
 end.

Definition map_replace m q (comp:AnnoInstr) :=
  let cleared_map := remove q m in
  map_set cleared_map q comp.

Definition append_code_at (q:Plc) (s:MapC Plc AnnoInstr) (code:AnnoInstr) :
  MapC Plc AnnoInstr :=
  let currCodeMaybe := map_get s q in
  match currCodeMaybe with
  | Some oldCode => 
    let newCode := aseq oldCode code in
    map_replace s q newCode
  | _ => map_set s q code
  end.
    

Fixpoint copland_compliment_l (t:AnnoTerm) (s:MapC Plc AnnoInstr): MapC Plc AnnoInstr :=
  match t with
  | aasp r l a => s
  | aatt (i,j) _ (_,_) p q t' =>
    let term_code := instr_compiler t' in
    let node_code :=
        aseq (aseq
                (aWaitReq i)
                term_code) (* "me" place will be in iconf context *)
             (aResp (Nat.pred j) p) in
    append_code_at q s node_code
  | alseq _ _ t1 t2 =>
    let s1 := copland_compliment_l t1 s in
    let s2 := copland_compliment_l t2 s1 in
    s2
 (* | _ => [] *)
  end.


Definition wrap_server_config (pr:AnnoInstr*Plc): InstrSt :=
  iconf (fst pr) (snd pr) mtc.

Definition init_configs (ls:list AnnoInstr) (ps:list Plc) : list InstrSt :=
  map wrap_server_config (combine ls ps).

Definition orchestrate_l (t:AnnoTerm) (p:Plc) (e:EvidenceC):
  (InstrSt * list InstrSt) :=
  let main_code := instr_compiler t in (* AnnoInstr *)
  let server_codes := copland_compliment_l t [] in (* Map Plc AnnoInstr *)
  let codes := map_vals server_codes in (* list AnnoInstr *)
  let server_places := map_dom server_codes in (* list Plc *)
  let server_configs := init_configs codes server_places in
  (iconf main_code p e, server_configs).

(*
Inductive WorldTerm: Set :=
| onePlat: InstrSt -> WorldTerm
| parPlats: WorldTerm -> WorldTerm -> WorldTerm.
 *)


Inductive WorldTerm: Set :=
| onePlat: InstrSt -> WorldTerm
| parPlats: WorldTerm -> WorldTerm -> WorldTerm
| donePlat: nat -> EvidenceC -> WorldTerm.

(* Remember:  Start term remains left-most parallel WorldTerm subterm (to grab final evidence at end *)
Definition combineInstrSt (wt:WorldTerm) (i:InstrSt)  : WorldTerm :=
  parPlats wt (onePlat i) .

Check fold_left.

Definition build_world_term'' (startTerm: WorldTerm) (ls:list InstrSt) : WorldTerm :=
  fold_left combineInstrSt ls startTerm.
  

Definition build_world_term' (startInstr:InstrSt) (ls:list InstrSt) : WorldTerm :=
  build_world_term'' (onePlat startInstr) ls.
  
Definition build_world_term (t:AnnoTerm) (p:Plc) (e:EvidenceC) : WorldTerm :=
  let '(one,rest) := orchestrate_l t p e in
  build_world_term' one rest.


(*
Inductive InstrSt: Set :=
| istop: Plc -> EvidenceC -> (*heap ->*) InstrSt
*)

Inductive platStep_l : WorldTerm -> heap -> option Ev ->
                       WorldTerm -> heap -> Type :=
| platStepOne: forall i i' ev h h',
    Instr_step i h ev i' h' ->
    platStep_l (onePlat i) h ev (onePlat i') h'
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

Inductive lstar_world: WorldTerm -> heap -> list Ev -> WorldTerm -> heap -> Prop :=
| lstar_refl: forall w h, lstar_world w h [] w h
| lstar_tran: forall e tr wt wt' wt'' h h' h'',
    platStep_l wt h (Some e) wt' h' ->
    lstar_world wt' h' tr wt'' h'' ->
    lstar_world wt h (e :: tr) wt'' h''
| lstar_silent_tran: forall wt wt' wt'' h h' h'' tr,
    platStep_l wt h None wt' h' ->
    lstar_world wt' h' tr wt'' h'' ->
    lstar_world wt h tr wt'' h''.
Hint Resolve lstar_refl : core.

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
  (*att 1 asp1. *)

Definition ex1_term_annotated :=
  snd (anno' ex1_term 0 [42;43] 2 ).

(*
Definition ex1_heap := [(42,Empty);(43,Empty)].
Check ex1_heap.
*)

Compute ex1_term_annotated.

Compute (orchestrate_l ex1_term_annotated 2 mtc).

Compute (copland_compliment_l (snd (anno' (att 1 asp1) 0 [42;43] 2)) []).

Compute (copland_compliment_l ex1_term_annotated []).

Compute (build_world_term ex1_term_annotated 2 mtc).

Ltac inv_lstar :=
  match goal with
  (*|[H: locContains (?C) _ _  |- _ ] => invc H
  | [H: locEmpty (?C) (*(put_heap _ _ _)*) _  |- _ ] => invc H *)
  | [H: Instr_step (?C _) _ _ _ _  |- _ ] => invc H
  | [H: platStep_l
          (onePlat (?C _)) _ _ _ _ |- _ ] => invc H
  | [H: platStep_l
          (parPlats (?C _) _) _ _ _ _ |- _ ] => invc H
  | [H: lstar_world
          (parPlats (?C _) _) _ _ _ _ |- _] => invc H
  end;
  df;
  try solve_by_inversion.


Set Nested Proofs Allowed.

Definition ex1_heap : heap := Empty. (* option (Plc*EvidenceC) := None. *)

Lemma world_refines_lts_event_ordering_ex1:
  forall (*t p e*) e' (*h*) h' tr (*et*) (*(wt:WorldTerm)*) ,
    (*well_formed t -> *)
    (* let wt := build_world_term t p e in (*(InstrSt*configs)*) *)
    
    lstar_world (build_world_term ex1_term_annotated 2 mtc) ex1_heap tr (donePlat 2 e') h' ->
    LTS.lstar (conf ex1_term_annotated 2 mt) tr (stop 2 (aeval ex1_term_annotated 2 mt)).
Proof.
  intros.
  unfold build_world_term in *.
  unfold orchestrate_l in *.
  unfold build_world_term' in *.
  unfold build_world_term'' in *.
  unfold ex1_term_annotated in *.
  cbn in *.
  unfold combineInstrSt in *.
  unfold ex1_heap in *.
  df.
  unfold wrap_server_config in *.
  (*unfold build_one' in *. *)

  df.

  repeat inv_lstar.

  admit.
  admit.
  admit.
  admit.
  admit.
  admit.

  (*
  assert (tr0 = []).
  {
    invc H0; try solve_by_inversion.
    tauto.
  }
  subst.

  eapply lstar_tran.
  eapply statt.

  eapply lstar_tran.
  eapply stattstep.
  econstructor.
  eapply lstar_tran.
  apply stattstop.
  apply lstar_refl.

  assert (tr0 = []).
  {
    invc H0; try solve_by_inversion.
    tauto.
  }
  subst.

  eapply lstar_tran.
  eapply statt.

  eapply lstar_tran.
  eapply stattstep.
  econstructor.
  eapply lstar_tran.
  apply stattstop.
  apply lstar_refl.

    assert (tr0 = []).
  {
    invc H0; try solve_by_inversion.
    tauto.
  }
  subst.

  eapply lstar_tran.
  eapply statt.

  eapply lstar_tran.
  eapply stattstep.
  econstructor.
  eapply lstar_tran.
  apply stattstop.
  apply lstar_refl.
  Defined.
   *)
Abort.



HERE




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

    
