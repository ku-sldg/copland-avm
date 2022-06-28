Require Import Term_Defs OptMonad_Coq BS Preamble.
Require Import StructTactics Defs.


Require Import Lia Coq.Program.Tactics.
Require Import List.
Import List.ListNotations.







(** * Annotated Terms

    Annotated terms are used to ensure that each distinct event has a
    distinct natural number.  To do so, each term is annotated by a
    pair of numbers called a range.  Let [(i, k)] be the label for
    term [t].  The labels will be chosen to have the property such
    that for each event in the set of events associated with term [t],
    its number [j] will be in the range [i <= j < k].  *)

Definition Range: Set := nat * nat.

Inductive AnnoTerm: Set :=
| aasp: Range -> ASP -> AnnoTerm
| aatt: Range -> Plc -> AnnoTerm -> AnnoTerm
| alseq: Range -> AnnoTerm -> AnnoTerm -> AnnoTerm
| abseq: Range -> Split -> AnnoTerm -> AnnoTerm -> AnnoTerm
| abpar: Range -> Split -> AnnoTerm -> AnnoTerm -> AnnoTerm.

Fixpoint esize t :=
  match t with
  | aasp _ _ => 1
  | aatt _ _ t1 => 2 + esize t1
  | alseq _ t1 t2 => esize t1 + esize t2
  | abseq _ _ t1 t2 => 2 + esize t1 + esize t2
  | abpar _ _ t1 t2 => 2 + esize t1 + esize t2
  end.

Definition range x :=
  match x with
  | aasp r _ => r
  | aatt r _ _ => r
  | alseq r _ _ => r
  | abseq r _ _ _ => r
  | abpar r _ _ _ => r
  end.


(*
Inductive AnnoTermPar: Set :=
| aasp_par: ASP -> AnnoTermPar
| aatt_par: Plc -> Term -> AnnoTermPar
| alseq_par: AnnoTermPar -> AnnoTermPar -> AnnoTermPar
| abseq_par: Split -> AnnoTermPar -> AnnoTermPar -> AnnoTermPar
| abpar_par: Loc -> Split -> AnnoTermPar -> Term -> AnnoTermPar.

Fixpoint unannoPar (t:AnnoTermPar) : Term :=
  match t with
  | aasp_par a => asp a
  | aatt_par p t => att p t
  | alseq_par a1 a2 => lseq (unannoPar a1) (unannoPar a2)                 
  | abseq_par spl a1 a2 => bseq spl (unannoPar a1) (unannoPar a2) 
  | abpar_par _ spl a1 a2 => bpar spl (unannoPar a1) a2
  end.

Fixpoint anno_par (t:Term) (loc:Loc) : (Loc * AnnoTermPar)  :=
  match t with
  | asp a => (loc, aasp_par a)
  | att p t' => (loc, aatt_par p t')
                     
  | lseq t1 t2 =>
    let '(loc', t1') := anno_par t1 loc in
    let '(loc'', t2') := anno_par t2 loc' in

    (loc'', alseq_par t1' t2')
      
  | bseq spl t1 t2 =>
    let '(loc', t1') := anno_par t1 loc in
    let '(loc'', t2') := anno_par t2 loc' in

    (loc'', abseq_par spl t1' t2')
      
  | bpar spl t1 t2 =>
    let '(loc', t1') := anno_par t1 (S loc) in
    
    (loc', abpar_par loc spl t1' t2)
  end.

Definition peel_loc (ls:list Loc) : Opt (Loc * list Loc) :=
  match ls with
  | bs :: ls' => ret (bs, ls')
  | _ => failm
  end.

Fixpoint anno_par_list' (t:Term) (ls:list Loc) : Opt (list Loc * AnnoTermPar) :=
  match t with
  | asp a => ret (ls, aasp_par a)
  | att p t' => ret (ls, aatt_par p t')
  | lseq t1 t2 =>
    '(ls', t1') <- anno_par_list' t1 ls ;;
    '(ls'', t2') <- anno_par_list' t2 ls' ;;
    ret (ls'', alseq_par t1' t2')
  | bseq spl t1 t2 =>
    '(ls', t1') <- anno_par_list' t1 ls ;;
    '(ls'', t2') <- anno_par_list' t2 ls' ;;
    ret (ls'', abseq_par spl t1' t2')
  | bpar spl t1 t2 =>
    '(loc, ls') <- peel_loc ls ;;
    '(ls'', t1') <- anno_par_list' t1 ls' ;;
    ret (ls'', abpar_par loc spl t1' t2)
  end.

Definition anno_par_list (t:Term) (ls:list Loc) : Opt AnnoTermPar :=
  '(ls', t') <- anno_par_list' t ls ;;
  ret t'.

Set Nested Proofs Allowed.

Lemma peel_loc_fact: forall ls ls' loc,
    peel_loc ls = Some (loc, ls') ->
    length ls' = length ls - 1.
Proof.
  intros.
  generalizeEverythingElse ls.
  induction ls; intros; ff.
  unfold ret in *. inversion H.
  subst.
  lia.
Defined.

Lemma par_list_helper: forall t1 t1' ls ls',
    anno_par_list' t1 ls = Some (ls', t1') ->
    length ls' = length ls - top_level_thread_count t1.
Proof.
  intros.
  generalizeEverythingElse t1.
  induction t1; intros.
  -
    ff.
    unfold ret in *.
    ff.
    lia.
  -
    ff.
    unfold ret in *.
    ff.
    lia.
  -
    ff.
    unfold bind in *.
    unfold ret in *.
    ff.
    find_eapply_hyp_hyp.
    find_eapply_hyp_hyp.
    lia.
  -
    ff.
    unfold bind in *.
    unfold ret in *.
    ff.
    find_eapply_hyp_hyp.
    find_eapply_hyp_hyp.
    lia.
  -
    ff.
    unfold bind in *.
    unfold ret in *.
    ff.
    find_eapply_hyp_hyp.
    rewrite Heqo0.
    assert (length l0 = length ls - 1).
    {
      eapply peel_loc_fact.
      eauto.
    }
    lia.
Defined.

Lemma peel_loc_fact2: forall ls, 
    length ls >= 1 ->
    exists res, peel_loc ls = Some res.
Proof.
  intros.
  generalizeEverythingElse ls.
  induction ls; intros.
  -
    ff.
  -
    ff.
    unfold ret.
    eauto.
Defined.

Lemma anno_par_list_some : forall ls t,
  length ls >= (top_level_thread_count t) ->
  exists t', anno_par_list t ls = Some t'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    ff.
    eauto.
  -
    ff.
    eauto.
  -
    ff.
    unfold anno_par_list.
    cbn.
    destruct (anno_par_list' t1 ls) eqn:hi.
    unfold bind.
    ff.
    unfold ret.
    eauto.

    assert (length l >= top_level_thread_count t2).
    {
      assert (length ls >= top_level_thread_count t2) by lia.
      assert (length l = length ls - (top_level_thread_count t1)).
      {


        eapply par_list_helper; eauto.
      }
      rewrite H1.
      lia.
    }

    find_eapply_hyp_hyp.
    destruct_conjs.
    unfold anno_par_list in H1.
    unfold bind in H1.
    ff.

    assert (length ls >= top_level_thread_count t1) by lia.
    find_eapply_hyp_hyp.
    destruct_conjs.
    unfold anno_par_list in H1.
    unfold bind in H1.
    ff.
  -
    ff.
    unfold anno_par_list.
    cbn.
    destruct (anno_par_list' t1 ls) eqn:hi.
    unfold bind.
    ff.
    unfold ret.
    eauto.

    assert (length l >= top_level_thread_count t2).
    {
      assert (length ls >= top_level_thread_count t2) by lia.
      assert (length l = length ls - (top_level_thread_count t1)).
      {


        eapply par_list_helper; eauto.
      }
      rewrite H1.
      lia.
    }

    find_eapply_hyp_hyp.
    destruct_conjs.
    unfold anno_par_list in H1.
    unfold bind in H1.
    ff.

    assert (length ls >= top_level_thread_count t1) by lia.
    find_eapply_hyp_hyp.
    destruct_conjs.
    unfold anno_par_list in H1.
    unfold bind in H1.
    ff.
  -
    ff.
    unfold anno_par_list.
    cbn.
    destruct (anno_par_list' t1 ls) eqn:hi.
    unfold bind.
    ff.
    unfold ret.
    eauto.

    assert (length l0 >= top_level_thread_count t1).
    {
      assert (length l0 = length ls - 1).
      {
        eapply peel_loc_fact; eauto.
      }
      lia.
    }
    find_eapply_hyp_hyp.
    destruct_conjs.
    unfold anno_par_list in H1.
    unfold bind in H1. ff.

    assert (length ls >= 1) by lia.


    edestruct peel_loc_fact2.
    eassumption.
    rewrite H1 in *.
    ff.

    unfold bind in *.
    ff.
    unfold ret in *; ff.
    eauto.

    assert (length l0 >= top_level_thread_count t1).
    {
      assert (length l0 = length ls - 1).
      {
        eapply peel_loc_fact; eauto.
      }
      lia.

    }
    find_eapply_hyp_hyp.
    destruct_conjs.
    unfold anno_par_list in H1.
    unfold bind in H1. ff.

     assert (length ls >= 1) by lia.


    edestruct peel_loc_fact2.
    eassumption.
    rewrite H1 in *.
    ff.
Defined.

    
    
    
              

Definition annotated_par (x:Term) :=
  snd (anno_par x 0).
*)

Inductive term_sub : Term -> Term -> Prop :=
| termsub_refl_annt: forall t: Term, term_sub t t
| aatt_sub_annt: forall t t' p,
    term_sub t' t ->
    term_sub t' (att p t)
| alseq_subl_annt: forall t' t1 t2,
    term_sub t' t1 ->
    term_sub t' (lseq t1 t2)
| alseq_subr_annt: forall t' t1 t2,
    term_sub t' t2 ->
    term_sub t' (lseq t1 t2)
| abseq_subl_annt: forall t' t1 t2 s,
    term_sub t' t1 ->
    term_sub t' (bseq s t1 t2)
| abseq_subr_annt: forall t' t1 t2 s,
    term_sub t' t2 ->
    term_sub t' (bseq s t1 t2)
| abpar_subl_annt: forall t' t1 t2 s,
    term_sub t' t1 ->
    term_sub t' (bpar s t1 t2)
| abpar_subr_annt: forall t' t1 t2 s,
    term_sub t' t2 ->
    term_sub t' (bpar s t1 t2).
Hint Constructors term_sub : core.

Lemma termsub_transitive: forall t t' t'',
    term_sub t t' ->
    term_sub t' t'' ->
    term_sub t t''.
Proof.  
  generalizeEverythingElse t''.
  induction t'';
    intros H H0; ff.
    (* try (invc H0; eauto). *)
Defined.


(*

Lemma nullify_no_none_nones_seq: forall t t' t1 t2 sp,
    nullify_branchesP t t' ->
    term_sub (bseq sp t1 t2) t' ->
    sp = (ALL,ALL).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a; ff; invc H; ff.
  -
    invc H; ff.
    invc H0.
    
    eapply IHt.
    2: { eassumption. }
    econstructor.
    eauto.
  -
    invc H; ff.
    invc H0.
    + (* t1 term_sub case *)
      eapply IHt1.
      2: { eassumption. }
      econstructor; eauto.
    +
      eapply IHt2.
      2: { eassumption. }
      econstructor; eauto.
  -
    invc H; ff.
    invc H0; ff.
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.

    invc H0; ff.

     eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    invc H2.
    invc H1.

     eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.

    invc H0; ff.

    invc H2.
    invc H1.

    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    
     eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.

    invc H0; ff.

    invc H2.
    invc H1.

    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    invc H2.
    invc H1.

    
     eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
  -
        invc H; ff.
    invc H0; ff.
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.

    invc H0; ff.

     eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    invc H2.
    invc H1.

     eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.

    invc H0; ff.

    invc H2.
    invc H1.

    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    
     eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.

    invc H0; ff.

    invc H2.
    invc H1.

    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    invc H2.
    invc H1.

    
     eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
Qed.

Lemma nullify_no_none_nones_par: forall t t' t1 t2 sp,
    nullify_branchesP t t' ->
    term_sub (bpar sp t1 t2) t' ->
    sp = (ALL,ALL).
Proof.
    intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a; ff; invc H; ff.
  -
    invc H; ff.
    invc H0.
    
    eapply IHt.
    2: { eassumption. }
    econstructor.
    eauto.
  -
    invc H; ff.
    invc H0.
    + (* t1 term_sub case *)
      eapply IHt1.
      2: { eassumption. }
      econstructor; eauto.
    +
      eapply IHt2.
      2: { eassumption. }
      econstructor; eauto.
  -
    invc H; ff.
    invc H0; ff.
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.

    invc H0; ff.

     eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    invc H2.
    invc H1.

     eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.

    invc H0; ff.

    invc H2.
    invc H1.

    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    
     eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.

    invc H0; ff.

    invc H2.
    invc H1.

    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    invc H2.
    invc H1.

    
     eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
  -
        invc H; ff.
    invc H0; ff.
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.

    invc H0; ff.

     eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    invc H2.
    invc H1.

     eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.

    invc H0; ff.

    invc H2.
    invc H1.

    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    
     eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.

    invc H0; ff.

    invc H2.
    invc H1.

    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    invc H2.
    invc H1.

    
     eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
Qed.

Lemma nullify_no_none_seq_contra: forall t t' t1 t2 sp1 sp2,
  nullify_branchesP t t' ->
  term_sub (bseq (sp1,sp2) t1 t2) t' ->
  ((sp1 = NONE) \/ (sp2 = NONE)) ->
  False.
Proof.
  intros.
  invc H1.
  -
    assert ((NONE,sp2) = (ALL,ALL)).
    {
      eapply nullify_no_none_nones_seq; eauto.
    }
    invc H1.
  -
    assert ((sp1,NONE) = (ALL,ALL)).
    {
      eapply nullify_no_none_nones_seq; eauto.
    }
    invc H1.
Qed.

Lemma nullify_no_none_par_contra: forall t t' t1 t2 sp1 sp2,
  nullify_branchesP t t' ->
  term_sub (bpar (sp1,sp2) t1 t2) t' ->
  ((sp1 = NONE) \/ (sp2 = NONE)) ->
  False.
Proof.
  intros.
  invc H1.
  -
    assert ((NONE,sp2) = (ALL,ALL)).
    {
      eapply nullify_no_none_nones_par; eauto.
    }
    invc H1.
  -
    assert ((sp1,NONE) = (ALL,ALL)).
    {
      eapply nullify_no_none_nones_par; eauto.
    }
    invc H1.
Qed.
*)
    
    
                                   

  


(*
(** This function annotates a term.  It feeds a natural number
    throughout the computation so as to ensure each event has a unique
    natural number. *) *)

Fixpoint anno (t: Term) (i:nat) : (nat * AnnoTerm) :=
  match t with
  | asp x => (S i, (aasp (i, S i) x))

  | att p x =>
    let '(j,a) := anno x (S i)  in
    (S j, aatt (i, S j) p a)

  | lseq x y =>
    let '(j,a) := anno x i in
    let '(k,bt) := anno y j in
    (k, alseq (i, k) a bt)

  | bseq s x y =>
    let '(j,a) := anno x (S i) in
    let '(k,b) := anno y j in
    (S k, abseq (i, S k) s a b)

  | bpar s x y =>
    let '(j,a) := anno x (S i) in
    let '(k,b) := anno y j in
    (S k, abpar (i, S k) s a b)
  end.

Definition annotated x :=
  snd (anno x 0).

Fixpoint unanno a :=
  match a with
  | aasp _ a => asp a
  | aatt _ p t => att p (unanno t)
  | alseq _ a1 a2 => lseq (unanno a1) (unanno a2)                 
  | abseq _ spl a1 a2 => bseq spl (unanno a1) (unanno a2) 
  | abpar _ spl a1 a2 => bpar spl (unanno a1) (unanno a2)
  end.

Lemma anno_unanno: forall t i,
    unanno (snd (anno t i)) = t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a; ff.
  -
    ff.
    erewrite <- IHt.
    jkjke.
  -
    ff.
    erewrite <- IHt1.
    erewrite <- IHt2.
    jkjke.
    jkjke.
  -
    ff.
    erewrite <- IHt1.
    erewrite <- IHt2.
    jkjke.
    jkjke.
  -
    ff.
    erewrite <- IHt1.
    erewrite <- IHt2.
    jkjke.
    jkjke.
Defined.


(*

Lemma anno_unanno_par: forall a l l' annt,
    anno_par a l = (l', annt) ->
    unannoPar annt = a.
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros.
  -
    ff.
  -
    ff.
  -
    ff.
    assert (unannoPar a = a1) by eauto.
    assert (unannoPar a0 = a2) by eauto.
    congruence.
  -
    ff.
    assert (unannoPar a = a1) by eauto.
    assert (unannoPar a0 = a2) by eauto.
    congruence.
  -
    ff.
    assert (unannoPar a = a1) by eauto.
    congruence.
Defined.

Lemma anno_unanno_par_list': forall a l l' annt,
    anno_par_list' a l = Some (l', annt) ->
    unannoPar annt = a.
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros.
  -
    ff.
  -
    ff.
  -
    ff.
    unfold bind in *.
    unfold ret in *.
    ff.
    assert (unannoPar a = a1) by eauto.
    assert (unannoPar a0 = a2) by eauto.
    congruence.
  -
    ff.
    unfold bind in *.
    unfold ret in *.
    ff.
    assert (unannoPar a = a1) by eauto.
    assert (unannoPar a0 = a2) by eauto.
    congruence.
  -
    ff.
    unfold bind in *.
    unfold ret in *.
    ff.
    assert (unannoPar a = a1) by eauto.
    congruence.
Defined.

Lemma anno_unanno_par_list: forall a l annt,
    anno_par_list a l = Some annt ->
    unannoPar annt = a.
Proof.
  intros.
  unfold anno_par_list in *.
  unfold bind in *.
  unfold ret in *.
  ff.
  eapply anno_unanno_par_list'.
  eassumption.
Defined.
*)


Inductive annoP: AnnoTerm -> Term -> Prop :=
| annoP_c: forall anno_term t,
    (exists n n', anno t n = (n',anno_term)) -> (* anno_term = snd (anno t n)) -> *)
    annoP anno_term t.

Inductive annoP_indexed': AnnoTerm -> Term -> nat -> Prop :=
| annoP_c_i': forall anno_term t n,
    (exists n', anno t n = (n', anno_term)) -> (*anno_term = snd (anno t n) -> *)
    annoP_indexed' anno_term t n.

Inductive annoP_indexed: AnnoTerm -> Term -> nat -> nat ->  Prop :=
| annoP_c_i: forall anno_term t n n',
    (*(exists n', anno t n = (n', anno_term)) -> (*anno_term = snd (anno t n) -> *) *)
    anno t n = (n', anno_term) ->
    annoP_indexed anno_term t n n'.



(*
Inductive anno_parP (*anno_par_listP*): AnnoTermPar -> Term -> Prop :=
| anno_parP_c: forall par_term t,
    (exists ls ls', anno_par_list' t ls = Some (ls', par_term)) -> (*par_term = snd (anno_par t loc)) -> *)
    (*anno_par_listP*) anno_parP par_term t.

Inductive anno_parPloc: AnnoTermPar -> Term -> list Loc -> Prop :=
| anno_parP_cloc: forall par_term t ls,
    (exists ls', anno_par_list' t ls = Some (ls', par_term)) -> (*par_term = snd (anno_par t loc) -> *)
    anno_parPloc par_term t ls.
*)


(*
Inductive anno_parP: AnnoTermPar -> Term -> Prop :=
| anno_parP_c: forall par_term t,
    (exists loc loc', anno_par t loc = (loc', par_term)) -> (*par_term = snd (anno_par t loc)) -> *)
    anno_parP par_term t.

Inductive anno_parPloc: AnnoTermPar -> Term -> Loc -> Prop :=
| anno_parP_cloc: forall par_term t loc,
    (exists loc', anno_par t loc = (loc', par_term)) -> (*par_term = snd (anno_par t loc) -> *)
    anno_parPloc par_term t loc.


Inductive anno_par_listP: AnnoTermPar -> Term -> Prop :=
| anno_par_listP_c: forall par_term t,
    (exists ls ls', anno_par_list' t ls = Some (ls', par_term)) -> (*par_term = snd (anno_par t loc)) -> *)
    anno_par_listP par_term t.

Inductive anno_par_listPls: AnnoTermPar -> Term -> list Loc -> Prop :=
| anno_par_listP_cloc: forall par_term t ls,
    (exists ls', anno_par_list' t ls = Some (ls', par_term)) -> (*par_term = snd (anno_par t loc) -> *)
    anno_par_listPls par_term t ls.
*)

(*

Lemma nolist_list_same_annopar: forall t annt,
  anno_parP annt t ->
  anno_par_listP annt t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    invc H.
    destruct_conjs.
    econstructor.
    destruct a; ff; eauto.
  -
    invc H.
    destruct_conjs.
    econstructor.
    ff.
    eauto.
  -
    invc H.
    destruct_conjs.
    ff.
    assert (anno_parP a t1).
    {
      econstructor; eauto.
    }
    find_eapply_hyp_hyp.

    assert (anno_parP a0 t2).
    {
      econstructor; eauto.
    }
    find_eapply_hyp_hyp.

    invc H1; invc H2.
    destruct_conjs.


    (*
    econstructor.
    exists H3. eexists.

    ff.

    unfold bind.
    unfold ret.
    find_rewrite.
    find_rewrite.
    
    repeat eexists.
    ff.
    rewrite H6 in *.
    ff.
    unfold an
    ff.
    eauto.
    ff.
    
    eauto.
  -
    invc H.
    destruct_conjs.
    econstructor.
    eauto.
  - invc H.
    destruct_conjs.
    econstructor.
    eauto.
Defined.
*)

Lemma list_nolist_same_annopar: forall t annt,
  anno_par_listP annt t ->
  anno_parP annt t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    invc H;
    destruct_conjs; econstructor; eauto.
Defined.
    
    
*)    
    


(** This predicate determines if an annotated term is well formed,
    that is if its ranges correctly capture the relations between a
    term and its associated events. *)

(*
Lemma unique_req_events (t:AnnoTerm) : forall p i i0 p1 p2 q q0 t0 t1,
       events t p (req i  loc p1 q  t0) ->
    not (events t p (req i0 loc p2 q0 t1)).
 *)

(** Eval for annotated terms. *)

Fixpoint aeval t p e :=
  match t with
  | aasp _ x => eval (asp x) p e
  | aatt _ q x => aeval x q e
  | alseq _ t1 t2 => aeval t2 p (aeval t1 p e)
  | abseq _ s t1 t2 => ss (aeval t1 p ((splitEv_T_l s e)))
                         (aeval t2 p ((splitEv_T_r s e)))
  | abpar _ s t1 t2 => ss (aeval t1 p ((splitEv_T_l s e)))
                         (aeval t2 p ((splitEv_T_r s e)))
  end.

Lemma eval_aeval:
  forall t p e i,
    eval t p e = aeval (snd (anno t i)) p e.
Proof.
  induction t; intros; simpl; auto;
    repeat expand_let_pairs; simpl;
      try (repeat jkjk; auto;congruence);
      try (repeat jkjk'; auto).
Defined.



Inductive well_formed_r_annt: AnnoTerm -> Prop :=
| wf_asp_r_annt: forall r x,
    snd r = S (fst r) ->
    well_formed_r_annt (aasp r x)
| wf_att_r_annt: forall r p x,
    well_formed_r_annt x ->
    S (fst r) = fst (range x) ->
    snd r = S (snd (range x)) ->
    Nat.pred (snd r) > fst r ->
    well_formed_r_annt (aatt r p x)
                  
| wf_lseq_r_annt: forall r x y,
    well_formed_r_annt x -> well_formed_r_annt y ->
    fst r = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = snd (range y) -> 
    well_formed_r_annt (alseq r x y)               
| wf_bseq_r_annt: forall r s x y,
    well_formed_r_annt x -> well_formed_r_annt y ->
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = S (snd (range y)) ->  
    well_formed_r_annt (abseq r s x y)              
| wf_bpar_r_annt: forall r s x y,
    well_formed_r_annt x -> well_formed_r_annt y ->  
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    (snd r) = S (snd (range y)) ->
    (*fst (range y) > fst (range x) -> *)
    well_formed_r_annt (abpar r s x y).
Hint Constructors well_formed_r_annt : core.

Ltac afa :=
  match goal with   
  | [H : forall _, _, H2: Term, H3: nat |- _] => pose_new_proof (H H2 H3)
  end.

Ltac afa' :=
  match goal with   
  | [H : forall _, _, H2: Term, H3: nat |- _] => pose_new_proof (H H2 (S H3))
  end.

Ltac afa'' :=
  match goal with   
  | [H : forall _, _, H2: Term, H3: nat, H4:nat, H5: AnnoTerm |- _] =>
    pose_new_proof (H H2 (H3)(H4) H5)
  end.

Ltac same_index :=
  match goal with
  | [H: anno ?t _ = (?n, _),
        H': anno ?t _ = (?n', _) |- _] =>
    assert_new_proof_by (n = n') eauto
  end.

Lemma same_anno_range: forall t i a b n n',
    anno t i = (n,a) ->
    anno t i = (n',b) ->
    n = n'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    try destruct a;
    ff.
Defined.
  
Lemma anno_mono : forall (t:Term) (i j:nat) (t':AnnoTerm),
  anno t i = (j,t') ->
  j > i.
Proof.
  induction t; intros; (*i j t' ls b H; *)
    ff;
    repeat find_apply_hyp_hyp;
    lia.
Defined.
Hint Resolve anno_mono : core.

Lemma anno_range:
  forall x i j t',
     anno x i = (j,t') ->
    range (t') = (i, j).
Proof.
  induction x; intros; ff.
Defined.

Ltac haha :=
  let asdff := eapply anno_mono; eauto in
  match goal with
  | [H: anno _ ?x = (?y,_) |- _] => assert_new_proof_by (y > x) (asdff)
  end.

Ltac hehe :=
  match goal with
  | [H: anno ?x ?y = (_,_) |- _] => pose_new_proof (anno_range x y)
  end.

Ltac hehe' :=
  match goal with
  | [x: Term, y:nat |- _] => pose_new_proof (anno_range x (S y))
  end.

Ltac hehe'' :=
  match goal with
  | [x: Term, y:nat |- _] => pose_new_proof (anno_range x y)
  end.

Ltac do_list_empty :=
  match goal with
    [H: length ?ls = 0 |- _] =>
    assert_new_proof_by (ls = []) ltac:(destruct ls; solve_by_inversion)
  end.

Lemma anno_well_formed_r:
  forall t i j t',
    anno t i = (j, t') ->
    well_formed_r_annt t'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      ff.
  -
    ff.
    +
      econstructor.
      eauto.
      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

      simpl.
      assert (n > S i) by (eapply anno_mono; eauto).
      lia.
  -
    ff.
    econstructor.
    eauto.
    eauto.

    simpl.
    erewrite anno_range.
    2: {
        eassumption.
      }
    tauto.

    simpl.
    erewrite anno_range.
    2: {
        eassumption.
      }
    erewrite anno_range.
    2: {
        eassumption.
      }
    tauto.

    simpl.
    erewrite anno_range.
    2: {
        eassumption.
      }
    tauto.
      
  -
    ff.
    econstructor.
    eauto.
    eauto.

     simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

  -
    ff.
    econstructor.
    eauto.
    eauto.

     simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      erewrite anno_range.
      2: {
        eassumption.
      }
      
      tauto.
      
      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.     
Defined.
