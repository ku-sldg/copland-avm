(*  Copland language definition.
    
   -Term(T):  Copland Phrase AST.
*)

Require Import String.

Require Import Appraisal_Defs.
Require Import Term_Defs.
Require Import Anno_Term_Defs.

Module CopParser.

Ltac qinv H := inversion H; subst; clear H.

(* If we have a        (Sign, Hash) *)
Fixpoint checkSign_Hash (bb : (bool * bool)) (t : Term): (bool * bool) :=
    match t with
    | (asp a) =>
        match a with
        | SIG => let (s', h') := bb in if s' then (s', h') else (true, false)
        | HSH => let (s', _) := bb in (s', true)
        | _ => bb
        end
    | (att plc t)            => checkSign_Hash bb t
    | (lseq f sec)            => match (checkSign_Hash bb f) with
                                | (sf,hf) => if sf
                                                then (if hf 
                                                    then (true,true)
                                                    else (checkSign_Hash (sf,hf) sec))
                                                else (checkSign_Hash (sf,hf) sec)
                                end
    | (bseq (sp1,sp2) f sec) => match sp1 with
                                | ALL => match sp2 with
                                        | ALL => (* Check both*)
                                            match (checkSign_Hash bb f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash (sf,hf) sec)
                                            end
                                        | NONE => (* Check only sp1 with above, reset below*)
                                            match (checkSign_Hash bb f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)    => (checkSign_Hash (false,false) sec)
                                            end
                                        end
                                | NONE => match sp2 with
                                        | ALL => (* Check only sp2 with above, reset below*)
                                            match (checkSign_Hash (false,false) f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash bb sec)
                                            end
                                        | NONE => (* reset for both*)
                                            match (checkSign_Hash (false,false) f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash (false,false) sec)
                                            end
                                        end
                                end
    | (bpar (sp1,sp2) f sec) => match sp1 with
                                | ALL => match sp2 with
                                        | ALL => (* Check both*)
                                            match (checkSign_Hash bb f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash (sf,hf) sec)
                                            end
                                        | NONE => (* Check only sp1 with above, reset below*)
                                            match (checkSign_Hash bb f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash (false,false) sec)
                                            end
                                        end
                                | NONE => match sp2 with
                                        | ALL => (* Check only sp2 with above, reset below*)
                                            match (checkSign_Hash (false,false) f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash bb sec)
                                            end
                                        | NONE => (* reset for both*)
                                            match (checkSign_Hash (false,false) f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash (false,false) sec)
                                            end
                                        end
                                end 
    end.

Example csh_test1 : checkSign_Hash (false,false) (lseq (asp SIG) (asp HSH)) = (true,true).
reflexivity. Qed.

Example csh_test2 : 
    checkSign_Hash (false,false) (lseq (asp SIG) (lseq (asp CPY) (asp HSH)))
    = (true,true).
simpl.
reflexivity. Qed.

Inductive ind_check_sh : (bool * bool) -> Term -> (bool * bool) -> Prop :=
| csh_asp_sig_t : forall bs bh, (* true case, sign seen previously, no update *)
                    bs = true -> 
                    bh = false -> 
                    ind_check_sh (true, false) (asp SIG) (true, false)
| csh_asp_sig_f : forall bs bh, (* false case sign not seen previously *)
                    bs = false ->
                    ind_check_sh (bs,bh) (asp SIG) (bs,bh)
| csh_asp_hsh   : forall bh, (* case, sign cannot be seen previously *)
                    ind_check_sh (false, bh) (asp HSH) (false, bh)
| csh_asp_other : forall a bs bh, (* other asp's just pass along *)
                    a <> HSH /\ a <> SIG -> 
                    (* TODO: Technically think we allow (true,true) now, but not reachable? *)
                    ind_check_sh (bs,bh) (asp a) (bs,bh)
| 

Example ind_check_sh1 : ind_check_sh (true, false) (asp SIG) (true, false).
apply (csh_asp_sig_t true false); reflexivity. Qed.

Example ind_check_sh2 : ~ (ind_check_sh (true, false) (asp HSH) (true, true)).
(* we cannot generate a failing program *)
unfold not. intros.
qinv H. Qed.

Example ind_check_sh3 : forall b1 b2, (ind_check_sh (b1, b2) (asp CPY) (b1,b2)).
constructor.
split; intros H; discriminate.
Qed.

    match t with
    | (asp a) =>
        match a with
        | SIG => let (s', h') := bb in if s' then (s', h') else (true, false)
        | HSH => let (s', _) := bb in (s', true)
        | _ => (false, false)
        end
    | (att plc t)            => checkSign_Hash bb t
    | (lseq f sec)            => match (checkSign_Hash bb f) with
                                | (sf,hf) => if sf
                                                then (if hf 
                                                    then (true,true)
                                                    else (checkSign_Hash (sf,hf) sec))
                                                else (checkSign_Hash (sf,hf) sec)
                                end
    | (bseq (sp1,sp2) f sec) => match sp1 with
                                | ALL => match sp2 with
                                        | ALL => (* Check both*)
                                            match (checkSign_Hash bb f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash (sf,hf) sec)
                                            end
                                        | NONE => (* Check only sp1 with above, reset below*)
                                            match (checkSign_Hash bb f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)    => (checkSign_Hash (false,false) sec)
                                            end
                                        end
                                | NONE => match sp2 with
                                        | ALL => (* Check only sp2 with above, reset below*)
                                            match (checkSign_Hash (false,false) f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash bb sec)
                                            end
                                        | NONE => (* reset for both*)
                                            match (checkSign_Hash (false,false) f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash (false,false) sec)
                                            end
                                        end
                                end
    | (bpar (sp1,sp2) f sec) => match sp1 with
                                | ALL => match sp2 with
                                        | ALL => (* Check both*)
                                            match (checkSign_Hash bb f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash (sf,hf) sec)
                                            end
                                        | NONE => (* Check only sp1 with above, reset below*)
                                            match (checkSign_Hash bb f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash (false,false) sec)
                                            end
                                        end
                                | NONE => match sp2 with
                                        | ALL => (* Check only sp2 with above, reset below*)
                                            match (checkSign_Hash (false,false) f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash bb sec)
                                            end
                                        | NONE => (* reset for both*)
                                            match (checkSign_Hash (false,false) f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash (false,false) sec)
                                            end
                                        end
                                end 
    end.

Inductive Option {X : Type} : Type :=
| Some {X} (n : X)
| None.

Definition sign_hash_TypeCheck (t : Term) : @Option Term :=
    match (checkSign_Hash (false,false) t) with
    | (true, true)  => None
    | (_,_)         => Some t
    end.

Example shTC1 : sign_hash_TypeCheck (lseq (asp SIG) (asp HSH)) = None.
Proof. reflexivity. Qed.

Example shTC2 : sign_hash_TypeCheck (lseq (asp HSH) (asp SIG)) = Some (lseq (asp HSH) (asp SIG)).
reflexivity. Qed.

Lemma none_not_some : forall (t : Term),
    @None Term = Some t -> False.
Proof.
    intros. discriminate.
Qed.

Lemma checkSH_lseq : forall (t1 t2 : Term) b0 b1,
    ((checkSign_Hash (false,false) t1) = (b0,b1) -> (b0 = true /\ b1 = true) -> (checkSign_Hash (false, false) (lseq t1 t2) = (true,true))) 
    /\
    ((checkSign_Hash (false,false) t1) = (b0,b1) -> (b0 <> true \/ b1 <> true) -> (checkSign_Hash (false, false) (lseq t1 t2) = (checkSign_Hash (b0, b1) t2))).
Proof.
    split; intros.
    * destruct H0; subst. simpl. rewrite H. reflexivity.
    * destruct H0.
        ** simpl. apply Bool.not_true_is_false in H0. subst. rewrite H. reflexivity.
        ** simpl. apply Bool.not_true_is_false in H0. 
            subst. rewrite H.
            destruct b0; reflexivity.
Qed.

Lemma T_impl_P : forall (P : Prop),
    (True -> P) -> P.
Proof.
    intros.
    apply H. apply I.
Qed.

Lemma att_injective_SH : forall p t,
    sign_hash_TypeCheck (att p t) = Some (att p t) ->
    sign_hash_TypeCheck t = Some t.
Proof.
    unfold sign_hash_TypeCheck.
    intros.
    induction t; simpl in *.
    - induction a; reflexivity.
    - destruct (checkSign_Hash (false,false) t).
        destruct b,b0; simpl in *; try discriminate; try reflexivity.
    - destruct (checkSign_Hash (false,false) t1) eqn:T1.
        destruct (checkSign_Hash (false,false) t2) eqn:T2.
        destruct b,b0,b1,b2; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.

        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
    - destruct (checkSign_Hash (false,false) t1) eqn:T1.
        destruct (checkSign_Hash (false,false) t2) eqn:T2.
        destruct b,b0,b1,b2; simpl in *; destruct s as [s1 s2]; destruct s1, s2; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.

        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
    - destruct (checkSign_Hash (false,false) t1) eqn:T1.
        destruct (checkSign_Hash (false,false) t2) eqn:T2.
        destruct b,b0,b1,b2; simpl in *; destruct s as [s1 s2]; destruct s1, s2; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.

        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
Qed.

Lemma termsub_refl : forall t t',
    t = t' ->
    term_sub t t' <-> term_sub t' t.
Proof.
    split; intros; subst; assumption.
Qed. 

Lemma att_term_sub_bijection : forall t t' p,
    (att p t) <> t' ->
    term_sub t' t <-> term_sub t' (att p t).
Proof.
    split; intros.
    - apply aatt_sub_annt. apply H0.
    - generalize dependent t. induction t'; intros.
        * qinv H0. apply H3.
        * qinv H0.
            ** (* very obviously false, (X ..) cannot be sub of X *)
                (* proving it different story *)
                exfalso. apply H. reflexivity.
            ** apply H3.
        * qinv H0. apply H3.
        * qinv H0. apply H3.
        * qinv H0. apply H3.
Qed.

Theorem checkSH_impl_not_hash_sig_term : forall (t : Term),
    sign_hash_TypeCheck t = Some t ->
    not_hash_sig_term t.
Proof.
    intros t H.
    unfold sign_hash_TypeCheck in H. 
    unfold not_hash_sig_term.
    induction t; simpl in *; unfold not in *.
    - admit.
    - intros t' Ht' Htsub. 
      destruct (checkSign_Hash (false,false) t) eqn:E.
      destruct b,b0; simpl in *; try discriminate.
      * assert (Htemp : @Some Term Term t = Some t). {
          reflexivity.
      } apply (IHt Htemp (att p t)). 
        qinv Htsub.
        ** assumption.
    Restart.
    intros t H.
    induction t; unfold not_hash_sig_term in *; unfold not in *; simpl in *; intros.
    - qinv H1. qinv H0. destruct H1 as [e [H1 [H2 H3]]].
        qinv H1.
    - pose proof (att_injective_SH p t). apply H2 in H. 
        apply (IHt H t').
        * apply H0.
        * pose proof (att_term_sub_bijection t t' p).
            apply H3.
            ** unfold not. intros. (* possible they equal, but violate hash_sig *)
                subst. qinv H0.
                destruct H4 as [e [He1 [He2 He3]]].
                discriminate.
            ** apply H1.
    - 

Theorem not_hash_sig_term_impl_typeCheckPass: 
    forall (t : Term),
        not_hash_sig_term t -> sign_hash_TypeCheck t = Some t.
Proof.
    intros t H.
    unfold not_hash_sig_term in H.
    induction t.
    - (* basic asp *)
        induction a; reflexivity.
    - (* basic att *)
        unfold sign_hash_TypeCheck in *.
        pose proof (none_not_some t) as NTF.
        destruct (checkSign_Hash (false,false) (att p t)) eqn:E;
        destruct (checkSign_Hash (false,false) t) eqn:E'.
        destruct b,b0; try reflexivity.
        destruct b1,b2; simpl in *.
        * exfalso. apply NTF.
            apply IHt.
            intros.
            specialize H with t'.
            unfold not. intros. 
            apply H. apply H0.
            apply aatt_sub_annt. apply H1.
        * rewrite E in E'. discriminate.
        * rewrite E in E'. discriminate.
        * rewrite E in E'. discriminate.
    - (* lseq t1 t2*)
        unfold sign_hash_TypeCheck in *.
        destruct (checkSign_Hash (false,false) t1) eqn:Et1.
        destruct (checkSign_Hash (false,false) t2) eqn:Et2.
        (* We should be able to construct Lt1t2 from previous *)
        (* destruct (checkSign_Hash (false,false) (lseq t1 t2)) eqn:Lt1t2. *)
        (* destruct b3,b4; try reflexivity. *)
        destruct b,b0; destruct b1,b2; try (
            (* kill t1 cases *)
            exfalso;
            apply (none_not_some (t1));
            apply IHt1; intros;
            specialize H with t';
            unfold not; intros;
            apply H; [apply H0 | apply alseq_subl_annt; apply H1]
        ); try (
            (* kill t2 cases *)
            exfalso;
            apply (none_not_some (t2));
            apply IHt2; intros;
            specialize H with t';
            unfold not; intros;
            apply H; [apply H0 | apply alseq_subr_annt; apply H1]
        ).
        * pose proof (checkSH_lseq t2 t1 true false) as Hsh.
            destruct Hsh as [_ Hsh].
            apply Hsh in Et2.
            ** 
            ** 
        * qinv Lt1t2. rewrite Et1 in H1.
            (* even if we start in true we never see HSH to double true *)
            admit.
        * qinv Lt1t2. rewrite Et1 in H1.
            (* this is very tricky, seems like it should truly be false *)
            admit.
        * qinv Lt1t2. rewrite Et1 in H1.
            (* never see HSH *)
            admit.
        * qinv Lt1t2. rewrite Et1 in H1.
            (* tricky case, seems like should fail *)
            admit.
        * rewrite <- Et1 in Et2. qinv Lt1t2.
            rewrite Et1 in H1.
            admit.


        (* either works *)
        * exfalso. 
            apply (none_not_some (t2)).
            apply IHt2. unfold not. intros.
            specialize H with t'.
            apply H.
            ** apply H0.
            ** apply alseq_subr_annt. apply H1.
        (* only t1 works *)
        * exfalso. 
            apply (none_not_some (t1)).
            apply IHt1. intros.
            specialize H with t'.
            unfold not. intros.
            apply H.
            ** apply H0.
            ** apply alseq_subl_annt. apply H1.
        (* only t1 works *)
        * exfalso. 
            apply (none_not_some (t1)).
            apply IHt1. intros.
            specialize H with t'.
            unfold not. intros.
            apply H.
            ** apply H0.
            ** apply alseq_subl_annt. apply H1.
        * 

    
Qed.


End CopParser.