Require Import Term_Defs_Core Eqb_EvidenceT EqClass.

Require Import List.
Import List.ListNotations.

Inductive GenNN: Set :=
| wc_nn: GenNN
| real_nn: N_ID -> GenNN.

Inductive GenPlc: Set :=
| wc_plc: GenPlc
| real_plc: Plc -> GenPlc.

Inductive GenFwd: Set :=
| wc_fwd: GenFwd
| real_fwd: FWD -> GenFwd.

Inductive GenAspId: Set :=
| wc_aspid: GenAspId
| real_aspid: ASP_ID -> GenAspId.

Inductive GenTargId: Set :=
| wc_targid: GenTargId
| real_targid: TARG_ID -> GenTargId.

Inductive GenListArgs: Set :=
| wc_listargs: GenListArgs
| real_listargs: (list Arg) -> GenListArgs.

Inductive GenAspParams: Set :=
| wc_params: GenAspId -> GenListArgs -> GenPlc -> GenTargId -> GenAspParams.



Inductive GenEvidenceT: Set :=
| gen_wc: GenEvidenceT
| gen_mt_evt: GenEvidenceT
| gen_nn: GenNN -> GenEvidenceT
| gen_uu: GenPlc -> GenFwd -> GenAspParams -> GenEvidenceT -> GenEvidenceT
| gen_ss: GenEvidenceT -> GenEvidenceT -> GenEvidenceT.

Definition nid_matches_gen (genNid:GenNN) (nid:N_ID): bool :=
  match genNid with
  | wc_nonce_evt => true
  | real_nonce_evt nid' => eqb nid nid'
  end.

Definition plc_matches_gen (genPlc:GenPlc) (plc:Plc): bool :=
  match genPlc with
  | wc_plc => true
  | real_plc plc' => eqb plc plc'
  end.

Definition fwd_matches_gen (genFwd:GenFwd) (fwd:FWD): bool :=
  match genFwd with
  | wc_fwd => true
  | real_fwd fwd' => eqb_fwd fwd fwd'
  end.

Definition asp_matches_gen (genAsp:GenAspId) (asp:ASP_ID): bool :=
  match genAsp with
  | wc_aspid => true
  | real_aspid asp' => eqb asp asp'
  end.

Definition targid_matches_gen (gentargid:GenTargId) (targid:TARG_ID): bool :=
  match gentargid with
  | wc_targid => true
  | real_targid targid' => eqb targid targid'
  end.

Definition args_matches_gen (genArgs:GenListArgs) (args:list Arg): bool :=
  match genArgs with
  | wc_listargs => true
  | real_listargs args' => eqb args args'
  end.

Fixpoint andb_list (l:list bool) : bool :=
  match l with
  | nil => true
  | b::l => andb b (andb_list l)
  end.

Definition andb_list_alt (l:list bool) : bool := forallb (fun b => b) l.

Lemma and_list_alt_eq : forall (l:list bool),
    andb_list l = andb_list_alt l.
Proof.
  intros.
  induction l; trivial.
Qed.

Definition params_matches_gen (genParams:GenAspParams) (params:ASP_PARAMS) : bool :=
  match genParams with
  | wc_params genaspid genargs genplc gentargid =>
    match params with
    | asp_paramsC aspid args plc targid => 
      andb_list
              [ (asp_matches_gen genaspid aspid);
                (args_matches_gen genargs args);
                (plc_matches_gen genplc plc);
                (targid_matches_gen gentargid targid) ]
    end
  end.

Fixpoint EvidenceT_matches_gen (genEv:GenEvidenceT) (ev:EvidenceT) : bool :=
  match genEv with
  | gen_wc => true
  | gen_mt_evt=>
    match ev with
    | mt_evt=> true
    | _ => false
    end
  | gen_nonce_evt c =>
    match ev with
    | nonce_evt nid => nid_matches_gen c nid
    | _ => false
    end
  | gen_asp_evt genp genfwd genparams genEv' =>
    match ev with
    | asp_evt p fwd params ev' =>
      andb_list [ (plc_matches_gen genp p);
                    (fwd_matches_gen genfwd fwd);
                    (params_matches_gen genparams params);
                    (EvidenceT_matches_gen genEv' ev') ]
    | _ => false
    end
  | gen_split_evt gene1 gene2 =>
    match ev with
    | split_evt e1 e2 =>
      andb_list [ (EvidenceT_matches_gen gene1 e1);
                (EvidenceT_matches_gen gene2 e2) ]
    | _ => false
    end

  end.

Definition specific_aspid_genEvidenceT (i:ASP_ID): GenEvidenceT :=
  gen_asp_evt wc_plc wc_fwd (wc_params (real_aspid i) wc_listargs wc_plc wc_targid) gen_wc.
        
