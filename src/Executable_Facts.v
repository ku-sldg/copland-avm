Require Import Term_Defs_Core Manifest Manifest_Generator (* Manifest_Generator_Facts *) Executable_Defs_Prop Manifest_Admits Eqb_Evidence.

Require Import Params_Admits.
Require Import List.
Import ListNotations.

(*
Definition Environment := Plc -> option Manifest.
*)


(********************
  *   EXECUTABLE 
  ********************)

(** Static guarentee that states: 
  * Is term [t] exectuable on the    
  * attestation manager named [k] in
  * environment [e]?  
  * Are ASPs available at the right attesation managers
  * and are necessary communications allowed?
  *)

(*
Print Manifest. 
Print Environment.
*)

Definition canRunAsp_Env (k:Plc) (em:EnvironmentM) (ps: ASP_PARAMS) : Prop := 
  match (Maps.map_get em k) with 
  | None => False 
  | Some m => canRunAsp_Manifest m ps
  end. 
  
Definition canRun_aspid_Env (k:Plc) (em:EnvironmentM) (i:ASP_ID) : Prop :=
  match (Maps.map_get em k) with 
  | None => False 
  | Some m => canRun_aspid m i
  end. 

Definition knowsOf_Env (k:Plc)(em:EnvironmentM)(p:Plc):Prop :=
  match (Maps.map_get em k) with 
  | None => False
  | Some m => In p m.(uuidPlcs)
  end.

Definition knowsPub_Env (k:Plc)(em:EnvironmentM)(p:Plc):Prop :=
    match (Maps.map_get em k) with 
    | None => False
    | Some m => In p m.(pubKeyPlcs)
    end.

(* Statically, we have a global view so we can use the environement to reason about the system *)
Fixpoint executable_static (t:Term) (k:Plc) (em:EnvironmentM) : Prop := 
  match t with
    | asp (ASPC _ _ ps)  => canRunAsp_Env k em ps
    | asp SIG => canRun_aspid_Env k em (sig_aspid)
    | asp HSH => canRun_aspid_Env k em (hsh_aspid)
    | asp (ENC p) => knowsPub_Env k em p
    | asp _ => exists m, Maps.map_get em k = Some m(* asp _ => True *)
    | att p t1 => knowsOf_Env k em p /\ executable_static t1 p em
    | lseq t1 t2 => executable_static t1 k em /\ executable_static t2 k em
    | bseq _ t1 t2 => executable_static t1 k em /\ executable_static t2 k em
    | bpar _ t1 t2 => executable_static t1 k em /\ executable_static t2 k em
  end.

(* A dynamic version of executabiilty. 
   At runtime, we cannot know if an att term can be executed on a remote place. *)
Fixpoint executable_dynamic (t:Term) (k:Plc) (em:EnvironmentM) : Prop := 
  match t with
    (* | asp (ASPC _ _ (asp_paramsC asp_id _ _ _))  => canRunAsp_Env k em asp_id
    | asp _ => True *)
    | asp (ASPC _ _ ps)  => canRunAsp_Env k em ps
    | asp SIG => canRun_aspid_Env k em (sig_aspid)
    | asp HSH => canRun_aspid_Env k em (hsh_aspid)
    | asp (ENC p) => knowsPub_Env k em p
    | asp _ =>  exists m, Maps.map_get em k = Some m (* True *)
    | att p t => knowsOf_Env k em p
    | lseq t1 t2 => executable_dynamic t1 k em /\ executable_dynamic t2 k em
    | bseq _ t1 t2 => executable_dynamic t1 k em /\ executable_dynamic t2 k em
    | bpar _ t1 t2 => executable_dynamic t1 k em /\ executable_dynamic t2 k em
  end.

(*
Definition envs_eq_at (e:Environment) (em:EnvironmentM) (ps:list Plc) : Prop := 
    forall p, 
        In p ps ->
        e p = Maps.map_get em p.
*)

(* Record Manifest : Set := Build_Manifest
                            { my_abstract_plc : Plc;
                              asps : list ASP_ID;
                              uuidPlcs : list Plc;
                              pubKeyPlcs : list Plc;
                              policy : Manifest_Admits.PolicyT }.*)

(* Try to build a manifest. *)

Definition build_manifest_helper p a p1 p2 pol : Manifest := 
{|  my_abstract_plc := p ; 
    asps :=  a ;
    uuidPlcs := p1 ; 
    pubKeyPlcs := p2 ; 
    policy := pol |}. 

Lemma eqb_plc_refl : forall p0, Eqb_Evidence.eqb_plc p0 p0 = true.
Proof.
  intros. apply eqb_eq_plc. auto.
Qed.  

(* Proof that the dynamic notion of executability respects the static notion of executability. *)
Theorem static_executability_implies_dynamic : 
    forall t p em,
      executable_static t p em -> 
      executable_dynamic t p em.
Proof.
  intros t. induction t; try ( intros; inversion H; specialize IHt1 with p em; specialize IHt2 with p em; simpl; split; auto).
  + intros. auto. 
  + intros. specialize IHt with p0 em. simpl in *. inversion H. apply H0.
Qed. 


(*

(* Proof that the distributed notion of executability respects the static notion of executability. *)
Theorem static_executability_implies_distributed : 
    forall t p em,
      executable_static t p em -> 
      distributed_executability t p em.
Proof.
  (*
  intros. unfold distributed_executability. intros; subst.
  induction t.  
  + simpl in *. destruct a.
  ++ simpl in *.   
  
  
  
  
  
  
  auto. destruct a eqn:H'.
  ++ induction em.
  +++ simpl in *; auto. remember (build_manifest_helper p0 [] [] [] empty_PolicyT) as m.
      exists m. split.
  ++++ inversion H1.
  +++++ rewrite H0 in H2. pose proof eqb_plc_refl p0. rewrite H3 in H2. inversion H2.    apply eqb_plc_refl in H2.  Search "eqb_plc".     auto.  
  +++ left.    
  remember (build_manifest_helper p0 [] [] [] empty_PolicyT) as m.

  
  
  inversion H1; simpl in *. 
  
  
  
  
  
  
  inversion H.   remember (build_manifest_helper p0 [] [] [] empty_PolicyT) as m.
     exists m. split.
  +++ simpl in *.      
  
  destruct em eqn:H'.
  ++ split with (x := []).  split with (x := a).
  *)

Abort.

*)