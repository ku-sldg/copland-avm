(* 
  Negotiation over Manifests (NOT enviornments)
*)

Require Import Manifest. 
Require Import Term.

Require Import String. 
Require Import Coq.Bool.Bool.

Require Import List.
Import ListNotations.
Require Import Params_Admits Term_Defs Eqb_Evidence AbstractedTypes EqClass.
Require Import Example_Phrases_Demo_Admits Example_Phrases_Demo.  

(**** Ltac used *)

Ltac inverts t := inversion t; subst; clear t.
Ltac right_dest_contr H := right; unfold not; intros H; destruct H; contradiction.
Ltac right_intro_inverts := right; unfold not; intros H'; inverts H'.
Ltac right_dest_inverts := right; unfold not; intros H; inverts H.

(** ****************************
  * REASONING ABOUT MANIFESTS
*****************************)

Fixpoint Inb `{H : EqClass ID_Type} (a:ASP_ID) (l:list ASP_ID) : bool :=
  match l with
  | [] => false
  | b :: m => orb (eqb b a) (Inb a m)
  end.
  
(** Within the manifest [m], does the AMß have ASP [a]? *)
Definition hasASPm (m:Manifest) (a:ASP_ID) : bool :=
  Inb a m.(asps).        

(** Determine if manifest [m] knows how to communicate with [k] *)
Definition knowsOfm (m:Manifest) (k:Plc) : bool :=
  Inb k m.(knowsOf).

(** ***************************
    * EXECUTABILITY 
*****************************)


(** Is term [t] exectuable on the attestation manager 
    with the manifest [m]?  Are ASPs available at the 
    right attesation managers and are necessary communications allowed? *)

Print ASP_ID.

Fixpoint executable' (t:Term) (m:Manifest): bool :=
match t with
| asp a  => match a with 
            | ASPC _ _ p => match p with 
                            | asp_paramsC aspid _ _ _ => hasASPm m aspid
                            end
            | NULL => true
            | CPY => true
            | SIG => true
            | HSH => true
            | ENC p => true
            end
| att p t => true
| lseq t1 t2 => andb (executable' t1 m) (executable' t2 m)
| bseq _ t1 t2 => andb (executable' t1 m) (executable' t2 m)
| bpar _ t1 t2 => andb (executable' t1 m) (executable' t2 m)
end.

(* Now, executability with the dispatch opertation...
   The problem is that if we want to check executability 
  on a remote place, we need to somehow have access to that
  place's manifest. Without the enviornment, we have no way 
  of knowing what place belongs to what Manifest. We could
  make manifests place dependent but I'm not sure we want to
  do that...  
  Will says forgo this for now.... *)
Fixpoint executable (t:Term) (m:Manifest): bool :=
match t with
| asp a  => match a with 
            | ASPC _ _ p => match p with 
                            | asp_paramsC aspid _ _ _ => hasASPm m aspid
                            end
            | NULL => true
            | CPY => true
            | SIG => true
            | HSH => true
            | ENC p => true
            end
| att p t1 => if (knowsOfm m p) then true (* executable t1 (p's manifest) *) else false 
| lseq t1 t2 => andb (executable t1 m) (executable t2 m)
| bseq _ t1 t2 => andb (executable t1 m) (executable t2 m)
| bpar _ t1 t2 => andb (executable t1 m) (executable t2 m)
end.

(******************************
*        POLICY
*******************************)

(** Check manifest [m] and see if place [p] can run a. *)
Definition checkMPolicy (p:Plc) (m:Manifest) (a:ASP_ID) : bool := 
  policy m a p.  

(** Recursive policy check. *)
Fixpoint checkTermPolicy(t:Term)(k:Plc)(m:Manifest): bool :=
  match t with
  | asp a  => match a with 
              | ASPC _ _ (asp_paramsC aspid _ _ _ )=> checkMPolicy k m aspid
              | NULL => true
              | CPY => true
              | SIG => true
              | HSH => true
              | ENC p => true
              end
  | att r t0 => checkTermPolicy t0 k m
  | lseq t1 t2 => andb (checkTermPolicy t1 k m) (checkTermPolicy t2 k m)
  | bseq _ t1 t2 => andb (checkTermPolicy t1 k m) (checkTermPolicy t2 k m)
  | bpar _ t1 t2 => andb (checkTermPolicy t1 k m) (checkTermPolicy t2 k m)
  end.

(*****************************
 * SOUND
 *****************************)

(** Soundness is executability and policy adherence *)

Definition sound (t:Term)(m:Manifest) (k:Plc) :=
  andb (executable t m) (checkTermPolicy t k m).

(*****************************
 * NEGOTIATION
 *****************************)

(* Negotiate' 
   * input : t is list of requested terms 
             r is list of proposed terms 
   * output : list of proposed terms 
   * reasoning: check if requested term satisfies soundness
                the soundness check is done  *)

Fixpoint negotiate' (t: list Term ) (r: list Term) (m: Manifest) (tp : Plc): list Term := 
  match t with 
  | [] => r
  | h :: tl => if sound h m tp then negotiate' tl ([h] ++ r) m tp else negotiate' tl r m tp
  end.

(** ***************************
 * DEMO SYSTEM 
 *****************************)

 Definition server_plc := dest_plc.
 Definition client_plc := source_plc.

(* the server should be able to share: 
   1. kim_meas_aspid with client  *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

(* server can share data with source_plc (client) *)
Definition server_Policy_bool  `{H : EqClass ID_Type} (a: ASP_ID) (p:Plc) : bool := 
    (eqb a kim_meas_aspid && eqb p client_plc).

    (* client can share data with dest_plc (server) *)
Definition client_Policy_bool `{H : EqClass ID_Type} (a: ASP_ID) (p:Plc) : bool := 
 (eqb a store_clientData_aspid && eqb p server_plc).

(** Definition of manifest for use in examples and proofs. *)

Definition m_client := ({| asps := [store_clientData_aspid]; knowsOf:= [dest_plc] ; context := [] ; policy := client_Policy_bool |}).
Definition m_server := ({| asps := [kim_meas_aspid;  cal_ak_aspid; pub_bc_aspid; get_data_aspid; tpm_sig_aspid; ssl_enc_aspid]; knowsOf:= [] ; context := [] ; policy := server_Policy_bool|}).

(** ***************************
  * EXAMPLE SYSTEM PROPERTIES
  *****************************)

(** Decidable equality proofs for various Copland datatypes *)
Definition eq_asp_id_dec `{H : EqClass ID_Type} :
forall x y: ASP_ID, {x = y} + {x <> y}.
Proof.
intros.
eapply EqClass_impl_DecEq; eauto.
Defined.


Lemma eqb_refl : forall `{H: EqClass ID_Type} (x:ID_Type), eqb x x = true.
  intros. destruct H. eapply eqb_leibniz. auto.
Qed.    

(* Anytime equality is needed for the admitted type, use this. *)
Ltac eqbr var :=
  let H := fresh "H" in
  assert (H : (let (eqb, _) := Eq_Class_ID_Type in eqb) var
  var = true); [eapply eqb_refl |]; rewrite H.
  
(** Prove client knows of server *)
Example ex1 : knowsOfm m_client server_plc = true.
Proof. 
  cbv.
  eqbr dest_plc.
  eauto.
Qed.

(* demo phrase currently is a kim measurement *)
Definition demo_phrase := kim_meas.
Print kim_meas. (* <{ << kim_meas_aspid dest_plc kim_meas_targid >> }> *)

(** Prove server can share kim_meas (the demo phrase) with the client. 
    AKA that it satisfies policy *)
Theorem kim_meas_policy : server_Policy_bool kim_meas_aspid client_plc = true.
Proof.
  cbv. 
  eqbr kim_meas_aspid.
  eqbr source_plc.
  auto. 
Qed.

Theorem demo_phrase_checkMPolicy : checkMPolicy server_plc m_server kim_meas_aspid = true.
Proof.
  cbv.
  eqbr kim_meas_aspid.