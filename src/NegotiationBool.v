(* Functions surrounding Negotiation for DEMO 

   Roughly, code will: 
   1. pass in protocol
   2. ensure protocol is sound and executable 

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

(** [Environment] is a set of AM's each defined by a [Manifest].
  The domain of an [Environment] provides names for each [Manifest].
  Names should be the hash of their public key, but this restriction
  is not enforced here. 
*)

Definition Environment : Type :=  Plc -> (option Manifest).

Definition e_empty : Environment := (fun _ => None).

Print Plc. 

Definition e_update `{H : EqClass ID_Type} (m : Environment) (x : Plc) (v : (option Manifest)) :=
  fun x' => if eqb x x' then v else m x'.

(** A [System] is all attestation managers in the enviornement *)

Definition System := list Environment.

(** ****************************
  * REASONING ABOUT MANIFESTS
*****************************)

(** Within the enviornment [e], does the AM at place [k] have ASP [a]? *)

Search "In". 

Fixpoint Inb `{H : EqClass ID_Type} (a:ASP_ID) (l:list ASP_ID) : bool :=
  match l with
    | [] => false
    | b :: m => orb (eqb b a) (Inb a m)
  end.

Definition hasASPe(k:Plc)(e:Environment)(a:ASP_ID) : bool :=
match (e k) with
| None => false
| Some m => Inb a m.(asps)
end.      

(** Determine if manifest [k] from [e] knows how to 
   communicate from [k] to [p]
*)

Definition knowsOfe `{H: EqClass ID_Type} (k:Plc)(e:Environment)(p:Plc): bool :=
match (e k) with
| None => false
| Some m => Inb p m.(knowsOf)
end.

(** Determine if place [k] within the environment [e]  
    depends on place [p] (the context relation) *)
Definition dependsOne (k:Plc)(e:Environment)(p:Plc): bool  :=
match (e k) with
| None => false
| Some m => Inb p m.(context)
end.

(** ***************************
    * EXECUTABILITY 
*****************************)


(** Is term [t] exectuable on the attestation manager named [k] in 
    environment [e]?  Are ASPs available at the right attesation managers
    and are necessary communications allowed? *)

Print ASP_ID.

Fixpoint executable(t:Term)(k:Plc)(e:Environment): bool :=
match t with
| asp a  => match a with 
            | ASPC _ _ p => match p with 
                            | asp_paramsC aspid _ _ _ => hasASPe k e aspid
                            end
            | NULL => true
            | CPY => true
            | SIG => true
            | HSH => true
            | ENC p => true
            end
| att p t => if knowsOfe k e p then executable t p e else false
| lseq t1 t2 => andb (executable t1 k e) (executable t2 k e)
| bseq _ t1 t2 => andb (executable t1 k e) (executable t2 k e)
| bpar _ t1 t2 => andb (executable t1 k e) (executable t2 k e)
end.

(******************************
*        POLICY
*******************************)

(** Check environment [e] and see if place [p] has some policy 
 *  where the Policy allows p to run a. *)
Definition checkASPPolicy(p:Plc)(e:Environment)(a:ASP_ID):bool :=
match (e p) with (* Look for p in the environment *)
| None => false
| Some m => (policy m a p) (* Policy from m allows p to run a *)
end.

(** Recursive policy check. *)
Fixpoint checkTermPolicy(t:Term)(k:Plc)(e:Environment): bool :=
  match t with
  | asp a  => match a with 
              | ASPC _ _ p => match p with 
                              | asp_paramsC aspid _ _ _ => hasASPe k e aspid
                              end
              | NULL => true
              | CPY => true
              | SIG => true
              | HSH => true
              | ENC p => true
              end
  | att r t0 => checkTermPolicy t0 k e
  | lseq t1 t2 => andb (checkTermPolicy t1 k e) (checkTermPolicy t2 k e)
  | bseq _ t1 t2 => andb (checkTermPolicy t1 k e) (checkTermPolicy t2 k e)
  | bpar _ t1 t2 => andb (checkTermPolicy t1 k e) (checkTermPolicy t2 k e)
  end.

(*****************************
 * SOUND
 *****************************)

(** Soundness is executability and policy adherence *)

Definition sound (t:Term)(k:Plc)(e:Environment) :=
  andb (executable t k e) (checkTermPolicy t k e).

(** ***************************
 * DEMO SYSTEM 
 *****************************)

(* the target should be able to share: 
   1. kim_meas_aspid wiht kim_meas_targid
   2. the cal_ak_aspid with cal_ak_targid 
   3. the public key to bc (?)
   4. data 
   5. tpm signature
   6. ssl encryption *)

   (* might want to care who it discloses evidence to *)
Inductive server_Policy : ASP_ID -> Plc -> Prop := 
| p_kim : server_Policy kim_meas_aspid kim_meas_targid 
| p_cal_ak : server_Policy cal_ak_aspid cal_ak_targid
| p_pub_bc : server_Policy pub_bc_aspid pub_bc_targid
| p_data : server_Policy get_data_aspid get_data_targid
| p_tpm_sig : server_Policy tpm_sig_aspid tpm_sig_targid 
| p_ssl_enc : server_Policy ssl_enc_aspid ssl_enc_targid. 

(* Definition server_Policy_bool : forall a p, reflect (server_Policy a p). *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

(* server can share data with source_plc (client) *)
Definition server_Policy_bool  `{H : EqClass ID_Type} (a: ASP_ID) (p:Plc) : bool := 
    (eqb a kim_meas_aspid && eqb p source_plc) || 
    (eqb a cal_ak_aspid && eqb p source_plc) || 
    (eqb a pub_bc_aspid && eqb p source_plc) || 
    (eqb a get_data_aspid && eqb p source_plc) ||
    (eqb a tpm_sig_aspid && eqb p source_plc) || 
    (eqb a ssl_enc_aspid && eqb p source_plc) .

    (* client can share data with dest_plc (server) *)
Definition client_Policy_bool `{H : EqClass ID_Type} (a: ASP_ID) (p:Plc) : bool := 
 (eqb a store_clientData_aspid && eqb p dest_plc).

(** Definition of environments for use in examples and proofs.  
 * Note there are 2 communicating peer's present... server and client
 * About the demo:  
 ** client is source_plc 
 ** server is dest_plc
 ** client is appraising the server 
 *)

Definition e0 := e_empty.
Definition e_client :=
    e_update e0 source_plc (Some {| asps := [store_clientData_aspid]; knowsOf:= [dest_plc] ; context := [] ; policy := client_Policy_bool |}).
Definition e_server :=
    e_update e0 dest_plc (Some {| asps := [kim_meas_aspid;  cal_ak_aspid; pub_bc_aspid; get_data_aspid; tpm_sig_aspid; ssl_enc_aspid]; knowsOf:= [] ; context := [] ; policy := server_Policy_bool|}).

(** In our example, the system includes client and server *)

Definition example_sys_1 := [ e_client; e_server]. 

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
  
(** Prove the P0 knows of P1 in P0's enviornment *)

Example ex1 : knowsOfe source_plc e_client dest_plc = true.
Proof.
  cbv.
  eqbr source_plc.
  eqbr dest_plc.
  eauto.
Qed.

(** Prove server can share kim_meas (the demo phrase) with the client. 
    AKA that it satisfies policy *)

Theorem kim_meas_policy : server_Policy_bool kim_meas_aspid source_plc = true.
Proof.
  cbv. 
  eqbr kim_meas_aspid.
  eqbr source_plc.
  auto. 
Qed.


(* Remove all other theorems for now.... *)

(* Steps for negotiation 
   1. pass in protocol 
   2. check executability and soundness
   3. return protocol if passes check *)

Print sound. 

(* Negotiate' 
   * input : t is list of requested terms 
             r is list of proposed terms 
   * output : list of proposed terms 
   * reasoning: check if requested term satisfies soundness
                the soundness check is done  *)

Fixpoint negotiate' (t: list Term ) (r: list Term): list Term := 
  match t with 
  | [] => r
  | h :: tl => if sound h dest_plc e_server then negotiate' tl ([h] ++ r) else negotiate' tl r 
  end.


(* Negotiate. 
   * input: list of terms. This is the request. 
   * output : list of terms. This is the proposal. 
   * reasoning: pass input to helper function negotiate 
       to call soundness check with empty list as proposal *)  
Definition negotiate (t:list Term) : list Term := 
  negotiate' t []. 

(* demo phrase currently is a kim measurement *)
Definition demo_phrase := kim_meas.

Theorem negotiate_demo : negotiate [demo_phrase] = [kim_meas].
Proof.
  cbv. 
  eqbr dest_plc.
  eqbr kim_meas_aspid.
  auto.
Qed. 

Definition selection (t : list Term) : option Term := 
match t with 
| [] => None 
| h :: tl => Some h 
end. 