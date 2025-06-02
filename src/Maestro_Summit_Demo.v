Require Import Term_Defs Flexible_Mechanisms_Vars JSON_Type.

Require Import Demo_Terms CDS_Demo Rodeo_Demo Rodeo_Demo_NoArgs.
Require Import List String.
Import ListNotations.

Definition attest_term : Term :=
  (asp (ASPC (asp_paramsC attest (JSON_Object []) P0 sys_targ))).
  
Definition attest_term_P1 : Term :=
  (asp (ASPC (asp_paramsC attest (JSON_Object []) P1 sys_targ))).

Definition attest_term_P2 : Term :=
  (asp (ASPC (asp_paramsC attest (JSON_Object []) P2 sys_targ))).

Open Scope cop_ent_scope.
Definition example_appTerm : Term :=
<{
    ( meas_cds ) ->
    appr_term
}>.

Definition attest_term_remote : Term :=
  <{
    @P1 [attest_term_P1]
  }>.

Definition attest_term_remote_multinode : Term :=
  <{
    @P1 [attest_term_P1] +<+
    @P2 [attest_term_P2]
  }>.
Close Scope cop_ent_scope.


Open Scope string_scope.
Definition maestro_demo_terms_map : list (string * Term) := 
  [("attest", attest_term);
   ("attest_remote", attest_term_remote);
   ("attest_remote_multinode", attest_term_remote_multinode)].
Close Scope string_scope.