Require Import EqClass.

Definition ASP_Address : Set. Admitted.

Definition UUID : Type. Admitted.

Global Instance Eq_Class_uuid : EqClass UUID. Admitted.

Definition PublicKey : Set. Admitted.

Global Instance Eq_Class_public_key : EqClass PublicKey. Admitted.

Definition PrivateKey : Set. Admitted.

Global Instance Eq_Class_private_key : EqClass PrivateKey. Admitted.

Definition PolicyT : Set. Admitted.
