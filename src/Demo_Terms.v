Require Import Term_Defs JSON.

Require Import String.
Require Import List.
Import ListNotations.


Open Scope string_scope.

Definition gather_file_contents : ASP_ID := "readfile".
Definition hash_file_contents : ASP_ID := "hashfile".
Definition hash_dir_contents : ASP_ID := "hashdir".
Definition hash_evidence : ASP_ID := "hashevidence".
Definition provision : ASP_ID := "provision".

Definition gather_targ_asp (targPlc:Plc) (targId:TARG_ID) 
    (env_var:string) (env_var_golden:string) 
    (path:string) (path_golden:string) : Term := 
    (asp (ASPC (asp_paramsC 
                    gather_file_contents 
                    (JSON_Object [
                     ("env_var", (JSON_String env_var));
                     ("filepath", (JSON_String path)); 
                     ("env_var_golden", (JSON_String env_var_golden));
                     ("filepath_golden", (JSON_String path_golden))])
                    targPlc 
                    targId ))).

Definition hash_targ_asp (targPlc:Plc) (targId:TARG_ID) 
(env_var:string) (env_var_golden:string) 
(path:string) (path_golden:string) : Term := 
(asp (ASPC (asp_paramsC 
                hash_file_contents 
                (JSON_Object [
                    ("env_var", (JSON_String env_var));
                    ("filepath", (JSON_String path)); 
                    ("env_var_golden", (JSON_String env_var_golden));
                    ("filepath_golden", (JSON_String path_golden))])
                targPlc 
                targId ))).

Definition string_to_json (s:string) : JSON := JSON_String s.

Definition hash_dir_asp (targPlc:Plc) (targId:TARG_ID) 
    (env_var:string) (env_var_golden:string) (paths:list string) (appr_path:string) : Term := 
    (asp (ASPC (asp_paramsC 
                    hash_dir_contents 
                    (JSON_Object [("env_var", (JSON_String env_var)); 
                                    ("env_var_golden", (JSON_String env_var_golden));
                                    ("paths", (JSON_Array (map string_to_json paths)));
                                    ("filepath_golden", (JSON_String appr_path))])
                    targPlc 
                    targId ))).

Definition provision_targ_asp (targPlc:Plc) (targId:TARG_ID) 
    (env_var:string) (path:string) : Term := 
    (asp (ASPC (asp_paramsC 
                    provision 
                    (JSON_Object [
                        ("env_var", (JSON_String env_var));
                        ("filepath", (JSON_String path))])
                    targPlc 
                    targId ))).

Definition hash_evidence_asp (targPlc:Plc) (targId:TARG_ID)
    (env_var_golden:string) (path_golden:string) : Term := 
    (asp (ASPC (asp_paramsC 
                    hash_evidence 
                        (JSON_Object [
                        ("env_var_golden", (JSON_String env_var_golden));
                        ("filepath_golden", (JSON_String path_golden))])
                    targPlc 
                    targId ))).

Close Scope string_scope.