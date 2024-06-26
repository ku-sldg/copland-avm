Require Export String ResultT.
Open Scope string_scope.

Class Serializable (A : Type) :=
  {
    to_string : A -> string;
    from_string : string -> ResultT A string;
  }.

Global Instance Serializable_string : Serializable string :=
  {
    to_string := fun s => s;
    from_string := fun s => resultC s;
  }.

Global Instance Serializable_bool : Serializable bool :=
  {
    to_string := fun b => if b then "true" else "false";
    from_string := fun s => 
                     match s with
                     | "true" => resultC true
                     | "false" => resultC false
                     | _ => errC "Not a boolean"
                     end;
  }.

Close Scope string_scope.
