Require Import Arith.
Require Import Ascii.
Require Import Coq.Strings.Byte.
Require Import String.
Local Open Scope string_scope.

(* -------------------- Datatypes for VPL -------------------- *)
Add LoadPath "datatypes_folder".
Require Import datatypes.

(* ---------- Syntax for variables ---------- *)
Inductive variable : Set :=
| var_name : string -> variable.

Coercion var_name : string >-> variable.

(* ---------- Equality between vars ---------- *)
Definition vars_eq (var1 var2 : variable) : bool :=
  match var1, var2 with
  | var_name name1, var_name name2 => if (eqb name1 name2)
                                      then true
                                      else false
  end.

(* ---------- Check a datatype ---------- *)
Inductive all_types :=
| var_t : variable -> all_types
| val_t : Val -> all_types
| array_t : Array -> all_types
| tuple_t : Tuple -> all_types
| dict_t : Dict -> all_types.

Coercion var_t : variable >-> all_types.
Coercion val_t : Val >-> all_types.
Coercion array_t : Array >-> all_types.
Coercion tuple_t : Tuple >-> all_types.
Coercion dict_t : Dict >-> all_types.

(* ---------- Define environments ---------- *)
Definition Env := variable -> all_types.

(* ---------- Update environment ---------- *)
Definition update (env : Env) (var : variable) (value : all_types) : Env :=
  fun var' => if (vars_eq var' var)
              then value
              else (env var').

(* ---------- To get the datatype ---------- *)
Definition typeof_auxiliar (x : all_types) : string :=
  match x with
  | var_t x' => "var"
  | val_t x' => match x' with
              | error => "error"
              | positive x'' => "natural"
              | negative x'' => "integer"
              | boolean x'' => "boolean"
              | char x'' => "character"
              end
  | array_t x' => "array"
  | tuple_t x' => "tuple"
  | dict_t x' => "dict"
  end.

Definition typeof (x : all_types) (env : Env) : string :=
  match x with
  | var_t x' => (typeof_auxiliar (env x'))
  | val_t x' => match x' with
              | error => "error"
              | positive x'' => "natural"
              | negative x'' => "integer"
              | boolean x'' => "boolean"
              | char x'' => "character"
              end
  | array_t x' => "array"
  | tuple_t x' => "tuple"
  | dict_t x' => "dict"
  end.

Notation "'typeof$(' A $; B '$)'" := (typeof A B) (at level 1).