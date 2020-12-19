Require Import Arith.
Require Import Ascii.
Require Import Coq.Strings.Byte.
Require Import String.
Local Open Scope string_scope.

(* -------------------- Datatypes for VPL -------------------- *)
Add LoadPath "datatypes_folder".
Require Import datatypes.

(* -------------------- Variables, Environments, typeof() -------------------- *)
Add LoadPath "variables_folder".
Require Import variables.

(* ---------- Expression Syntax ---------- *)
Inductive val_expression :=
| exp_val : Val -> val_expression
| exp_var : variable -> val_expression
| exp_array : Array -> val_expression
| exp_tuple : Tuple -> val_expression
| exp_plus : val_expression -> val_expression -> val_expression
| exp_sub : val_expression -> val_expression -> val_expression
| exp_mul : val_expression -> val_expression -> val_expression
| exp_div : val_expression -> val_expression -> val_expression
| exp_mod : val_expression -> val_expression -> val_expression
(* to be able to make something like: if typeof(3) == "number" then... *)
| exp_typeof : string -> val_expression.

Coercion exp_val : Val >-> val_expression.
Coercion exp_var : variable >-> val_expression.
Coercion exp_array : Array >-> val_expression.
Coercion exp_tuple : Tuple >-> val_expression.

Notation "A +' B" := (exp_plus A B) (at level 50, left associativity).
Notation "A -' B" := (exp_sub A B) (at level 50, left associativity).
Notation "A *' B" := (exp_mul A B) (at level 40, left associativity).
Notation "A /' B" := (exp_div A B) (at level 40, left associativity).
Notation "A %' B" := (exp_mod A B) (at level 40, left associativity).
Notation "'type#' A" := (exp_typeof A) (at level 1).