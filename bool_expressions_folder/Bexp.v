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

(* -------------------- Expression Syntax -------------------- *)
Add LoadPath "val_expressions_folder".
Require Import VALexp.

(* ---------- Boolean Expression Syntax ---------- *)
Inductive boolean_expression :=
| bval : bool -> boolean_expression
| bnot : boolean_expression -> boolean_expression
| band : boolean_expression -> boolean_expression -> boolean_expression
| bor : boolean_expression -> boolean_expression -> boolean_expression
| blt : val_expression -> val_expression -> boolean_expression
| blteq : val_expression -> val_expression -> boolean_expression
| beq : val_expression -> val_expression -> boolean_expression
| bgt : val_expression -> val_expression -> boolean_expression
| bgteq : val_expression -> val_expression -> boolean_expression.

Coercion bval : bool >-> boolean_expression.

Notation "!' A" := (bnot A) (at level 75).
Notation "A 'and'' B" := (band A B) (at level 80).
Notation "A 'or'' B" := (bor A B) (at level 80).
Notation "A <' B" := (blt A B) (at level 70).
Notation "A <=' B" := (blteq A B) (at level 70).
Notation "A ==' B" := (beq A B) (at level 70).
Notation "A >' B" := (bgt A B) (at level 70).
Notation "A >=' B" := (bgteq A B) (at level 70).