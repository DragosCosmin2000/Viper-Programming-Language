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
Add LoadPath "bool_expressions_folder".
Require Import Bexp.

(* ---------- Vectors Methods ---------- *)
Add LoadPath "vectors_methods_folder".
Require Import vectors_methods.

(* -------------------- Comments -------------------- *)
Inductive comment : Set :=
| comm : string -> comment.

Notation "/* A */" := (comm A) (at level 99).

(* -------------------- Statements -------------------- *)
Inductive Statement :=
(* vectors methods *)
| push : variable -> Array -> Statement
| pop : variable -> Statement
| insert : variable -> val_expression -> val_expression -> Statement
| remove : variable -> val_expression -> Statement
(* comm *)
| empty_stmt : comment -> Statement
(* assignment *)
| assignment : variable -> val_expression -> Statement
| sequence : Statement -> Statement -> Statement
(* conditional statements *)
| ifthen : boolean_expression -> Statement -> Statement
| ifthenelse : boolean_expression -> Statement -> Statement -> Statement
(* repetition statements *)
| while : boolean_expression -> Statement -> Statement
| do_while : Statement -> boolean_expression -> Statement
| forloop : boolean_expression -> Statement -> Statement -> Statement
| forloop_firstloop : Statement -> boolean_expression -> Statement -> Statement -> Statement.

Notation "A 'push'(' B ')'" := (push A B) (at level 1).
Notation "A '.pop'()'" := (pop A) (at level 1).
Notation "A '.insert'(' B , C ')'" := (insert A B C) (at level 1).
Notation "A '.remove'(' B ')'" := (remove_arr A B) (at level 1).

Coercion empty_stmt : comment >-> Statement.

Notation "X ::= A" := (assignment X A) (at level 90).
Notation "S ;' S'" := (sequence S S') (at level 97, right associativity).

Notation "'if*' A 'then*' '{' B '}'" := (ifthen A B) (at level 95).
Notation "'if'' A 'then'' '{' B '}' 'else'' '{' C '}'" := (ifthenelse A B C) (at level 95).

Notation "'while'' A 'do'' '{' B '}'" := (while A B) (at level 95).
Notation "'do*' '{' A '}' 'while*' B" := (do_while A B) (at level 95).

Notation "'for'' A ; B 'do'' '{' C '}'" := (forloop A B C) (at level 95).
Notation "'for*' A ; B ; C 'do*' '{' D '}'" := (forloop_firstloop A B C D) (at level 95).