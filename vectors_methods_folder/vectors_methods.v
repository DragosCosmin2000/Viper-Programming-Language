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

(* ---------- Built-in functions ---------- *)

(* .count() *)

Fixpoint count_arr (col : Array) : nat :=
  match col with
  | array_nil => 0
  | (array_el val) => 1
  | (array_cons arr' arr'') => 1 + count_arr arr''
  end.

Fixpoint count_tup (col : Tuple) : nat :=
  match col with
  | tuple_nil => 0
  | (tuple_el val) => 1
  | (tuple_cons arr' arr'') => 1 + count_tup arr''
  end.

Notation "A '.count()''" := (count_arr A) (at level 1).
Notation "A '.count()'''" := (count_tup A) (at level 1).

Compute (#[ 2, 3, 4, #"a"#]).count()'.
Compute (#( 2, 3, 4, #"a"#)).count()''.

(* .append() *)

Fixpoint append_arr (col1 col2 : Array) : Array :=
  match col1 with
  | array_nil => col2
  | array_el val => array_cons (array_el val) col2
  | array_cons arr' arr'' => array_cons arr' (append_arr arr'' col2)
  end.

Notation "A '.append'(' B ')'" := (append_arr A B) (at level 1).

Compute (#[ 2, 3, 4, #"a"#]).append'((#[ 3, 4, 5, #"b"#])).


