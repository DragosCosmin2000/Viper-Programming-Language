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
    (* Object doesn't change *)
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

  (* .append() *)

Fixpoint append_arr (col1 col2 : Array) : Array :=
  match col1 with
  | array_nil => col2
  | array_el val => array_cons (array_el val) col2
  | array_cons arr' arr'' => array_cons arr' (append_arr arr'' col2)
  end.

Fixpoint append_tup (col1 col2 : Tuple) : Tuple :=
  match col1 with
  | tuple_nil => col2
  | tuple_el val => tuple_cons (tuple_el val) col2
  | tuple_cons tup' tup'' => tuple_cons tup' (append_tup tup'' col2)
  end.

  (* get() *)
Fixpoint get_arr (col1 : Array) (poz current_poz : nat) : Array :=
  match col1 with
  | array_nil => error
  | array_el val => if Nat.eqb current_poz poz
                    then array_el val
                    else error
  | array_cons val' val'' => if Nat.eqb current_poz poz
                             then val'
                             else get_arr val'' poz (current_poz + 1)
  end.

    (* Object changes *)
  (* push() *)

(* el - array type -> can be any val because of "array_el" *)
Fixpoint push_arr (col1 : Array) (el : Array) : Array :=
  match col1 with
  | array_nil => array_cons el array_nil
  | array_el val => array_cons val (array_cons el array_nil)
  | array_cons val' val'' => array_cons val' (push_arr val'' el)
  end.

  (* pop() *)

Fixpoint pop_arr (col1 : Array) : Array :=
  match col1 with
  | array_nil => array_nil
  | array_el val => array_nil
  | array_cons val' array_nil => array_nil
  | array_cons val' val'' => array_cons val' (pop_arr val'')
  end.

  (* insert() *)
Fixpoint insert_arr (col1 : Array) (el : Array) (poz current_poz : nat) : Array :=
  match col1 with
  | array_nil => if Nat.eqb current_poz poz
                 then array_cons el array_nil
                 else error
  | array_el val => if Nat.eqb current_poz poz
                    then array_cons el (array_cons val array_nil)
                    else if Nat.ltb poz (current_poz + 1)
                         then error
                         else array_cons val (array_cons el array_nil)
  | array_cons val' val'' => if Nat.eqb current_poz poz
                             then array_cons el (array_cons val' val'')
                             else if Nat.ltb poz (current_poz + 1)
                                  then error
                                  else array_cons val' (insert_arr val'' el poz (current_poz + 1))
  end.

Definition my_and (b1 b2 : bool) : bool :=
  match b1, b2 with
  | true, true => true
  | _, _ => false
  end.

  (* remove() *)
Fixpoint remove_arr (col1 : Array) (poz current_poz : nat) : Array :=
  match col1 with
  | array_nil => error
  | array_el val => if Nat.eqb current_poz poz
                    then array_nil
                    else error
  | array_cons val' array_nil => if Nat.eqb current_poz poz
                                 then array_nil
                                 else error
  | array_cons val' (array_el val'') => if Nat.eqb current_poz poz
                                        then array_el val''
                                        else if Nat.eqb (current_poz + 1) poz
                                             then array_cons val' array_nil
                                             else error
  | array_cons val' (array_cons val'' val''') => if my_and (Nat.ltb ((count_arr col1) - 1) poz) (Nat.eqb current_poz 0)
                                                 then error
                                                 else  if Nat.eqb current_poz poz
                                                       then array_cons val'' val'''
                                                       else if Nat.eqb poz (current_poz + 1)
                                                            then array_cons val' val'''
                                                            else array_cons val' (array_cons val'' (remove_arr val''' poz (current_poz + 2)))
  end.

    (* string methods *)
  (* slice *)

Fixpoint slice_arr (col1 : Array) (abegin aend current_poz : nat) : Array :=
  match col1 with
  | array_nil => array_nil
  | array_el val => array_el val
  | array_cons val' val'' => if my_and (Nat.ltb abegin (current_poz + 1)) (Nat.ltb current_poz (aend + 1))
                             then array_cons val' (slice_arr val'' abegin aend (current_poz + 1))
                             else slice_arr val'' abegin aend (current_poz + 1)
  end.

