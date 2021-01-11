Require Import Arith.
Require Import Ascii.
Require Import Coq.Strings.Byte.
Require Import String.
Local Open Scope string_scope.

(* -------------------- Datatypes for VPL -------------------- *)
Inductive Val : Set :=
(* for errors *)
| error : Val
(* int *)
| positive : nat -> Val
| negative : nat -> Val
(* bool *)
| boolean : bool -> Val
(* characters *)
| char : ascii -> Val.

Coercion positive : nat >-> Val.
Coercion boolean : bool >-> Val.
Notation "-# A" := (negative A) (at level 20).
Notation "# A" := (char A) (at level 20).

(* ---------- Collections ---------- *)
Inductive Array : Set :=
(* '\0' *)
| arr_NULL
| array_cons : Val -> Array -> Array.

Notation "#[ #]" := arr_NULL (format "#[ #]", at level 20).
Notation "#[ A #]" := (array_cons A arr_NULL) (at level 20).
Notation "#[ A , B , .. , N #]" := (array_cons A (array_cons B .. (array_cons N arr_NULL)..)) (at level 20).

(* Examples *)
Check #[ #].
Check #[ 1 #].
Check #[ -#22, true, 220, false, #"a" #].
Check #[ #"s", #"a", #"l", #"u", #"t" #].

Inductive Tuple : Set :=
(* '\0' *)
| tup_NULL
| tuple_cons : Val -> Tuple -> Tuple.

Notation "#( #)" := tup_NULL (format "#( #)", at level 20).
Notation "#( A #)" := (tuple_cons A tup_NULL) (at level 20).
Notation "#( A , B , .. , N #)" := (tuple_cons A (tuple_cons B .. (tuple_cons N tup_NULL)..)) (at level 20).

(* Examples *)
Check #( #).
Check #( 1 #).
Check #( -#22, true, 220, false, #"a" #).
Check #( #"s", #"a", #"l", #"u", #"t" #). (* a string *)

Inductive Pair_Element : Set :=
| pair_el_val : Val -> Pair_Element
| pair_el_arr : Array -> Pair_Element
| pair_el_tup : Tuple -> Pair_Element.

Coercion pair_el_val : Val >-> Pair_Element.
Coercion pair_el_arr : Array >-> Pair_Element.
Coercion pair_el_tup : Tuple >-> Pair_Element.

(* Pairs, (key:value) - especially for dicts *)
Inductive Pair : Set :=
| pair : Pair_Element -> Pair_Element -> Pair.

Notation " A : B " := (pair A B) (at level 40).

Inductive Dict : Set :=
(* '\0' *)
| dict_NULL
| dict_cons : Pair -> Dict -> Dict.

Notation "#{ #}" := dict_NULL (format "#{ #}", at level 20).
Notation "#{ A #}" := (dict_cons A dict_NULL) (at level 20).
Notation "#{ A , B , .. , N #}" := (dict_cons A (dict_cons B .. (dict_cons N dict_NULL)..)) (at level 20).

Check #{
  #[ #"D", #"r", #"a", #"g", #"o", #"s" #] : -#9,
  #[ #"A", #"n", #"d", #"r", #"e", #"e", #"a" #] : 9,
  #[ #"R", #"a", #"r", #"e", #"s" #] : -#10
#}.

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
Inductive bool_all_types :=
| bval_t : bool -> bool_all_types
| berr.

Coercion bval_t : bool >-> bool_all_types.

Inductive all_types :=
| val_t : Val -> all_types
| array_t : Array -> all_types
| tuple_t : Tuple -> all_types
| dict_t : Dict -> all_types.

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

Definition default_env : Env := fun var => error.

Definition env1 := update (update (update (update (update default_env "a" 5) "b" (-#10)) "c" (#[ 7, 9, 15, 4#])) "x" true) "y" (#(#"f", -#2, 7#)).

(* ---------- Check a datatype ---------- *)
Inductive typeof_element :=
| var_tp : variable -> typeof_element
| val_tp : Val -> typeof_element
| array_tp : Array -> typeof_element
| tuple_tp : Tuple -> typeof_element
| dict_tp : Dict -> typeof_element.

Coercion var_tp : variable >-> typeof_element.
Coercion val_tp : Val >-> typeof_element.
Coercion array_tp : Array >-> typeof_element.
Coercion tuple_tp : Tuple >-> typeof_element.
Coercion dict_tp : Dict >-> typeof_element.

Definition typeof (x : typeof_element) (env : Env) : string :=
  match x with
  | var_tp x' => match (env x') with
              | error => "error"
              | positive x'' => "natural"
              | negative x'' => "integer"
              | boolean x'' => "boolean"
              | char x'' => "character"
              | array_t x' => "array"
              | tuple_t x' => "tuple"
              | dict_t x' => "dict"
              end
  | val_tp x' => match x' with
              | error => "error"
              | positive x'' => "natural"
              | negative x'' => "integer"
              | boolean x'' => "boolean"
              | char x'' => "character"
              end
  | array_tp x' => "array"
  | tuple_tp x' => "tuple"
  | dict_tp x' => "dict"
  end.

Notation "'@typeof(' A , B ')'" := (typeof A B) (at level 15).

(* Examples *)
Compute @typeof( "a", env1).
Compute @typeof( "b", env1).
Compute @typeof( "c", env1).
Compute @typeof( "x", env1).

(* ---------- Built-in functions ---------- *)
    (* Object doesn't change *)
  (* .count() *)

Fixpoint count_arr (col : Array) : nat :=
  match col with
  | arr_NULL => 0
  | (array_cons arr' arr'') => 1 + count_arr arr''
  end.

Fixpoint count_tup (col : Tuple) : nat :=
  match col with
  | tup_NULL => 0
  | (tuple_cons arr' arr'') => 1 + count_tup arr''
  end.

  (* .append() *)

Fixpoint append_arr (col1 col2 : Array) : Array :=
  match col1 with
  | arr_NULL => col2
  | array_cons arr' arr'' => array_cons arr' (append_arr arr'' col2)
  end.

Compute append_arr (#[1#]) (append_arr (#[1#]) (#[1#])).

Fixpoint append_arr_times (times : nat) (col1 : Array) : Array :=
  match times with
  | O => arr_NULL
  | S n' => append_arr col1 (append_arr_times n' col1)
  end.

Fixpoint append_tup (col1 col2 : Tuple) : Tuple :=
  match col1 with
  | tup_NULL => col2
  | tuple_cons tup' tup'' => tuple_cons tup' (append_tup tup'' col2)
  end.

Fixpoint append_tup_times (times : nat) (col1 : Tuple) : Tuple :=
  match times with
  | O => tup_NULL
  | S n' => append_tup col1 (append_tup_times n' col1)
  end.

  (* get() *)
Fixpoint get_arr (col1 : Array) (poz current_poz : nat) : Val :=
  match col1 with
  | arr_NULL => error
  | array_cons val' val'' => if Nat.eqb current_poz poz
                             then val'
                             else get_arr val'' poz (current_poz + 1)
  end.

Fixpoint get_tup (col1 : Tuple) (poz current_poz : nat) : Val :=
  match col1 with
  | tup_NULL => error
  | tuple_cons val' val'' => if Nat.eqb current_poz poz
                             then val'
                             else get_tup val'' poz (current_poz + 1)
  end.

    (* Object changes *)
  (* push() *)

Fixpoint push_arr (col1 : Array) (el : Val) : Array :=
  match col1 with
  | arr_NULL => array_cons el arr_NULL
  | array_cons val' val'' => array_cons val' (push_arr val'' el)
  end.

  (* pop() *)

Fixpoint pop_arr (col1 : Array) : Array :=
  match col1 with
  | arr_NULL => arr_NULL
  | array_cons val' arr_NULL => arr_NULL
  | array_cons val' val'' => array_cons val' (pop_arr val'')
  end.

  (* insert() *)
Fixpoint insert_arr (col1 : Array) (el : Val) (poz current_poz : nat) : Array :=
  match col1 with
  | arr_NULL => if Nat.eqb current_poz poz
                then array_cons el arr_NULL
                else arr_NULL
  | array_cons val' val'' => if Nat.eqb current_poz poz
                             then array_cons el (array_cons val' val'')
                             else if Nat.ltb poz (current_poz + 1)
                                  then arr_NULL
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
  | arr_NULL => arr_NULL
  | array_cons val' arr_NULL => arr_NULL
  | array_cons val' (array_cons val'' val''') => if Nat.eqb current_poz poz
                                                       then array_cons val'' val'''
                                                       else if Nat.eqb poz (current_poz + 1)
                                                            then array_cons val' val'''
                                                            else array_cons val' (array_cons val'' (remove_arr val''' poz (current_poz + 2)))
  end.

    (* string methods *)
  (* slice *)

Fixpoint slice_arr (col1 : Array) (abegin aend current_poz : nat) : Array :=
  match col1 with
  | arr_NULL => arr_NULL
  | array_cons val' val'' => if my_and (Nat.ltb abegin (current_poz + 1)) (Nat.ltb current_poz (aend + 1))
                             then array_cons val' (slice_arr val'' abegin aend (current_poz + 1))
                             else slice_arr val'' abegin aend (current_poz + 1)
  end.

Fixpoint slice_tup (col1 : Tuple) (abegin aend current_poz : nat) : Tuple :=
  match col1 with
  | tup_NULL => tup_NULL
  | tuple_cons val' val'' => if my_and (Nat.ltb abegin (current_poz + 1)) (Nat.ltb current_poz (aend + 1))
                             then tuple_cons val' (slice_tup val'' abegin aend (current_poz + 1))
                             else slice_tup val'' abegin aend (current_poz + 1)
  end.

(* ---------- Expression Syntax ---------- *)
Inductive val_expression :=
| exp_val : all_types -> val_expression
| exp_var : variable -> val_expression
| exp_plus : val_expression -> val_expression -> val_expression
| exp_sub : val_expression -> val_expression -> val_expression
| exp_mul : val_expression -> val_expression -> val_expression
| exp_div : val_expression -> val_expression -> val_expression
| exp_mod : val_expression -> val_expression -> val_expression
(* to be able to make something like: if typeof(3) == "number" then... *)
| exp_typeof : string -> val_expression
(* for vectors methods *)
| exp_count : variable -> val_expression
| exp_append : variable -> variable -> val_expression
| exp_get : variable -> nat -> val_expression
| exp_slice : variable -> nat -> nat -> val_expression.

Coercion exp_val : all_types >-> val_expression.
Coercion exp_var : variable >-> val_expression.

Notation "A +' B" := (exp_plus A B) (at level 76, left associativity).
Notation "A -' B" := (exp_sub A B) (at level 76, left associativity).
Notation "A *' B" := (exp_mul A B) (at level 66, left associativity).
Notation "A /' B" := (exp_div A B) (at level 66, left associativity).
Notation "A %' B" := (exp_mod A B) (at level 66, left associativity).
Notation "'type(' A ')'" := (exp_typeof A) (at level 60).

Notation "A '.count()'" := (exp_count A) (at level 60).
Notation "A '.append(' B ')'" := (exp_append A B) (at level 60).
Notation "A '.get(' B ')'" := (exp_get A B) (at level 60).
Notation "A '.slice(' B , C ')'" := (exp_slice A B C) (at level 60).

(* ---------- Operations with exceptions ---------- *)
Definition plus_with_error (v1 v2 : all_types) : all_types :=
  match v1, v2 with
  | val_t a1, val_t a2 => (match a1, a2 with
                          | error, _ => error
                          | positive b1, positive b2 => (b1 + b2)
                          | positive b1, negative b2 => (if Nat.ltb b1 b2
                                                         then negative (b2 - b1)
                                                         else positive (b1 - b2))
                          | positive b1, boolean b2 => (if Bool.eqb b2 true
                                                        then positive (b1 + 1)
                                                        else positive b1)
                          | positive b1, _ => error
                          | negative b1, positive b2 => (if Nat.ltb b2 b1
                                                         then negative (b1 - b2)
                                                         else positive (b2 - b1))
                          | negative b1, negative b2 => negative (b1 + b2)
                          | negative b1, boolean b2 => (if Bool.eqb b2 true
                                                        then (if Nat.ltb 1 b1
                                                              then negative (b1 - 1)
                                                              else positive (1 - b1))
                                                        else negative b1)
                          | negative b1, _ => error
                          | boolean b1, positive b2 => (if Bool.eqb b1 true
                                                        then positive (b2 + 1)
                                                        else positive b2)
                          | boolean b1, negative b2 => (if Bool.eqb b1 true
                                                        then (if Nat.ltb 1 b2
                                                              then negative (b2 - 1)
                                                              else positive (1 - b2))
                                                        else negative b2)
                          | boolean b1, boolean b2 => (if Bool.eqb b1 true
                                                       then (if Bool.eqb b2 true
                                                             then positive 2
                                                             else positive 1)
                                                       else (if Bool.eqb b2 true
                                                            then positive 1
                                                            else positive 0))
                          | boolean b1, _ => error
                          | char b1, char b2 => #[ char b1, char b2 #]
                          | char b1, _ => error
                          end)
  | val_t a1, _ => error
  | array_t a1, array_t a2 => (append_arr a1 a2)
  | array_t a1, _ => error
  | tuple_t a1, tuple_t a2 => (append_tup a1 a2)
  | tuple_t a1, _ => error
  | dict_t a1, _ => error
  end.

Definition sub_with_error (v1 v2 : all_types) : all_types :=
  match v1, v2 with
  | val_t a1, val_t a2 => (match a1, a2 with
                          | error, _ => error
                          | positive b1, positive b2 => (if Nat.ltb b1 b2
                                                         then negative (b2 - b1)
                                                         else positive (b1 - b2))
                          | positive b1, negative b2 => positive (b1 + b2)
                          | positive b1, boolean b2 => (if Bool.eqb b2 true
                                                        then (if Nat.eqb b1 0
                                                              then negative 1
                                                              else positive (b1 - 1))
                                                        else positive b1)
                          | positive b1, _ => error
                          | negative b1, positive b2 => negative (b1 + b2)
                          | negative b1, negative b2 => (if Nat.ltb b1 b2
                                                         then positive (b2 - b1)
                                                         else negative (b1 - b2))
                          | negative b1, boolean b2 => (if Bool.eqb b2 true
                                                        then negative (b1 + 1)
                                                        else negative b1)
                          | negative b1, _ => error
                          | boolean b1, positive b2 => (if Bool.eqb b1 true
                                                        then (if Nat.ltb 1 b2
                                                              then negative (b2 - 1)
                                                              else positive (1 - b2))
                                                        else negative b2)
                          | boolean b1, negative b2 => (if Bool.eqb b1 true
                                                        then positive (b2 + 1)
                                                        else positive b2)
                          | boolean b1, boolean b2 => (if Bool.eqb b1 true
                                                       then (if Bool.eqb b2 true
                                                             then positive 0
                                                             else positive 1)
                                                       else (if Bool.eqb b2 true
                                                            then negative 1
                                                            else positive 0))
                          | boolean b1, _ => error
                          | _, _ => error
                          end)
  | _, _ => error
  end.

Definition mul_with_error (v1 v2 : all_types) : all_types :=
  match v1, v2 with
  | val_t a1, val_t a2 => (match a1, a2 with
                          | error, _ => error
                          | positive b1, positive b2 => (b1 * b2)
                          | positive b1, negative b2 => negative (b1 * b2)
                          | positive b1, boolean b2 => (if Bool.eqb b2 true
                                                        then positive b1
                                                        else positive 0)
                          | positive b1, _ => error
                          | negative b1, positive b2 => negative (b1 * b2)
                          | negative b1, negative b2 => positive (b1 * b2)
                          | negative b1, boolean b2 => (if Bool.eqb b2 true
                                                        then negative b1
                                                        else positive 0)
                          | negative b1, _ => error
                          | boolean b1, positive b2 => (if Bool.eqb b1 true
                                                        then positive b2
                                                        else positive 0)
                          | boolean b1, negative b2 => (if Bool.eqb b1 true
                                                        then negative b2
                                                        else positive 0)
                          | boolean b1, boolean b2 => (if Bool.eqb b1 true
                                                       then (if Bool.eqb b2 true
                                                             then positive 1
                                                             else positive 0)
                                                       else (if Bool.eqb b2 true
                                                            then positive 0
                                                            else positive 0))
                          | boolean b1, _ => error
                          | char b1, char b2 => error
                          | char b1, _ => error
                          end)
  | val_t a1, array_t a2 => (match a1 with
                            | positive a1' => append_arr_times a1' a2
                            | _ => error
                            end)
  | val_t a1, tuple_t a2 => (match a1 with
                            | positive a1' => append_tup_times a1' a2
                            | _ => error
                            end)
  | val_t a1, _ => error
  | array_t a1, array_t a2 => (append_arr a1 a2)
  | array_t a1, val_t a2 => (match a2 with
                            | positive a1' => append_arr_times a1' a1
                            | _ => error
                            end)
  | array_t a1, _ => error
  | tuple_t a1, tuple_t a2 => (append_tup a1 a2)
  | tuple_t a1, val_t a2 => (match a2 with
                            | positive a1' => append_tup_times a1' a1
                            | _ => error
                            end)
  | tuple_t a1, _ => error
  | dict_t a1, _ => error
  end.

Definition div_with_error (v1 v2 : all_types) : all_types :=
  match v1, v2 with
  | val_t a1, val_t a2 => (match a1, a2 with
                          | error, _ => error
                          | positive b1, positive b2 => (if Nat.eqb b2 0
                                                        then error
                                                        else positive (Nat.div b1 b2))
                          | positive b1, negative b2 => (if Nat.eqb b2 0
                                                        then error
                                                        else negative (Nat.div b1 b2))
                          | positive b1, boolean b2 => (if Bool.eqb b2 true
                                                        then positive b1
                                                        else error)
                          | positive b1, _ => error
                          | negative b1, positive b2 => if Nat.eqb b2 0
                                                        then error
                                                        else negative (Nat.div b1 b2)
                          | negative b1, negative b2 => if Nat.eqb b2 0
                                                        then error
                                                        else positive (Nat.div b1 b2)
                          | negative b1, boolean b2 => (if Bool.eqb b2 true
                                                        then negative b1
                                                        else error)
                          | negative b1, _ => error
                          | boolean b1, positive b2 => (if Nat.eqb b2 0
                                                        then error
                                                        else (if Bool.eqb b1 true
                                                              then positive (Nat.div 1 b2)
                                                              else positive 0))
                          | boolean b1, negative b2 => (if Nat.eqb b2 0
                                                        then error
                                                        else (if Bool.eqb b1 true
                                                              then negative (Nat.div 1 b2)
                                                              else positive 0))
                          | boolean b1, boolean b2 => (if Bool.eqb b1 true
                                                       then (if Bool.eqb b2 true
                                                             then positive 1
                                                             else error)
                                                       else (if Bool.eqb b2 true
                                                            then positive 0
                                                            else error))
                          | boolean b1, _ => error
                          | char b1, char b2 => error
                          | char b1, _ => error
                          end)
  | val_t a1, _ => error
  | array_t a1, _ => error
  | tuple_t a1, _ => error
  | dict_t a1, _ => error
  end.

Definition mod_with_error (v1 v2 : all_types) : all_types :=
  match v1, v2 with
  | val_t a1, val_t a2 => (match a1, a2 with
                          | error, _ => error
                          | positive b1, positive b2 => (if Nat.eqb b2 0
                                                        then error
                                                        else positive (Nat.modulo b1 b2))
                          | positive b1, negative b2 => (if Nat.eqb b2 0
                                                        then error
                                                        else positive (Nat.modulo b1 b2))
                          | positive b1, boolean b2 => (if Bool.eqb b2 true
                                                        then positive b1
                                                        else error)
                          | positive b1, _ => error
                          | negative b1, positive b2 => if Nat.eqb b2 0
                                                        then error
                                                        else negative (Nat.modulo b1 b2)
                          | negative b1, negative b2 => if Nat.eqb b2 0
                                                        then error
                                                        else negative (Nat.modulo b1 b2)
                          | negative b1, boolean b2 => (if Bool.eqb b2 true
                                                        then negative b1
                                                        else error)
                          | negative b1, _ => error
                          | boolean b1, positive b2 => (if Nat.eqb b2 0
                                                        then error
                                                        else (if Bool.eqb b1 true
                                                              then positive (Nat.modulo 1 b2)
                                                              else positive 0))
                          | boolean b1, negative b2 => (if Nat.eqb b2 0
                                                        then error
                                                        else (if Bool.eqb b1 true
                                                              then negative (Nat.modulo 1 b2)
                                                              else positive 0))
                          | boolean b1, boolean b2 => (if Bool.eqb b1 true
                                                       then (if Bool.eqb b2 true
                                                             then positive 1
                                                             else error)
                                                       else (if Bool.eqb b2 true
                                                            then positive 0
                                                            else error))
                          | boolean b1, _ => error
                          | char b1, char b2 => error
                          | char b1, _ => error
                          end)
  | val_t a1, _ => error
  | array_t a1, _ => error
  | tuple_t a1, _ => error
  | dict_t a1, _ => error
  end.

(*---------- Small-step operational semantics ----------*)
Reserved Notation "A =[ S ]=> N" (at level 70).

Inductive aeval_small_step : val_expression -> Env -> val_expression -> Prop :=
| alookup : forall x sigma, exp_var x =[ sigma ]=> match (sigma x) with
                                                   | val_t x' => x'
                                                   | array_t x' => x'
                                                   | tuple_t x' => x'
                                                   | dict_t x' => x'
                                                   end
| aconst : forall n sigma, exp_val n =[ sigma ]=> n
(* add *)
| add_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    (a1 +' a2) =[ sigma ]=> (a1' +' a2)
| add_2 : forall a1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    (a1 +' a2) =[ sigma ]=> (a1 +' a2')
| add : forall i1 i2 sigma n,
        n = exp_val (plus_with_error i1 i2) ->
        (i1 +' i2) =[ sigma ]=> n
(* sub *)
| sub_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    (a1 -' a2) =[ sigma ]=> (a1' -' a2)
| sub_2 : forall a1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    (a1 -' a2) =[ sigma ]=> (a1 -' a2')
| sub : forall i1 i2 sigma n,
        n = exp_val (sub_with_error i1 i2) ->
        (i1 -' i2) =[ sigma ]=> n
(* mul *)
| mul_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    (a1 *' a2) =[ sigma ]=> (a1' *' a2)
| mul_2 : forall a1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    (a1 *' a2) =[ sigma ]=> (a1 *' a2')
| mul : forall i1 i2 sigma n,
        n = exp_val (mul_with_error i1 i2) ->
        (i1 *' i2) =[ sigma ]=> n
(* div *)
| div_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    (a1 /' a2) =[ sigma ]=> (a1' /' a2)
| div_2 : forall a1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    (a1 /' a2) =[ sigma ]=> (a1 /' a2')
| div : forall i1 i2 sigma n,
        n = exp_val (div_with_error i1 i2) ->
        (i1 /' i2) =[ sigma ]=> n
(* mod *)
| mod_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    (a1 %' a2) =[ sigma ]=> (a1' %' a2)
| mod_2 : forall a1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    (a1 %' a2) =[ sigma ]=> (a1 %' a2')
| mod_ : forall i1 i2 sigma n,
        n = exp_val (mod_with_error i1 i2) ->
        (i1 %' i2) =[ sigma ]=> n
| acount : forall x sigma, exp_count x =[ sigma ]=> match (sigma x) with
                                                   | val_t x' => error
                                                   | array_t x' => count_arr x'
                                                   | tuple_t x' => count_tup x'
                                                   | dict_t x' => error
                                                   end
| aget : forall x sigma index, exp_get x index =[ sigma ]=> match (sigma x) with
                                                           | val_t x' => error
                                                           | array_t x' => get_arr x' index 0
                                                           | tuple_t x' => get_tup x' index 0
                                                           | dict_t x' => error
                                                           end
| aslice : forall x sigma begin_ end_, exp_slice x begin_ end_ =[ sigma ]=> match (sigma x) with
                                                                           | val_t x' => error
                                                                           | array_t x' => slice_arr x' begin_ end_ 0
                                                                           | tuple_t x' => slice_tup x' begin_ end_ 0
                                                                           | dict_t x' => error
                                                                           end
where "A =[ S ]=> N" := (aeval_small_step A S N).

Reserved Notation "A =[ S ]>* N" (at level 70).
Inductive aeval_closure  : val_expression -> Env -> val_expression -> Prop :=
| a_refl : forall a sigma, a =[ sigma ]>* a
| a_tran : forall a1 a2 a3 sigma,
    (a1 =[ sigma ]=> a2) ->
    (a2 =[ sigma ]>* a3) ->
    (a1 =[ sigma ]>* a3)
where "A =[ S ]>* N" := (aeval_closure A S N).

Example ex1 : #[1,2,3,4#] =[ env1 ]=> #[1,2,3,4#].
Proof.
  eapply aconst.
Qed.

Example ex2 : (#"a" +' #"a") =[ env1 ]>* (#[#"a", #"a"#]).
Proof.
  eapply a_tran.
  +eapply add. simpl. reflexivity.
  +eapply a_refl.
Qed.

Example ex3 : (3 *' #[1,2,3#] +' #[4,5,6#]) =[ env1 ]>* (#[1,2,3,1,2,3,1,2,3,4,5,6#]).
Proof.
  eapply a_tran.
  +eapply add_1. eapply mul. reflexivity.
  +simpl. eapply a_tran.
    -eapply add. reflexivity.
    -simpl. eapply a_refl.
Qed.

Example ex4 : (-#20 *' (56 /' (-#15 /' 3 +' true *' 5)) +' false) =[ env1 ]>* error.
Proof.
  eapply a_tran.
  +eapply add_1. eapply mul_2. eapply div_2. eapply add_1. eapply div. simpl. reflexivity.
  +eapply a_tran.
    -eapply add_1. eapply mul_2. eapply div_2. eapply add_2. eapply mul. simpl. reflexivity.
    -eapply a_tran.
      *eapply add_1. eapply mul_2. eapply div_2. eapply add. simpl. reflexivity.
      *eapply a_tran.
        ++eapply add_1. eapply mul_2. eapply div. simpl. reflexivity.
        ++eapply a_tran.
          --eapply add_1. eapply mul. simpl. reflexivity.
          --eapply a_tran.
            **eapply add. simpl. reflexivity.
            **eapply a_refl.
Qed.

Example ex5 : "c".count() =[ env1 ]>* 4.
Proof.
  eapply a_tran.
  -eapply acount.
  -unfold env1. simpl. fold env1. eapply a_refl.
Qed.

Example ex6: (#[1,2,3#] +' #[#"a", #"n", #"a"#] +' "c") =[ env1 ]>* #[1,2,3,#"a",#"n",#"a",7,9,15,4#].
Proof.
  eapply a_tran.
  -eapply add_1. eapply add. simpl. reflexivity.
  -eapply a_tran.
    +eapply add_2. eapply alookup. 
    +simpl. eapply a_tran.
      *eapply add. simpl. reflexivity.
      *eapply a_refl.
Qed.

Example ex7 : "y" *' ("y".get(1) +' "y".get(2) -' "y".count()) =[ env1 ]>* (#(#"f", -#2, 7,#"f", -#2, 7#)).
Proof.
  eapply a_tran. eapply mul_1. eapply alookup. simpl. eapply a_tran.
  eapply mul_2. eapply sub_1. eapply add_1. eapply aget. simpl.
  eapply a_tran. eapply mul_2. eapply sub_1. eapply add_2. eapply aget. simpl.
  eapply a_tran. eapply mul_2. eapply sub_1. eapply add. simpl. reflexivity.
  eapply a_tran. eapply mul_2. eapply sub_2. eapply acount. simpl.
  eapply a_tran. eapply mul_2. eapply sub. simpl. reflexivity.
  eapply a_tran. eapply mul. simpl. reflexivity.
  eapply a_refl.
Qed.

(* ---------- Boolean Expression Syntax ---------- *)
Inductive boolean_expression :=
| bval : bool_all_types -> boolean_expression
| bnot : boolean_expression -> boolean_expression
| band : boolean_expression -> boolean_expression -> boolean_expression
| bor : boolean_expression -> boolean_expression -> boolean_expression
| blt : val_expression -> val_expression -> boolean_expression
| beq : val_expression -> val_expression -> boolean_expression
| bgt : val_expression -> val_expression -> boolean_expression.

Coercion bval : bool_all_types >-> boolean_expression.

Notation "!' A" := (bnot A) (at level 85).
Notation "A 'and'' B" := (band A B) (at level 90).
Notation "A 'or'' B" := (bor A B) (at level 90).
Notation "A <' B" := (blt A B) (at level 80).
Notation "A ==' B" := (beq A B) (at level 80).
Notation "A >' B" := (bgt A B) (at level 80).

Definition lessthan_with_error (v1 v2 : all_types) : all_types :=
  match v1, v2 with
  | val_t a1, val_t a2 => (match a1, a2 with
                          | error, _ => error
                          | positive b1, positive b2 => (if Nat.ltb b1 b2
                                                         then boolean true
                                                         else boolean false)
                          | positive b1, negative b2 => boolean false
                          | positive b1, boolean b2 => (if Bool.eqb b2 true
                                                        then if Nat.ltb 0 b1
                                                             then boolean false
                                                             else boolean true
                                                        else boolean false)
                          | positive b1, _ => error
                          | negative b1, positive b2 => (if Nat.eqb b1 0
                                                         then if Nat.eqb b2 0
                                                              then boolean false
                                                              else boolean true
                                                         else boolean true)
                          | negative b1, negative b2 => (if Nat.ltb b1 b2
                                                         then boolean false
                                                         else boolean true)
                          | negative b1, boolean b2 => (if Bool.eqb b2 false
                                                        then if Nat.eqb 0 b1
                                                             then boolean false
                                                             else boolean true
                                                        else boolean true)
                          | negative b1, _ => error
                          | boolean b1, positive b2 => (if Bool.eqb b1 true
                                                        then if Nat.ltb 1 b2
                                                             then boolean true
                                                             else boolean false
                                                        else if Nat.ltb 0 b2
                                                             then boolean true
                                                             else boolean false)
                          | boolean b1, negative b2 => boolean false
                          | boolean b1, boolean b2 => (if Bool.eqb b1 true
                                                       then boolean false
                                                       else (if Bool.eqb b2 true
                                                            then boolean true
                                                            else boolean false))
                          | _, _ => error
                          end)
  | _, _ => error
  end.

Definition greaterthan_with_error (v1 v2 : all_types) : all_types := lessthan_with_error v2 v1.

Definition not_with_error (v1 : all_types) : all_types :=
  match v1 with
  | val_t a1 => (match a1 with
                | boolean b1 => (if Bool.eqb b1 true
                                 then boolean false
                                 else boolean true)
                | _ => error
                end)
  | _ => error
  end.

Definition eq_with_error (v1 v2 : all_types) : all_types := 
  match (not_with_error (lessthan_with_error v1 v2)) with
  | true => (match (not_with_error (lessthan_with_error v2 v1)) with
            | true => boolean true
            | false => boolean false
            | _ => error
            end)
  | false => boolean false
  | _ => error
  end.

Reserved Notation "B ={ S }=> B'" (at level 60).
Inductive beval_small_step : boolean_expression -> Env -> boolean_expression -> Prop :=
| bconst : forall n sigma, bval n ={ sigma }=> n
| lessthan_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    (a1 <' a2) ={ sigma }=> (a1' <' a2)
| lessthan_2 : forall i1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    ((exp_val i1) <' a2) ={ sigma }=> ((exp_val i1) <' a2')
| lessthan : forall i1 i2 b sigma,
    b = (match (lessthan_with_error i1 i2) with
        | boolean a => if Bool.eqb a true
                       then bval_t true
                       else bval_t false
        | _ => berr
        end) ->
    ((exp_val i1) <' (exp_val i2)) ={ sigma }=> b
| greaterthan_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    (a1 >' a2) ={ sigma }=> (a1' >' a2)
| greaterthan_2 : forall i1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    ((exp_val i1) >' a2) ={ sigma }=> ((exp_val i1) >' a2')
| greaterthan : forall i1 i2 b sigma,
    b = (match (greaterthan_with_error i1 i2) with
        | boolean a => if Bool.eqb a true
                       then bval_t true
                       else bval_t false
        | _ => berr
        end) ->
    ((exp_val i1) >' (exp_val i2)) ={ sigma }=> b
| not : forall b b' sigma,
    b ={ sigma }=> b' ->
    (bnot b) ={ sigma }=> (bnot b')
| not_true : forall sigma, (bnot true) ={ sigma }=> bval_t false
| not_false : forall sigma, (bnot false) ={ sigma }=> bval_t true
| and_1 : forall b1 b1' sigma b2,
    b1 ={ sigma }=> b1' ->
    (band b1 b2) ={ sigma }=> (band b1' b2)
| and_false : forall b2 sigma,
    (band (bval_t false) b2) ={ sigma }=> bval_t false
| and_true : forall b2 sigma,
    (band (bval_t true) b2) ={ sigma }=> b2
| or_1 : forall b1 b1' sigma b2,
    b1 ={ sigma }=> b1' ->
    (bor b1 b2) ={ sigma }=> (bor b1' b2)
| or_false : forall b2 sigma,
    (bor (bval_t false) b2) ={ sigma }=> b2
| or_true : forall b2 sigma,
    (bor (bval_t true) b2) ={ sigma }=> bval_t true
| eq_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    (a1 ==' a2) ={ sigma }=> (a1' ==' a2)
| eq_2 : forall i1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    ((exp_val i1) ==' a2) ={ sigma }=> ((exp_val i1) ==' a2')
| eq : forall i1 i2 b sigma,
    b = (match (eq_with_error i1 i2) with
        | boolean a => if Bool.eqb a true
                       then bval_t true
                       else bval_t false
        | _ => berr
        end) ->
    ((exp_val i1) ==' (exp_val i2)) ={ sigma }=> b
where "B ={ S }=> B'" := (beval_small_step B S B').

Reserved Notation "B ={ S }>* B'" (at level 60).
Inductive beval_closure : boolean_expression -> Env -> boolean_expression -> Prop :=
| b_refl : forall b sigma, b ={ sigma }>* b
| b_tran : forall b1 b2 b3 sigma,
    (b1 ={ sigma }=> b2) ->
    (b2 ={ sigma }>* b3) ->
    (b1 ={ sigma }>* b3)
where "B ={ S }>* B'" := (beval_closure B S B').

Example ex8: (4 <' "a") ={ env1 }>* true.
Proof.
  eapply b_tran.
  -eapply lessthan_2. eapply alookup.
  -simpl. eapply b_tran.
    +eapply lessthan. simpl. reflexivity.
    +eapply b_refl.
Qed.

Example ex9: ("c".count() >' "a" -'2) ={ env1 }>* true.
Proof.
  eapply b_tran.
  -eapply greaterthan_1. eapply acount.
  -simpl. eapply b_tran.
    +eapply greaterthan_2. eapply sub_1. eapply alookup.
    +simpl. eapply b_tran. eapply greaterthan_2. eapply sub. simpl. reflexivity.
      *eapply b_tran. eapply greaterthan. simpl. reflexivity. eapply b_refl.
Qed.

Example ex10: (!'(4 <' 3)) ={ env1 }>* true.
Proof.
  eapply b_tran.
  -eapply not. eapply lessthan. simpl. reflexivity. 
  -eapply b_tran. eapply not_false. eapply b_refl.
Qed.

Example ex11: ((!'false) and' false) ={ env1 }>* false.
Proof.
  eapply b_tran.
  -eapply and_1. eapply not_false.
  -eapply b_tran. eapply and_true. eapply b_refl.
Qed.

Example ex12: ("a" ==' 5) ={ env1 }>* true.
Proof.
  eapply b_tran.
  -eapply eq_1. eapply alookup.
  -simpl. eapply b_tran. eapply eq. simpl. reflexivity. eapply b_refl.
Qed.

(*
COMM FOR COMPILATION PART



(* -------------------- Comments -------------------- *)
Inductive comment : Set :=
| comm : string -> comment.

Notation "/* A */" := (comm A) (at level 99).

(* -------------------- Statements -------------------- *)
Inductive Statement :=
(* vectors methods *)
| push : variable -> val_expression -> Statement
| pop : variable -> Statement
| insert : variable -> val_expression -> nat -> Statement
| remove : variable -> nat -> Statement
(* comm *)
| empty_stmt : comment -> Statement
(* assignment *)
| skip
| assignment : variable -> val_expression -> Statement
| sequence : Statement -> Statement -> Statement
(* conditional statements *)
| ifthen : boolean_expression -> Statement -> Statement
| ifthenelse : boolean_expression -> Statement -> Statement -> Statement
(* repetition statements *)
| while : boolean_expression -> Statement -> Statement
| do_while : Statement -> boolean_expression -> Statement
| forloop : boolean_expression -> Statement -> Statement -> Statement.

Notation "A '.push(' B ')'" := (push A B) (at level 1).
Notation "A '.pop()'" := (pop A) (at level 1).
Notation "A '.insert(' B , C ')'" := (insert A B C) (at level 1).
Notation "A '.remove(' B ')'" := (remove A B) (at level 1).

Coercion empty_stmt : comment >-> Statement.

Notation "X ::= A" := (assignment X A) (at level 90).
Notation "S ; S'" := (sequence S S') (at level 97, right associativity).

Notation "'if'' A 'then'' B 'endif''" := (ifthen A B) (at level 95).
Notation "'if'' A 'then'' B 'else'' C 'endif''" := (ifthenelse A B C) (at level 95).
Notation "'while'' A 'do'' B 'endwhile''" := (while A B) (at level 95).
Notation "'do'' A 'while'' B 'enddowhile''" := (do_while A B) (at level 95).
Notation "'for'' A ;' B 'do'' C 'endfor''" := (forloop A B C) (at level 95).

Reserved Notation "St1 -{ State }->[ St2 ;' State' ]" (at level 60).
Inductive eval_small_step : Statement -> Env -> Statement -> Env -> Prop :=
| empty : forall sigma a,
    (empty_stmt a) -{ sigma }->[ skip ;' sigma]
| assign_2 : forall a a' x sigma,
    a =[ sigma ]=> a' -> 
    (x ::= a) -{ sigma }->[ x ::= a' ;' sigma ]
| assign : forall x i sigma,
    (x ::= (exp_val i)) -{ sigma }->[ skip ;' (update sigma x  i) ]
| seq_1 : forall s1 s1' s2 sigma sigma',
    s1 -{ sigma }->[ s1' ;' sigma' ] ->
    (s1 ; s2) -{ sigma }->[ (s1' ; s2) ;' sigma' ]
| seq : forall s2 sigma,
    (skip ; s2) -{ sigma }->[ s2 ;' sigma ]
| if_1 : forall b b' s1 s2 sigma,
    b ={ sigma }=> b' -> 
    (ifthenelse b s1 s2) -{ sigma }->[ ifthenelse b' s1 s2 ;' sigma ]
| if_true : forall s1 s2 sigma,
    (ifthenelse true s1 s2) -{ sigma }->[ s1 ;' sigma ]
| if_false : forall s1 s2 sigma,
    (ifthenelse false s1 s2) -{ sigma }->[ s2 ;' sigma ]
| ifthen_1 : forall b b' s1 sigma,
    b ={ sigma }=> b' -> 
    (ifthen b s1) -{ sigma }->[ ifthen b' s1 ;' sigma ]
| ifthen_true : forall s1 sigma,
    (ifthen true s1) -{ sigma }->[ s1 ;' sigma ]
| ifthen_false : forall s1 sigma,
    (ifthen false s1) -{ sigma }->[ skip ;' sigma ]
| while_ : forall b s sigma,
    while b s -{ sigma }->[ ifthenelse b (s ; while b s) skip ;' sigma ]
| do_while_ : forall s b sigma,
    (do_while s b) -{ sigma }->[ s ; (ifthenelse b (s ; do_while s b) skip) ;' sigma ]
| for_ : forall b s1 s2 sigma,
    forloop b s1 s2 -{ sigma }->[ ifthenelse b ((s2 ; s1) ; forloop b s1 s2) skip ;' sigma ]
(*| push : forall a a' x sigma,
    a =[ sigma ]=> a' -> 
    (x ::= a) -{ sigma }->[ x ::= a' ;' sigma ]*)
| push_1 : forall x a a' sigma,
    a =[ sigma ]=> a' ->
    ((push x a) -{ sigma }->[ (push x a') ;' sigma ])
| push_ : forall x i sigma (new_val : all_types),
    new_val = (match (sigma x) with
              | array_t x' => push_arr x' i
              | _ => error
              end) ->
    (push x i) -{ sigma }->[ skip ;' (update sigma x new_val) ]
| pop_ : forall x sigma (new_val : all_types),
    new_val = (match (sigma x) with
              | array_t x' => pop_arr x'
              | _ => error
              end) ->
    (pop x) -{ sigma }->[ skip ;' (update sigma x new_val) ]
| insert_1 : forall x a a' index sigma,
    a =[ sigma ]=> a' ->
    (insert x a index) -{ sigma }->[ (insert x a' index) ;' sigma ]
| insert_ : forall x i index sigma (new_val : all_types),
    new_val = (match (sigma x) with
              | array_t x' => insert_arr x' i index 0
              | _ => error
              end) ->
    (insert x i index) -{ sigma }->[ skip ;' (update sigma x new_val) ]
| remove_ : forall x index sigma (new_val : all_types),
    new_val = (match (sigma x) with
              | array_t x' => remove_arr x' index 0
              | _ => error
              end) ->
    (remove x index) -{ sigma }->[ skip ;' (update sigma x new_val) ]
where "St1 -{ State }->[ St2 ;' State' ]" := (eval_small_step St1 State St2 State').

Reserved Notation "St1 -{ State }>*[ St2 ;' State' ]" (at level 60).
Inductive eval_closure : Statement -> Env -> Statement -> Env -> Prop :=
| refl : forall s sigma, s -{ sigma }>*[ s ;' sigma ]
| tran : forall s1 s2 s3 sigma1 sigma2 sigma3,
    s1 -{ sigma1 }->[ s2 ;' sigma2 ] ->
    s2 -{ sigma2 }>*[ s3 ;' sigma3 ] ->
    s1 -{ sigma1 }>*[ s3 ;' sigma3 ]
where "St1 -{ State }>*[ St2 ;' State' ]" := (eval_closure St1 State St2 State').

Example ex14: (if' 3 <' "a" then' "a" ::= 4 else' "a" ::= 5 endif') -{ env1 }>*[ skip ;' (update env1 "a" 4)].
Proof.
  eapply tran. eapply if_1. eapply lessthan_2. eapply alookup. simpl. eapply tran. eapply if_1. eapply lessthan. simpl. reflexivity.
  eapply tran. eapply if_true. eapply tran. eapply assign. eapply refl.
Qed.

Example ex15: ("i" ::= 0; "j" ::= 1) -{ env1 }>*[ skip ;' (update (update env1 "i" 0) "j" 1) ].
Proof.
  eapply tran. eapply seq_1. eapply assign. eapply tran. eapply seq. eapply tran. eapply assign. eapply refl.
Qed.

Definition progr := 
"nr" ::= 12;
"inv" ::= 0;
while' 0 <' "nr" do'
  "inv" ::= "inv" *' 10 +' "nr" %' 10;
  "nr" ::= "nr" /' 10
endwhile'
.

Example ex16: (progr) -{ env1 }>*[skip ;' (update (update (update (update (update (update env1 "nr" 12) "inv" 0) "inv" 2) "nr" 1) "inv" 21) "nr" 0) ].
Proof.
  unfold progr. eapply tran. eapply seq_1. eapply assign. eapply tran. eapply seq. eapply tran.
  eapply seq_1. eapply assign. eapply tran. eapply seq.

  eapply tran. eapply while_. eapply tran.
  eapply if_1. eapply lessthan_2. eapply alookup. simpl. eapply tran. eapply if_1. eapply lessthan.
  simpl. reflexivity. eapply tran. eapply if_true. eapply tran. eapply seq_1. eapply seq_1. eapply assign_2.
  eapply add_1. eapply mul_1. eapply alookup. simpl. eapply tran. eapply seq_1. eapply seq_1. eapply assign_2.
  eapply add_1. eapply mul. simpl. reflexivity. eapply tran. eapply seq_1. eapply seq_1. eapply assign_2. eapply add_2.
  eapply mod_1. eapply alookup. simpl. eapply tran. eapply seq_1. eapply seq_1. eapply assign_2. eapply add_2. eapply mod_.
  simpl. reflexivity. eapply tran. eapply seq_1. eapply seq_1. eapply assign_2. eapply add. simpl. reflexivity. eapply tran.
  eapply seq_1. eapply seq_1. eapply assign. eapply tran. eapply seq_1. eapply seq. eapply tran. eapply seq_1. eapply assign_2.
  eapply div_1. eapply alookup. simpl. eapply tran. eapply seq_1. eapply assign_2. eapply div. simpl. reflexivity. eapply tran.
  eapply seq_1. eapply assign. eapply tran. eapply seq.

  eapply tran. eapply while_. eapply tran.
  eapply if_1. eapply lessthan_2. eapply alookup. simpl. eapply tran. eapply if_1. eapply lessthan.
  simpl. reflexivity. eapply tran. eapply if_true. eapply tran. eapply seq_1. eapply seq_1. eapply assign_2.
  eapply add_1. eapply mul_1. eapply alookup. simpl. eapply tran. eapply seq_1. eapply seq_1. eapply assign_2.
  eapply add_1. eapply mul. simpl. reflexivity. eapply tran. eapply seq_1. eapply seq_1. eapply assign_2. eapply add_2.
  eapply mod_1. eapply alookup. simpl. eapply tran. eapply seq_1. eapply seq_1. eapply assign_2. eapply add_2. eapply mod_.
  simpl. reflexivity. eapply tran. eapply seq_1. eapply seq_1. eapply assign_2. eapply add. simpl. reflexivity. eapply tran.
  eapply seq_1. eapply seq_1. eapply assign. eapply tran. eapply seq_1. eapply seq. eapply tran. eapply seq_1. eapply assign_2.
  eapply div_1. eapply alookup. simpl. eapply tran. eapply seq_1. eapply assign_2. eapply div. simpl. reflexivity. eapply tran.
  eapply seq_1. eapply assign. eapply tran. eapply seq.

  eapply tran. eapply while_. eapply tran.
  eapply if_1. eapply lessthan_2. eapply alookup. simpl. eapply tran. eapply if_1. eapply lessthan.
  simpl. reflexivity. eapply tran. eapply if_false. eapply refl.
Qed.

Example ex17: (for' "a" <' 6 ;' "a" ::= "a" +' 1 do' "i" ::= "a" *' 2 endfor') -{ env1 }>*[skip ;' (update (update env1 "i" 10) "a" 6) ].
Proof.
  eapply tran. eapply for_. eapply tran. eapply if_1. eapply lessthan_1. eapply alookup. simpl.
  eapply tran. eapply if_1. eapply lessthan. simpl. reflexivity.
  eapply tran. eapply if_true. eapply tran. eapply seq_1. eapply seq_1. eapply assign_2. eapply mul_1. eapply alookup. simpl.
  eapply tran. eapply seq_1. eapply seq_1. eapply assign_2. eapply mul. simpl. reflexivity.
  eapply tran. eapply seq_1. eapply seq_1. eapply assign. eapply tran. eapply seq_1. eapply seq. eapply tran. eapply seq_1.
  eapply assign_2. eapply add_1. eapply alookup. simpl. eapply tran. eapply seq_1.
  eapply assign_2. eapply add. simpl. reflexivity. eapply tran. eapply seq_1. eapply assign. eapply tran. eapply seq.

  eapply tran. eapply for_. eapply tran. eapply if_1. eapply lessthan_1. eapply alookup. simpl.
  eapply tran. eapply if_1. eapply lessthan. simpl. reflexivity.
  eapply tran. eapply if_false. eapply refl.
Qed.

Example ex18: (/* "Initializare x" */ ; "x" ::= #[ 2, 3, 4 #])-{ env1 }>*[skip ;' update env1 "x" (#[ 2, 3, 4 #]) ].
Proof.
  eapply tran. eapply seq_1. eapply empty. eapply tran. eapply seq. eapply tran. eapply assign. eapply refl.
Qed.

Example ex19: ("c".push(2 +' 3))-{ env1 }>*[ skip ;' (update env1 "c" (#[ 7, 9, 15, 4, 5#])) ].
Proof.
  eapply tran. eapply push_1. eapply add. simpl. reflexivity.
  eapply tran. eapply push_. simpl. reflexivity. eapply refl.
Qed.

Example ex20: ("c".insert("b", 3))-{ env1 }>*[ skip ;' (update env1 "c" (#[ 7, 9, 15, -#10, 4#])) ].
Proof.
  eapply tran. eapply insert_1. eapply alookup. simpl.
  eapply tran. eapply insert_. simpl. reflexivity. eapply refl.
Qed.

Check
/* "Random comment" */;
"v" ::= #[ 22, 33, -#12, 14, -#89 #];
"i" ::= 0;
for' "i" <' "v".count();' "i" ::= "i" +' 1 do'
  "a" ::= "v".get(0);
  if' "a" ==' 0 then'
    "a" ::= 200
  endif';
  while' "a" >' 0 do'
    if' "a" %' 3 ==' 0 then'
      "a" ::= "a" /' 3
    else'
      "a" ::= "a" /' 2
    endif'
  endwhile'
endfor'
.



*)
(* ---------- Lambda functions ----------*)
Inductive lambda_aexp :=
| lval : all_types -> lambda_aexp
| lparam : string -> lambda_aexp
| lplus : lambda_aexp -> lambda_aexp -> lambda_aexp
| lsub : lambda_aexp -> lambda_aexp -> lambda_aexp
| lmul : lambda_aexp -> lambda_aexp -> lambda_aexp
| ldiv : lambda_aexp -> lambda_aexp -> lambda_aexp
| lmod : lambda_aexp -> lambda_aexp -> lambda_aexp.

Coercion lval : all_types >-> lambda_aexp.
Coercion lparam : string >-> lambda_aexp.

Notation "A +& B" := (lplus A B) (at level 76, left associativity).
Notation "A -& B" := (lsub A B) (at level 76, left associativity).
Notation "A *& B" := (lmul A B) (at level 66, left associativity).
Notation "A /& B" := (ldiv A B) (at level 66, left associativity).
Notation "A %& B" := (lmod A B) (at level 66, left associativity).

Inductive Params :=
| empty_params
| params_cons : string -> Params -> Params.

Notation "$( $)" := empty_params (format "$( $)", at level 60).
Notation "$( A , B , .. , N $)" := (params_cons A (params_cons B .. (params_cons N empty_params)..)) (at level 60).

(* Compute get_arr (#[ 1, 11, 111, 1111 #]) 3 0. *)

Fixpoint get_value (param : string) (params : Params) (arguments : Array) (current_index : nat) : all_types :=
  match params with
  | empty_params => error
  | params_cons a1 a2 => if eqb a1 param
                         then get_arr arguments current_index 0
                         else get_value param a2 arguments (current_index + 1)
  end.

(*Compute get_value ("f") ( $("b", "d", "c", "a", "e" $) ) ( #[2, 4, 3, 1, 5#] ) 0.*)

Fixpoint aeval_lambda_aexp (params : Params) (arguments : Array) (exp : lambda_aexp) : all_types :=
  match exp with
  | lval a => a
  | lparam a => get_value a params arguments 0
  | lplus a1 a2 => plus_with_error (aeval_lambda_aexp params arguments a1) (aeval_lambda_aexp params arguments a2)
  | lsub a1 a2 => sub_with_error (aeval_lambda_aexp params arguments a1) (aeval_lambda_aexp params arguments a2)
  | lmul a1 a2 => mul_with_error (aeval_lambda_aexp params arguments a1) (aeval_lambda_aexp params arguments a2)
  | ldiv a1 a2 => div_with_error (aeval_lambda_aexp params arguments a1) (aeval_lambda_aexp params arguments a2)
  | lmod a1 a2 => mod_with_error (aeval_lambda_aexp params arguments a1) (aeval_lambda_aexp params arguments a2)
  end.

(*Definition my_exp := lsub (lparam "b") (lparam "e").
Compute aeval_lambda_aexp ( $("b", "d", "c", "a", "e" $) ) ( #[2, 4, 3, 1, 5#] ) (my_exp).*)

Inductive Lambda_pairs : Set :=
| basic_pair : Params -> lambda_aexp -> Lambda_pairs.

Notation " << P , A >> " := (basic_pair P A) (at level 50).

(*Check <<$("x", "y", "z"$), "x" +& "y" +& "z">>.*)

Definition lambda_Env := string -> Lambda_pairs.

Definition env0_lambda : lambda_Env :=
  fun l_func => basic_pair ($( $)) (lval error).

Definition update_lambda (env : lambda_Env) (l_func : string) (l_pair : Lambda_pairs) : lambda_Env :=
  fun var' => if eqb var' l_func
              then l_pair
              else (env var').

(*Definition env1_lambda := update_lambda env0_lambda "adunare_3" (basic_pair ($("x", "y", "z"$)) (lplus (lparam "x") (lplus (lparam "y") (lparam "z"))) ).
Compute env1_lambda "adunare_3".*)

Notation "N <- '@lambda(' E , P ')'" := (update_lambda E N P) (at level 35).

Definition env1_lambda := "round_arith_mean" <- @lambda( env0_lambda, <<$("x", "y", "z"$), ("x" +& "y" +& "z") /& 3>>).

Definition calculate_lambda (lambda_name : string) (l_env : lambda_Env) (arguments : Array) : all_types :=
  match (l_env lambda_name) with
  | basic_pair a b => aeval_lambda_aexp a arguments b
  end.

(*Compute calculate_lambda "round_arith_mean" env1_lambda ( #[ 31, 4, 10#]).*)

Notation " A '~(' B , C '~)'" := (calculate_lambda A B C) (at level 60).

Compute "round_arith_mean" ~(env1_lambda, (#[ 3, 4, 5#]) ~).

Definition env2_lambda := "double" <- @lambda( env1_lambda, <<$("x", "NULL"$), "x" *& 2 *& 3>>).

Compute "double" ~(env2_lambda, (#[ 1000#]) ~).

(*---------- Compilation bool_expr ----------*)
Require Import String.
Require Import List.
Import ListNotations.

Inductive boolean_exp :=
| _const : bool -> boolean_exp
| _var : variable -> boolean_exp
| _and : boolean_exp -> boolean_exp -> boolean_exp
| _or : boolean_exp -> boolean_exp -> boolean_exp
| _not : boolean_exp -> boolean_exp.

Coercion _const : bool >-> boolean_exp.
Coercion _var : variable >-> boolean_exp.
Notation "A &&& B" := (_and A B) (at level 50).
Notation "A ||| B" := (_or A B) (at level 55).
Notation "! A" := (_not A) (at level 45).

Check _const true.
Check _var "a".
Check _const false ||| _var "x" &&& _var "y".

Fixpoint interpret (b : boolean_exp) (env : variable -> bool) : bool :=
  match b with
  | _const c => c
  | _var x => (env x)
  | _and b1 b2 => andb (interpret b1 env) (interpret b2 env)
  | _or b1 b2 => orb (interpret b1 env) (interpret b2 env)
  | _not b => negb (interpret b env)
  end.

Definition env0 := fun x => if vars_eq x "x" then true else false.

Compute env0 "x".

(* Define a stack machine *)
Inductive Instruction :=
| asm_push_const : bool -> Instruction
| asm_push_var : variable -> Instruction
| asm_and : Instruction
| asm_or : Instruction
| asm_not : Instruction.

Definition Stack := list bool.
Definition run_instruction (i : Instruction) (env : variable -> bool) (stack : Stack) : Stack :=
  match i with
  | asm_push_const c => (c :: stack)
  | asm_push_var x => ((env x) :: stack)
  | asm_and => match stack with
               | n1 :: n2 :: stack' => (andb n1 n2) :: stack'
               | _ => stack
               end
  | asm_or => match stack with
              | n1 :: n2 :: stack' => (orb n1 n2) :: stack'
              | _ => stack
              end
  | asm_not => match stack with
               | n1 :: stack' => (negb n1) :: stack'
               | _ => stack
               end
  end.

Compute run_instruction (asm_push_const true) env0 [].
Compute run_instruction asm_and env0 [false;true].

Fixpoint run_instructions (is' : list Instruction) (env : variable -> bool) (stack : Stack) : Stack :=
  match is' with
  | [] => stack
  | i :: is'' => run_instructions is'' env (run_instruction i env stack)
  end.

Definition p1 := [
  asm_push_var "x";
  asm_push_const false;
  asm_or;
  asm_push_var "y";
  asm_not;
  asm_and
].

Compute run_instructions p1 env0 [].

Fixpoint compile (b : boolean_exp) : list Instruction :=
  match b with
  | _const c => [asm_push_const c]
  | _var x => [asm_push_var x]
  | _and b1 b2 => (compile b1) ++ (compile b2) ++ [asm_and]
  | _or b1 b2 => (compile b1) ++ (compile b2) ++ [asm_or]
  | _not b => (compile b) ++ [asm_not]
  end.

Definition bexp1 := "x" ||| "y" &&& "y".

Compute [interpret bexp1 env0].

Compute run_instructions (compile bexp1) env0 [].

Open Scope bool_scope.

Lemma soundness_helper :
  forall e env stack is',
    run_instructions (compile e ++ is') env stack =
    run_instructions is' env ((interpret e env) :: stack).
Proof.
  induction e; intros; simpl; trivial.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    rewrite Bool.andb_comm.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    rewrite Bool.orb_comm.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite IHe.
    simpl.
    reflexivity.
Qed.

Theorem soundness :
  forall e env,
    run_instructions (compile e) env [] =
    [interpret e env].
Proof.
  intros.
  Check app_nil_r.
  rewrite <- app_nil_r with (l := (compile e)).
  rewrite soundness_helper.
  simpl. trivial.
Qed.

Definition c_expr := !(!(("x" &&& "y" ||| "z" &&& false) ||| ("x" &&& false ||| ("y" ||| true)))).

Compute [interpret c_expr env0].

Compute compile c_expr.

Compute run_instructions (compile c_expr) env0 [].
