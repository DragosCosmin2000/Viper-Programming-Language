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
Notation "-# A" := (negative A) (at level 1).
Notation "# A" := (char A) (at level 1).

(* ---------- Collections ---------- *)
Inductive Array : Set :=
(* '\0' *)
| array_nil : Array
| array_el : Val -> Array
| array_cons : Array -> Array -> Array.

Coercion array_el : Val >-> Array.

Check 2.
Notation "#[ #]" := array_nil (format "#[ #]", at level 20).
Notation "#[ A #]" := (array_cons A array_nil) (at level 20).
Notation "#[ A , B , .. , N #]" := (array_cons A (array_cons B .. (array_cons N array_nil)..)) (at level 20).

Inductive Tuple : Set :=
(* '\0' *)
| tuple_nil : Tuple
| tuple_el : Val -> Tuple
| tuple_cons : Tuple -> Tuple -> Tuple.

Coercion tuple_el : Val >-> Tuple.

Notation "#( #)" := tuple_nil (format "#( #)", at level 20).
Notation "#( A #)" := (tuple_cons A tuple_nil) (at level 20).
Notation "#( A , B , .. , N #)" := (tuple_cons A (tuple_cons B .. (tuple_cons N tuple_nil)..)) (at level 20).

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

Notation " A :# B " := (pair A B) (at level 1).

Inductive Dict : Set :=
(* '\0' *)
| dict_nil : Dict
| dict_cons : Pair -> Dict -> Dict.

Notation "#{ #}" := dict_nil (format "#{ #}", at level 20).
Notation "#{ A #}" := (dict_cons A dict_nil) (at level 20).
Notation "#{ A , B , .. , N #}" := (dict_cons A (dict_cons B .. (dict_cons N dict_nil)..)) (at level 20).


(* ---------- Examples ---------- *)
  (* Empty array *)
Check #[ #].
  (* Also, that's a string *)
Check #[ #"H", #"e", #"l", #"l", #"o", #"!"#].
  (* 2D array *)
Check #[ 
#[1, 4, 7#],
#[2, 5, 8#],
#[3, 6, 9#]
#].

  (* Tuple *)
Check #( 1, -#1, 25, true, #"a", #"b", #(1, 2, 3#), #"c", 16#).

  (* Dict *)
Check #{
  #[ #"D", #"r", #"a", #"g", #"o", #"s" #] :# -#9,
  #[ #"A", #"n", #"d", #"r", #"e", #"e", #"a" #] :# 9,
  #[ #"R", #"a", #"r", #"e", #"s" #] :# -#10
#}.