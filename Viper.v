Require Import Arith.
Require Import Ascii.
(*Require Import Bool.*)
Require Import Coq.Strings.Byte.

(* ---------- Datatypes for VPL ---------- *)
Inductive Val : Set :=
(* for errors *)
| error : Val
(* vars value after declaration *)
| undef : Val
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
| array_cons : Val -> Array -> Array.

Notation "#[ #]" := array_nil (format "#[ #]").
Notation "#[ A #]" := (array_cons A array_nil) (at level 20).
Notation "#[ A , B , .. , N #]" := (array_cons A (array_cons B .. (array_cons N array_nil)..)) (at level 20).

Inductive Tuple : Set :=
| tuple_nil : Tuple
| tuple_cons : Val -> Tuple -> Tuple.

Notation "#( #)" := tuple_nil (format "#( #)").
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
| pair : Pair_Element -> Val -> Pair.

Notation " A : B " := (pair A B) (at level 1).

Inductive Dict : Set :=
| dict_nil : Dict
| dict_cons : Pair -> Dict -> Dict.

Notation "#{ #}" := dict_nil (format "#{ #}").
Notation "#{ A #}" := (dict_cons A dict_nil) (at level 20).
Notation "#{ A , B , .. , N #}" := (dict_cons A (dict_cons B .. (dict_cons N dict_nil)..)) (at level 20).

(*Compute #{
  #[ #"D", #"r", #"a", #"g", #"o", #"s" #] : -#9,
  #[ #"A", #"n", #"d", #"r", #"e", #"e", #"a" #] : 9,
  #[ #"R", #"a", #"r", #"e", #"s" #] : -#10
#}.*)







