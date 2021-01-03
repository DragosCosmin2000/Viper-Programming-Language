Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import String.
Local Open Scope string_scope.

Compute eqb "asa" "asa".

Inductive lambda_aexp :=
| anum : nat -> lambda_aexp
| aparam : string -> lambda_aexp
| aplus : lambda_aexp -> lambda_aexp -> lambda_aexp.

Inductive Array :=
| empty_array
| array_el : nat -> Array
| array_cons : Array -> Array -> Array.

Coercion array_el : nat >-> Array.

Notation "#[ #]" := empty_array (format "#[ #]", at level 60).
Notation "#[ A #]" := (array_el A) (at level 60).
Notation "#[ A , B , .. , N , M #]" := (array_cons (array_el A) (array_cons (array_el B) .. (array_cons (array_el N) (array_el M))..)) (at level 60).

Check array_cons empty_array (array_el 5).
Check #[ #].
Check #[ 2 #].
Check #[ 3, 6, 8#].

Inductive Params :=
| empty_params
| params_el : string -> Params
| params_cons : Params -> Params -> Params.

Coercion params_el : string >-> Params.

Notation "$( $)" := empty_params (format "$( $)", at level 60).
Notation "$( A $)" := (params_el A) (at level 60).
Notation "$( A , B , .. , N , M $)" := (params_cons (params_el A) (params_cons (params_el B) .. (params_cons (params_el N) (params_el M))..)) (at level 60).

Fixpoint get_element (arguments : Array) (current_index index : nat) : nat :=
  match arguments with
  | empty_array => 1000
  | array_el a => if Nat.eqb current_index index
                  then a
                  else 1000
  | array_cons a1 a2 => if Nat.eqb current_index index
                        then (match a1 with
                             | empty_array => 1000
                             | array_el a' => a'
                             | array_cons a'' a''' => 1000
                             end)
                        else get_element a2 (current_index + 1) index
  end.

Compute get_element (#[ 1, 11, 111, 1111 #]) 0 2.

Fixpoint get_value (param : string) (params : Params) (arguments : Array) (current_index : nat) : nat :=
  match params with
  | empty_params => 1000
  | params_el a => if eqb a param
                   then get_element arguments 0 current_index
                   else 1000
  | params_cons a1 a2 => (match a1 with
                         | empty_params => 1000
                         | params_el a' => if eqb a' param
                                          then get_element arguments 0 current_index
                                          else get_value param a2 arguments (current_index + 1)
                         | params_cons a'' a''' => 1000
                         end)
  end.

Compute get_value ("a") ( $("b", "d", "c", "a", "e" $) ) ( #[2, 4, 3, 1, 5#] ) (0).

Fixpoint aeval_lambda_aexp (params : Params) (arguments : Array) (exp : lambda_aexp) : nat :=
  match exp with
  | anum a => a
  | aparam a => get_value a params arguments 0
  | aplus a1 a2 => (aeval_lambda_aexp params arguments a1) + (aeval_lambda_aexp params arguments a2)
  end.

Definition my_exp := aplus (aparam "b") (aparam "e").

Compute aeval_lambda_aexp ( $("b", "d", "c", "a", "e" $) ) ( #[2, 4, 3, 1, 5#] ) (my_exp).

Inductive Lambda_pairs : Set :=
| basic_pair : Params -> lambda_aexp -> Lambda_pairs.


Definition lambda_Env := string -> Lambda_pairs.

Definition env1 : lambda_Env :=
  fun l_func => basic_pair ($( $)) (anum 1000).

Definition update (env : lambda_Env) (l_func : string) (l_pair : Lambda_pairs) : lambda_Env :=
  fun var' => if eqb var' l_func
              then l_pair
              else (env var').

Definition env2 := update env1 "adunare_3" (basic_pair ($("x", "y", "z"$)) (aplus (aparam "x") (aplus (aparam "y") (aparam "z"))) ).

Compute env2 "adunare_3".

Definition calculate_lambda (lambda_name : string) (l_env : lambda_Env) (arguments : Array) : nat :=
  match (l_env lambda_name) with
  | basic_pair a b => aeval_lambda_aexp a arguments b
  end.

Compute calculate_lambda "adunare_3" env2 ( #[ 3, 4, 5#]).

Notation " '@lambda(' A , B , C )" := (calculate_lambda A B C) (at level 60).

Compute @lambda("adunare_3", env2, (#[ 3, 4, 5#])).
