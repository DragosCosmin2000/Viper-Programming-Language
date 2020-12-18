Require Import Arith.
Require Import Ascii.
Require Import Coq.Strings.Byte.
Require Import String.
Local Open Scope string_scope.

(* -------------------- Comments -------------------- *)
Inductive comment : Set :=
| comm : string -> comment.

Notation "/* A */" := (comm A) (at level 99).

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

(* -------------------- Datatypes for VPL -------------------- *)
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

Notation "#[ #]" := array_nil (format "#[ #]", at level 20).
Notation "#[ A #]" := (array_cons A array_nil) (at level 20).
Notation "#[ A , B , .. , N #]" := (array_cons A (array_cons B .. (array_cons N array_nil)..)) (at level 20).

Inductive Tuple : Set :=
| tuple_nil : Tuple
| tuple_cons : Val -> Tuple -> Tuple.

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
| dict_nil : Dict
| dict_cons : Pair -> Dict -> Dict.

Notation "#{ #}" := dict_nil (format "#{ #}", at level 20).
Notation "#{ A #}" := (dict_cons A dict_nil) (at level 20).
Notation "#{ A , B , .. , N #}" := (dict_cons A (dict_cons B .. (dict_cons N dict_nil)..)) (at level 20).

Compute #{
  #[ #"D", #"r", #"a", #"g", #"o", #"s" #] :# -#9,
  #[ #"A", #"n", #"d", #"r", #"e", #"e", #"a" #] :# 9,
  #[ #"R", #"a", #"r", #"e", #"s" #] :# -#10
#}.

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
              | undef => "undef"
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
              | undef => "undef"
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

(* -------------------- Statements -------------------- *)
Inductive Statement :=
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

Coercion empty_stmt : comment >-> Statement.

Notation "X ::= A" := (assignment X A) (at level 90).
Notation "S ;' S'" := (sequence S S') (at level 97, right associativity).

Notation "'if*' A 'then*' '{' B '}'" := (ifthen A B) (at level 95).
Notation "'if'' A 'then'' '{' B '}' 'else'' C" := (ifthenelse A B C) (at level 95).

Notation "'while'' A 'do'' '{' B '}'" := (while A B) (at level 95).
Notation "'do*' '{' A '}' 'while*' B" := (do_while A B) (at level 95).

Notation "'for'' A ;' B 'do'' '{' C '}'" := (forloop A B C) (at level 95).
Notation "'for'' A ;' B ;' C 'do'' '{' D '}'" := (forloop_firstloop A B C D) (at level 95).

Definition start_env : Env :=
  fun var => undef.

(* Exemplu 1 *)
Check
  /* "P1: Program pentru inversul unui numar." */;'
  /* "Numarul de inversat" */;'
  "v" ::= 1241;'
  /* "Verificam tipul numarului" */;'
  if* typeof$("v" $; start_env$) ==' "natural" then*
  {
    /* "Calculam inversul" */;'
    "aux" ::= 0;'
    while' !'("v" ==' 0) do'
    {
      "aux" ::= ("aux" *' 10 +' "v" %' 10);'
      "v" ::= ("v" /' 10)
    };'
    "v" ::= "aux"
  }
.

Inductive files :=
(* filename and content *)
| text_file : string -> string -> files.

Notation "'file@' A @ B @" := (text_file A B) (at level 1).

Definition file1 := file@"tema1.txt" @ "1. Calculati: a)..."@.

Fixpoint substring (n m : nat) (s : string) : string :=
  match n, m, s with
  | O, O, _ => EmptyString
  | O, S m', EmptyString => s
  | O, S m', String c s' => String c (substring 0 m' s')
  | S n', _, EmptyString => s
  | S n', _, String c s' => substring n' m s'
  end.

Compute (substring 23 2 "abcdefg").











