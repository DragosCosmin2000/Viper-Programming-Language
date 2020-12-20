Require Import Arith.
Require Import Ascii.
Require Import Coq.Strings.Byte.
Require Import String.
Local Open Scope string_scope.

(* -------------------- Comments -------------------- *)
Inductive comment : Set :=
| comm : string -> comment.

Notation "/* A */" := (comm A) (at level 99).

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

Definition start_env : Env :=
  fun var => error.

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

Check
  /* "P2: Inlocuirea multiplilor de 3 cu string-ul <multiplu de 3> dintr-un vector" */;'
  "vec" ::= #[ 5, 2, 10, 12, -#20, #"a", #"7", 7, 60 #];'
  for* "it" ::= 0; "it" <' "vec".count'(); "it" ::= "it" +' 1 do*
  {
    if* "vec".get'("it") %' 3 ==' 0 then*
    {
      "vec".insert'(#(#"m", #"u", #"l", #"t", #"i", #"p", #"l", #"u", #" ", #"d", #"e", #" ", #"3"#), "it")
    }
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











