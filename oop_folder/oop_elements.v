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

(* -------------------- Statements -------------------- *)
Add LoadPath "statements_folder".
Require Import statements.

Inductive param :=
| no_param : param
| one_param : variable -> param
| multiple_param : param -> param -> param.

Notation "(( ))" := no_param (format "(( ))", at level 20).
Notation "(( A ))" := (one_param A) (at level 20).
Notation "(( A , B , .. , N ))" := (multiple_param (one_param A) (multiple_param (one_param B) .. (multiple_param (one_param N) no_param).. ) ) (at level 20).

Inductive func :=
| exec_func : string -> param -> Statement -> func
| seq_func : func -> func -> func.

Notation "'def'' A '@' B '@' '{' C '}'" := (exec_func A B C) (at level 20).
Notation " A ;; B" := (seq_func A B) (at level 30).

Inductive init :=
| init_func : param -> Statement -> init.

Notation "'def'' '_' '_' 'init' '_' '_' '@' A '@' '{' B '}'" := (init_func A B ) (at level 20).

Inductive classes :=
| class : string -> init -> func -> classes.

Notation "'class'' A :' B ;;; C" := (class A B C) (at level 15).

Check
class' "abcde":'
  def' _ _ init _ _ @ (("a", "b", "c" )) @
  {
    "a" ::= 2
  } ;;;
  
  def' "suma" @ (( "v")) @ 
  {
    "S" ::= 0;'
    for* "it" ::= 0; "it" <' "v".count'(); "it" ::= "it" +' 1 do*
    {
      "S" ::= "S" +' "v".get'("it")
    }
  };;
  
  def' "produs" @ (( "v")) @ 
  {
    "S" ::= 0;'
    for* "it" ::= 0; "it" <' "v".count'(); "it" ::= "it" +' 1 do*
    {
      "S" ::= "S" +' "v".get'("it")
    }
  }
.