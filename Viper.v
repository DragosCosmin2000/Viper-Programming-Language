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

(* I/O sim try *)
Definition files := string -> string.
(* filename and content *)

Definition current_files : files :=
  fun x => "".

Definition update (f : files)
           (filename : string) (new_content : string) : files :=
  fun x => if (eqb filename x)
              then new_content
              else (f x).

Notation "'write' '((' A , B , C '))'" := (update A B C) (at level 1).

Definition newfile := write((current_files, "input.txt", "10 5 6 12 33 3")).

Compute newfile "input.txt".

(* Lambda try *)
Notation " 'lambda(' A , B , C ')' :::= P " := (fun A B C => P) (at level 12).

Definition xw := lambda(a, b, c) :::= (a + b + c).