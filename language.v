
Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.

Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Coercion num: nat >-> ErrorNat.
Coercion boolean: bool >-> ErrorBool.

Inductive AExp :=
  | avar: string -> AExp 
  | anum: ErrorNat -> AExp
  | aplus: AExp -> AExp -> AExp
  | asub: AExp -> AExp -> AExp
  | amul: AExp -> AExp -> AExp 
  | adiv: AExp -> AExp -> AExp 
  | amod: AExp -> AExp -> AExp
  | ainc: AExp -> AExp
  | adec: AExp -> AExp
  | amin: AExp -> AExp -> AExp
  | amax: AExp -> AExp -> AExp
  | apow: AExp -> AExp.

Inductive BExp :=
  | berror
  | btrue
  | bfalse
  | bvar: string -> BExp
  | blt : AExp -> AExp -> BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp.

Inductive Stmt :=
  | nat_decl: string -> AExp -> Stmt 
  | bool_decl: string -> BExp -> Stmt 
  | nat_assign : string -> AExp -> Stmt 
  | bool_assign : string -> BExp -> Stmt 
  | sequence : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt.

Inductive Mem :=
  | mem_default : Mem
  | offset : nat -> Mem. 

Definition Env := string -> Mem.

Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (asub A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).
Notation "++ C" := (ainc C)(at level 50, left associativity).
Notation "-- C" := (adec C)(at level 50, left associativity).
Notation "min'( A , C )" := (amin A C)(at level 47, left associativity).
Notation "max'( A , C )" := (amax A C)(at level 47, left associativity).
Notation "pow'( A )" := (apow A)(at level 47, left associativity).


Notation "A <' B" := (blt A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).

Notation "X :n= A" := (nat_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "'iNat' X ::= A" := (nat_decl X A)(at level 90).
Notation "'iBool' X ::= A" := (bool_decl X A)(at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'fors' ( A ~ B ~ C ) { S }" := (A ;; while B ( S ;; C )) (at level 97).


Reserved Notation "A =[ S ]=> N" (at level 60).
Reserved Notation "B ={ S }=> B'" (at level 70).
Reserved Notation "B ={ S }=> B'" (at level 70).
Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).


Coercion anum: ErrorNat >-> AExp.
Coercion avar: string >-> AExp.


Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_nat : ErrorNat -> Result
  | res_bool : ErrorBool -> Result
  | code : Stmt -> Result. 

Scheme Equality for Result.

Definition check_eq_over_types (t1 : Result)(t2 : Result) : bool :=
  match t1 with
  | err_assign => match t2 with 
                   | err_assign => true
                   | _ => false
                   end
  | err_undecl => match t2 with
                   | err_undecl => true
                   | _ => false
                   end
  | default => match t2 with
                   | default => true
                   | _ => false
                   end
  | res_nat s => match t2 with
                   | res_nat s => true
                   | _ => false
                   end
  | res_bool s => match t2 with 
                   | res_bool s => true
                   | _ => false
                   end
  | code s => match t2 with
                   | code s => true
                   | _ => false
                   end
  end.

Compute (check_eq_over_types (res_nat 1000) (res_nat 100)). 
Compute (check_eq_over_types err_undecl (res_nat 100)). 
Compute (check_eq_over_types err_undecl (code ("x" :n= 4))).