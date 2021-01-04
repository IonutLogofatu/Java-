Require Import Strings.String.
Delimit Scope string_scope with string.
Require Import PeanoNat Le Gt Minus Bool Lt.
Scheme Equality for string.
Local Open Scope string_scope.
Require Import Coq.Strings.Byte.
Local Open Scope list_scope.
Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Nat.
Require Setoid.
Set Implicit Arguments.
Require Import Coq.Lists.List.
Open Scope list_scope.


Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Inductive errString :=
  | error_String : errString
  | newString : string -> errString.

Inductive funParam :=
  | param : string -> funParam.


Coercion num: nat >-> ErrorNat.
Coercion boolean: bool >-> ErrorBool.
Coercion newString: string >-> errString.
Coercion param : string >-> funParam.

Inductive StringOP:=
  | str_err : errString -> StringOP
  | strConcat : errString -> errString -> StringOP
  | strCmp : errString -> errString -> StringOP
  | strVar : string -> StringOP.

Definition strConcat_fun (s1 s2: errString) : errString:=
match s1, s2 with
   |error_String, _ => error_String
   |_, error_String => error_String
   |newString a, newString b => newString (a ++ b)
 end.

Definition strCmp_fun (s1 s2: errString) : ErrorBool:=
match s1, s2 with
   |error_String, _ => error_bool
   |_, error_String => error_bool
   |newString a, newString b => boolean (String.eqb a b)
 end.

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
  | apow: AExp -> AExp
  | asqrt: AExp -> AExp
  | strlenStr: errString ->AExp.



Inductive BExp :=
  | berror
  | btrue
  | bfalse
  | bvar: string -> BExp
  | bnum : ErrorBool -> BExp
  | blt : AExp -> AExp -> BExp
  | belt : AExp -> AExp -> BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp
  | bgreather: BExp -> BExp -> BExp
  | begreather: BExp -> BExp -> BExp
  | binneq : AExp -> AExp -> BExp
  | beq : AExp -> AExp -> BExp.


Inductive Stmt :=
  | nat_decl: string -> AExp -> Stmt 
  | locNatDecl : string -> Stmt
  | bool_decl: string -> BExp -> Stmt
  | locBoolDecl : string -> Stmt 
  | string_decl: string -> StringOP -> Stmt
  | locStringDecl : string -> Stmt
  | nat_assign : string -> AExp -> Stmt 
  | bool_assign : string -> BExp -> Stmt 
  | string_assign : string -> StringOP -> Stmt
  | sequence : Stmt -> Stmt -> Stmt
  | whileStmt : BExp -> Stmt -> Stmt
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt
  | SystemOut : StringOP -> Stmt
  | break : Stmt
  | callFun : string -> list funParam -> Stmt.

Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_nat : ErrorNat -> Result
  | res_bool : ErrorBool -> Result
  | res_string : StringOP -> Result
  | code : Stmt -> Result. 



Inductive Glb :=
    | mainDecl : Stmt -> Glb
    | functionDecl : string -> list funParam -> Stmt -> Glb
    | sequenceGlb : Glb -> Glb -> Glb
    | natGlb : string -> Glb
    | boolGlb : string -> Glb
    | stringGlb : string -> Glb.

Inductive Types : Type :=
 |error : Types
 |numberType : ErrorNat -> Types
 |booleanType : ErrorBool -> Types
 |stringType : errString -> Types
 |codeType : Stmt -> Types.

Definition eqType (a b: Types) : bool :=
match a,b with
  |error, error => true
  |numberType _, numberType _ => true
  |booleanType _, booleanType _ =>true
  |stringType _, stringType _ =>true
  |codeType _, codeType _ =>true
  | _, _ => false
end.

Coercion avar : string >-> AExp.
Coercion bvar : string >-> BExp.
Coercion strVar : string >-> StringOP.
Coercion anum: ErrorNat >-> AExp.


Notation "String.concat( A , B )" :=(strConcat A B)(at level 49, left associativity).
Notation "Str.lenght( A )" :=(strlenStr A)(at level 47, left associativity).

Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (asub A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).
Notation "++' C" := (ainc C)(at level 50, left associativity).
Notation "--' C" := (adec C)(at level 50, left associativity).
Notation "min'( A , C )" := (amin A C)(at level 47, left associativity).
Notation "max'( A , C )" := (amax A C)(at level 47, left associativity).
Notation "pow'( A )" := (apow A)(at level 47, left associativity).
Notation "Math.sqrt( A )" :=(asqrt A)(at level 47, left associativity).  


Notation "A <' B" := (blt A B) (at level 70).
Notation "A >' B" := (bgreather A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).
Notation "A <=' B" := (belt A B)(at level 71, left associativity).
Notation "A >=' B" := (begreather A B)(at level 71, left associativity).
Notation "A !=' B" := (binneq A B)(at level 72, left associativity).
Notation "A ==' B" := (beq A B)(at level 72, left associativity).


Notation "X :n= A" := (nat_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "X :s= A" := (string_assign X A)(at level 90).
Notation "'LNat' X" :=(locNatDecl X)(at level 90).
Notation "'GNat' X" := (natGlb X)(at level 90).
Notation "'Nat' X ::= A" := (nat_decl X A)(at level 90).
Notation "'LBoolean' X" :=(locBoolDecl X)(at level 90).
Notation "'Gboolean' X" := (boolGlb X)(at level 90).
Notation "'boolean' X ::= A" := (bool_decl X A)(at level 90).
Notation "'LString' X" :=(locStringDecl X)(at level 90).
Notation "'GSTring' X" :=(stringGlb X)(at level 90).
Notation "'STring' X ::= A" := (string_decl X A)(at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "S1 .' S2" := (sequenceGlb S1 S2)(at level 93, right associativity).

Notation "'fors' ( A ;' B ;' C ) { S }" := (A ;; whileStmt B ( S ;; C )) (at level 97).
Notation "'If'( B ) 'then' { A }'End'" :=(ifthen B A)(at level 97).
Notation "'If'( B ) 'then' { S1 }'Else'{ S2 }'End'" := (ifthenelse B S1 S2)(at level 97).
Notation "'while(' B '){' A '}'" := (whileStmt B A)(at level 95).
Notation "System.out.println( S )" := (SystemOut S)(at level 98).
Notation "'fun' S ()" := (callFun S nil)(at level 85).
Notation "'fun' S (( A1 , .. , An ))" := (callFun S (cons (param A1) .. (cons (param An) nil) .. ) ) (at level 85).

Notation "'public_void' 'main()' { S }" := (mainDecl S)(at level 98).
Notation "'public_void' N (){ S }" := (functionDecl N nil S)(at level 98).
Notation "'public_void' N ( A ){ S }" := (functionDecl N A S)(at level 98).
Notation "'public_void' N (( A1 , .. , An )){ S }" := (functionDecl N (cons (param A1) .. (cons (param An) nil) .. ) S)(at level 98).


Check 
  public_void "test" (("test1")){
    System.out.println( "Asta este un test" )
  }.

Check
  public_void "test" (){
     System.out.println( "Asta este un test" )
  }.'
  GNat "x".'
  GSTring "TestGlobal".'
  public_void main(){
     "TestGlobal" :s= "bine ai venit";;
     "x" :n= 1 +' 10;;
     LNat "n";;
     "n" :n= 10;;
     System.out.println( "TestGlobal" );;
     System.out.println( "x" );;
     fun "test" ()
  }.


Reserved Notation "A =[ S ]=> N" (at level 60).
Reserved Notation "B ={ S }=> B'" (at level 70).
Reserved Notation "B ={ S }=> B'" (at level 70).
Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).


Inductive Mem :=
  | mem_default : Mem
  | offset : nat -> Mem. 

Definition Env := string -> Mem.


Definition Memory := nat -> Types.
Definition State := ErrorNat -> nat.
Inductive MemoryLayer := 
| pair : State -> Memory -> nat -> State -> Memory -> nat -> MemoryLayer.
Notation "<< S , M , N >>-<< GS , GM , GN >>" := (pair S M N GS GM GN) (at level 0).







