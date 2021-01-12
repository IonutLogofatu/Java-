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
Require Import Notations Logic Datatypes.
Require Decimal Hexadecimal Numeral.
Local Open Scope nat_scope.


Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.


Scheme Equality for ErrorNat.


Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Inductive errString :=
  | error_String : errString
  | newString : string -> errString.

Inductive funParam :=
  | param : string -> funParam.
Scheme Equality for funParam.

Coercion num: nat >-> ErrorNat.
Coercion boolean: bool >-> ErrorBool.
Coercion newString: string >-> errString.
Coercion param : string >-> funParam.

Inductive StringOP:=
  | str_err : errString -> StringOP
  | strConcat : StringOP -> StringOP -> StringOP
  | strCmp : StringOP -> StringOP -> StringOP
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

Definition strlen_fun (s : errString) : ErrorNat :=
match s with 
| error_String => error_nat
| newString str1 => num (String.length str1)
end.

Inductive AExp :=
  | aconst : ErrorNat -> AExp 
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
  | apow: AExp -> AExp -> AExp
  | asqrt: AExp -> AExp
  | strlenStr: StringOP ->AExp.



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
  | bgreather: AExp -> AExp -> BExp
  | begreather: AExp -> AExp -> BExp
  | binneq : AExp -> AExp -> BExp
  | beq : AExp -> AExp -> BExp.


Inductive Stmt :=
  | nat_decl: funParam -> AExp -> Stmt 
  | locNatDecl : funParam -> Stmt
  | bool_decl: funParam -> BExp -> Stmt
  | locBoolDecl : funParam -> Stmt 
  | string_decl: funParam -> StringOP -> Stmt
  | locStringDecl : funParam -> Stmt
  | nat_assign : funParam -> AExp -> Stmt 
  | bool_assign : funParam -> BExp -> Stmt 
  | string_assign : funParam -> StringOP -> Stmt
  | sequence : Stmt -> Stmt -> Stmt
  | whileStmt : BExp -> Stmt -> Stmt
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt
  | SystemOut : StringOP -> Stmt
  | break : Stmt
  | callFun : funParam -> list funParam -> Stmt.

Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_nat : ErrorNat -> Result
  | res_bool : ErrorBool -> Result
  | res_string : StringOP -> Result
  | code : Stmt -> Result. 

Coercion aconst : ErrorNat >-> AExp.

Inductive Glb :=
    | mainDecl : Stmt -> Glb
    | functionDecl : funParam -> list funParam -> Stmt -> Glb
    | sequenceGlb : Glb -> Glb -> Glb
    | natGlb : funParam -> Glb
    | boolGlb : funParam -> Glb
    | stringGlb : funParam -> Glb.

Inductive Types : Type :=
 |error : Types
 |numberType : ErrorNat -> Types
 |booleanType : ErrorBool -> Types
 |stringType : errString -> Types
 |codeType : list funParam ->Stmt -> Types.

Definition eqType (a b: Types) : bool :=
match a,b with
  |error, error => true
  |numberType _, numberType _ => true
  |booleanType _, booleanType _ =>true
  |stringType _, stringType _ =>true
  |codeType _ _, codeType _ _ =>true
  | _, _ => false
end.

Coercion avar : string >-> AExp.
Coercion bvar : string >-> BExp.
Coercion strVar : string >-> StringOP.
Coercion anum: ErrorNat >-> AExp.


Notation "String.concat( A , B )" :=(strConcat A B)(at level 49, left associativity).
Notation "Str.lenght( A )" :=(strlenStr A)(at level 47, left associativity).
Notation "Str.cmp( A , B )" :=(strCmp A B)(at level 47, left associativity).

Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (asub A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).
Notation "++' C" := (ainc C)(at level 50, left associativity).
Notation "--' C" := (adec C)(at level 50, left associativity).
Notation "min'( A , C )" := (amin A C)(at level 47, left associativity).
Notation "max'( A , C )" := (amax A C)(at level 47, left associativity).
Notation "pow'( A , C )" := (apow A C)(at level 47, left associativity).
Notation "sqrt( A )" :=(asqrt A)(at level 47, left associativity).  


Notation "A <' B" := (blt A B) (at level 51, left associativity).
Notation "A >' B" := (bgreather A B) (at level 51, left associativity).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).
Notation "A <=' B" := (belt A B)(at level 51, left associativity).
Notation "A >=' B" := (begreather A B)(at level 51, left associativity).
Notation "A !=' B" := (binneq A B)(at level 55, left associativity).
Notation "A ==' B" := (beq A B)(at level 54, left associativity).


Notation "X :n= A" := (nat_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "X :s= A" := (string_assign X A)(at level 90).
Notation "'LNat' X" :=(locNatDecl X)(at level 90).
Notation "'GNat' X" := (natGlb X)(at level 90).
Notation "'Nat' X ::= A" := (nat_decl X A)(at level 90).
Notation "'LBoolean' X" :=(locBoolDecl X)(at level 90).
Notation "'Gboolean' X" := (boolGlb X)(at level 90).
Notation "'Boolean' X ::= A" := (bool_decl X A)(at level 90).
Notation "'LString' X" :=(locStringDecl X)(at level 90).
Notation "'GSTring' X" :=(stringGlb X)(at level 90).
Notation "'STring' X ::= A" := (string_decl X A)(at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "S1 .' S2" := (sequenceGlb S1 S2)(at level 93, right associativity).

Notation "'fors' ( A ;' B ;' C ) { S }" := (A ;; whileStmt B ( S ;; C )) (at level 97).
Notation "'If' B 'Then' A 'End'" :=(ifthen B A)(at level 97).
Notation "'If' B 'Then' S1 'Else' S2 'End'" := (ifthenelse B S1 S2) (at level 97).
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
Definition State := funParam -> nat.
Inductive LayerMemory := 
| pair : State -> Memory -> nat -> State -> Memory -> nat -> LayerMemory.
Notation "< S , M , N >-< GS , GM , GN >" := (pair S M N GS GM GN) (at level 0).

Definition localCheck (m : LayerMemory) (v : funParam) : bool :=
match m with
| pair s m _ gs gm _ => if (eqType ( m (s v) ) error) 
                              then false else true
end.

Definition getVal (m : LayerMemory) (v : funParam) : Types :=
match m with
| pair s mem _ gs gm _ => if (localCheck m v) 
                              then mem(s v) else gm(gs v)
end.

Definition getLocalMaxPos (m : LayerMemory) : nat :=
match m with
| pair _ _ val _ _ _  => val
end.

Definition getGlobalMaxPos (m : LayerMemory) : nat :=
match m with
| pair _ _ _ _ _ val  => val
end.

Definition getLocalAdress (m:LayerMemory) (v : funParam) : nat :=
match m with
| pair s _ _ _ _ _ => s v
end.

Definition getAdress (m:LayerMemory) (v:funParam) : nat :=
match m with
| pair st _ _ gst _ _ => if (eqb (st v) 0%nat) then gst v else st v
end.

Definition getGlobalAdress (m:LayerMemory) (v:funParam) : nat :=
match m with
| pair _ _ _ s _ _ => s v
end.
Definition updateState (st : State) (v : funParam) (n : nat) : State:= 
fun x => if (funParam_beq x v) then n else st x.

Definition updateMemory (m : Memory) (n : nat) (val : Types) : Memory :=
fun n' => if (eqb n' n) then val else m n'. 

Definition updateLocal (M : LayerMemory) (V : funParam) (T : Types) (pos : nat) : LayerMemory :=
match M with
| pair st mem max gst gmem gmax => if (andb (eqb pos (getLocalAdress M V) ) (eqb pos 0) ) then
       pair st mem max gst gmem gmax else
       pair (updateState st V pos) (updateMemory mem pos T) 
      (if (ltb pos max) then max else add max 1) gst gmem gmax
end.

Definition updateGlobal (M : LayerMemory) (V : funParam) (T : Types) (pos : nat) : LayerMemory :=
match M with
| pair st mem max gst gmem gmax => if (andb (eqb pos (getGlobalAdress M V) ) (eqb pos 0) ) then
       pair st mem max gst gmem gmax else
       pair st mem max (updateState gst V pos) (updateMemory gmem pos T) 
      (if (ltb pos gmax) then gmax else add gmax 1)
end.

Definition updateLocalAtAdress (M : LayerMemory) (addr : nat) (T : Types): LayerMemory :=
match M with
| pair st mem max gst gmem gmax => if (eqb addr 0) then
       pair st mem max gst gmem gmax else
       pair st (updateMemory mem addr T) max gst gmem gmax
end.

Definition updateGlobalAtAdress (M : LayerMemory) (addr : nat) (T : Types): LayerMemory :=
match M with
| pair st mem max gst gmem gmax => if (eqb addr 0) then
       pair st mem max gst gmem gmax else
       pair st mem max gst (updateMemory gmem addr T) gmax
end.

Definition updateAtAdress (M : LayerMemory) (isL : bool) (addr : nat) (T : Types) : LayerMemory :=
match M with
| pair st mem max gst gmem gmax => if isL
                                         then updateLocalAtAdress M addr T
                                         else updateGlobalAtAdress M addr T
end.

Definition mem_null : Memory := fun n => error.
Definition state_null : State := fun x => 0.
Definition stack_null := pair state_null mem_null 1 state_null mem_null 1.

Definition Plus (a b : Types) :=
match a, b with
| numberType a', numberType b' => match a', b' with
                        | num n1, num n2 => numberType (n1 + n2)
                        | _, _ => numberType error_nat
                        end
| _ , _ => error
end.

Definition Minus (a b : Types) :=
match a, b with
| numberType a', numberType b' => match a', b' with
                        | num n1, num n2 => if(leb n1 n2)then numberType error_nat else numberType (n1 - n2)
                        | _, _ => numberType error_nat
                        end
| _ , _ => error
end.

Definition Sqrt (a : Types) :=
match a with
| numberType a' => match a' with
                        | num n1 => if(eqb n1 0)then numberType error_nat else numberType (sqrt n1)
                        | _ => numberType error_nat
                        end
| _ => error
end.

Definition Multiplied (a b : Types) :=
match a, b with
| numberType a', numberType b' => match a', b' with
                        | num n1, num n2 => numberType (n1 * n2)
                        | _, _ => numberType error_nat
                        end
| _ , _ => error
end.

Definition Divide (a b : Types) :=
match a, b with
| numberType a', numberType b' => match a', b' with
                        | num n1, num n2 =>if(eqb n2 0) then numberType error_nat else numberType (n1 * n2)
                        | _, _ => numberType error_nat
                        end
| _ , _ => error
end.

Definition Mod (a b : Types) :=
match a, b with
| numberType a', numberType b' => match a', b' with
                        | num n1, num n2 =>if(eqb n2 0) then numberType error_nat else numberType (modulo n1 n2)
                        | _, _ => numberType error_nat
                        end
| _ , _ => error
end.

Definition Power (a b : Types) :=
match a, b with
| numberType a', numberType b' => match a', b' with
                        | num n1, num n2 =>if(ltb n2 0) then numberType error_nat else numberType (pow n1 n2)
                        | _, _ => numberType error_nat
                        end
| _ , _ => error
end.

Definition Strcat (s1 s2 : Types) := 
match s1, s2 with
| stringType s1', stringType s2' => stringType ( strConcat_fun s1' s2' )
| _, _ => error
end.

Definition Strcmp (s1 s2 : Types) := 
match s1, s2 with
| stringType s1', stringType s2' => match s1', s2' with
                        |newString n1, newString n2 =>if(String.eqb n1 n2 ) then booleanType true else booleanType false
                        |_,_ =>booleanType false
                        end
| _, _ =>booleanType false
end.


Definition Strlen (a : Types) :=
match a with
| stringType a' => numberType ( strlen_fun a' )
| _ => error
end.

Definition Comp (type : string) (a b : Types) : Types := 
match a, b with
| numberType a', numberType b' 
          => match a', b' with
          | num  m, num  n
                        => match type with
                           | "lessthan" => booleanType (ltb m n)
                           | "lessequal" => booleanType (leb m n)
                           | "greatherthan" => booleanType (ltb n n)
                           | "greatherequal" => booleanType (leb n n)
                           | "equal" => booleanType (eqb m n)
                           | _ => booleanType (eqb m n)
                           end
          | _, _ => booleanType error_bool 
          end
| _, _ => error
end.

Definition newOrB (a b : Types) : Types := 
match a, b with
| booleanType a', booleanType b' => match a', b' with
                              | boolean m, boolean n => booleanType (orb m n)
                              | _, _ => booleanType error_bool
                              end
| _, _ => error
end.

Reserved Notation "STR '=S[' St ']S>' N" (at level 60).
Inductive seval : StringOP -> LayerMemory -> Types -> Prop :=
| s_var : forall s sigma, strVar s =S[ sigma ]S> getVal sigma s
| s_concat : forall s1 s2 sigma s st1 st2,
    s1 =S[ sigma ]S> st1 ->
    s2 =S[ sigma ]S> st2 ->
    s = Strcat st1 st2 ->
    String.concat( s1 , s2 ) =S[ sigma ]S> s
| s_cmp : forall s1 s2  sigma b st1 st2,
    s1 =S[ sigma ]S> st1 ->
    s2 =S[ sigma ]S> st2 ->
    b = Strcmp st1 st2 ->
    Str.cmp( s1 , s2 ) =S[ sigma ]S> b
where "STR '=S[' St ']S>' N" := (seval STR St N).



Reserved Notation "B '=B[' S ']B>' B'" (at level 70).
Reserved Notation "A '=A[' S ']A>' N" (at level 60).

Inductive aeval : AExp -> LayerMemory -> Types -> Prop :=
| e_const : forall n sigma, aconst n =A[ sigma ]A> numberType n
| e_var : forall v sigma, avar v =A[ sigma ]A> getVal sigma v
| e_add : forall a1 a2 i1 i2 sigma n,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    n = Plus i1 i2 ->
    a1 +' a2 =A[ sigma ]A> n
| e_sub : forall a1 a2 i1 i2 sigma n,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    n = Minus i1 i2 ->
    a1 -' a2 =A[ sigma ]A> n
| e_times : forall a1 a2 i1 i2 sigma n,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    n = Multiplied  i1 i2 ->
    a1 *' a2 =A[ sigma ]A> n
| e_divided : forall a1 a2 i1 i2 sigma n,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    n = Divide  i1 i2 ->
    a1 /' a2 =A[ sigma ]A> n
| e_div_rest : forall a1 a2 i1 i2 sigma n,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    n = Mod i1 i2 ->
    a1 %' a2 =A[ sigma ]A> n
| e_power : forall a1 a2 i1 i2 sigma n,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    n = Power i1 i2 ->
    pow'( a1 , a2) =A[ sigma ]A> n
| e_sqrt :forall a1 sigma s1 n,
    a1 =A[ sigma ]A> s1 ->
    n = Sqrt s1 ->
    sqrt( a1 ) =A[ sigma ]A> n
| e_strlen : forall a1 sigma s1 n,
    a1 =S[ sigma ]S> s1 ->
    n = Strlen s1 ->
    Str.lenght( a1 ) =A[ sigma ]A> n
where "A '=A[' S ']A>' N" := (aeval A S N)
with beval : BExp -> LayerMemory -> Types -> Prop :=
| e_true : forall sigma, btrue =B[ sigma ]B> booleanType  true
| e_false : forall sigma, bfalse =B[ sigma ]B> booleanType  false
| e_bvar : forall v sigma, bvar v =B[ sigma ]B> getVal sigma v
| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    b = Comp "lessthan" i1 i2 ->
    a1 <' a2 =B[ sigma ]B> b
| e_lessthan_eq : forall a1 a2 i1 i2 sigma b,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    b = Comp "lessequal" i1 i2 ->
    a1 <=' a2 =B[ sigma ]B> b
| e_greaterthan : forall a1 a2 i1 i2 sigma b,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    b = Comp "greatherthan" i1 i2 ->
    a1 >' a2 =B[ sigma ]B> b
| e_greaterthan_eq : forall a1 a2 i1 i2 sigma b,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    b = Comp "greatherequal" i1 i2 ->
    a1 >=' a2 =B[ sigma ]B> b
| e_nottrue : forall b sigma,
    b =B[ sigma ]B> booleanType true ->
    (!' b) =B[ sigma ]B> booleanType false
| e_notfalse : forall b sigma,
    b =B[ sigma ]B> booleanType false ->
    (!' b) =B[ sigma ]B> booleanType true
| e_andtrue : forall b1 b2 sigma t,
    b1 =B[ sigma ]B> booleanType true ->
    b2 =B[ sigma ]B> t ->
    b1 &&' b2 =B[ sigma ]B> t
| e_andfalse : forall b1 b2 sigma,
    b1 =B[ sigma ]B>booleanType false ->
    b1 &&' b2 =B[ sigma ]B> booleanType false
| e_or : forall b1 b2 sigma t t1 t2,
    b1 =B[ sigma ]B> t1 ->
    b2 =B[ sigma ]B> t2 ->
    t = newOrB t1 t2 ->
    b1 ||' b2 =B[ sigma ]B> t
| e_equality : forall a1 a2 i1 i2 sigma b,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    b = Comp "equal" i1 i2 ->
    a1 ==' a2 =B[ sigma ]B> b
| e_inequality : forall a1 a2 i1 i2 sigma b,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    b = Comp "inequal" i1 i2 ->
    a1 !=' a2 =B[ sigma ]B> b
where "B '=B[' S ']B>' B'" := (beval B S B').

Definition getStmt (code : Types) : Stmt :=
match code with
| codeType _ stmt  => stmt
| _ => break
end.

Definition getArgs (cod : Types) : list funParam :=
match cod with
| codeType args _ => args
| _ => nil
end.

Definition MergeMemory (l g: LayerMemory) : LayerMemory :=
match l, g with
| pair st1 mem1 max1 gst1 gmem1 gmax1 ,
    pair st2 mem2 max2 gst2 gmem2 gmax2 => pair st1 mem1 max1 gst2 gmem2 gmax2
end.

Definition DeleteLocal (m:LayerMemory ) : LayerMemory :=
match m with 
| pair st mem max gst gmem gmax => pair state_null mem_null 1 gst gmem gmax
end.

Fixpoint NewLocalStack (l1 l2 : list funParam) (m save:LayerMemory): LayerMemory :=
match l1, l2 with
| nil , nil => save
| x :: nil, y :: nil => updateLocal save y (getVal m x) (getLocalMaxPos save)
| x :: l1', y :: l2' => NewLocalStack l1' l2' m (updateLocal save y (getVal m x) (getLocalMaxPos save) )
| _, _ => DeleteLocal m
end.

Reserved Notation " S -[ M1 , S1 ]=> M2 , S2" (at level 60).
Inductive stmt_eval : Stmt -> LayerMemory -> LayerMemory -> LayerMemory -> LayerMemory -> Prop :=
| st_secv : forall s1 s2 sigma sigma1 sigma2 save save',
   ( s1 )-[ sigma , save ]=> sigma1 , save ->
   ( s2 )-[ sigma1 , save ]=> sigma2 , save' ->
   ( s1 ;; s2 )-[ sigma , save ]=> sigma2 , save'
| st_natDecl : forall s a val sigma sigma1 save,
    val =A[ sigma ]A> a ->
    sigma1 = updateLocal sigma s a (getLocalMaxPos sigma) ->
    ( Nat s ::= val )-[ sigma , save ]=> sigma1 , save
| st_bool : forall s b val sigma sigma1 save,
    val =B[ sigma ]B> b ->
    sigma1 = updateLocal sigma s b (getLocalMaxPos sigma) ->
    ( Boolean s ::= val)-[ sigma , save ]=> sigma1 , save
| st_string : forall s val sigma sigma1 str save,
    val =S[ sigma ]S> str ->
    sigma1 = updateLocal sigma s str (getLocalMaxPos sigma) ->
    ( STring s ::= val )-[ sigma , save ]=> sigma1 , save
| st_asignat : forall s a val sigma sigma1 save,
    eqType  (getVal sigma s) (numberType  0) = true ->
    val =A[ sigma ]A> a ->
    sigma1 = updateAtAdress sigma (localCheck sigma s) (getAdress sigma s) a ->
    ( s :n= val )-[ sigma , save ]=> sigma1 , save
| st_asignboolean : forall s b val sigma sigma1 save,
    eqType  (getVal sigma s) (booleanType  false) = true ->
    val =B[ sigma ]B> b ->
    sigma1 = updateAtAdress sigma (localCheck sigma s) (getAdress sigma s) b ->
    ( s :b= val )-[ sigma , save ]=> sigma1 , save
| st_asigString : forall s val sigma sigma1 str save,
    eqType  (getVal sigma s) (stringType "" ) = true ->
    val =S[ sigma ]S> str ->
    sigma1 = updateAtAdress sigma (localCheck sigma s) (getAdress sigma s) str  ->
    ( s :s= val )-[ sigma , save ]=> sigma1 , save
| st_iffalse : forall b s1 sigma save,
    b =B[ sigma ]B> booleanType false ->
    ( ifthen b s1 )-[ sigma , save ]=> sigma , save
| st_iftrue : forall b s1 sigma sigma1 save,
    b =B[ sigma ]B> booleanType true ->
    ( s1 )-[ sigma , save ]=> sigma1 , save ->
    ( ifthen b s1 )-[ sigma , save ]=> sigma1 , save
| st_ifthenElseFalse : forall b s1 s2 sigma sigma2 save,
    b =B[ sigma ]B> booleanType false ->
    ( s2 )-[ sigma , save ]=> sigma2 , save ->
    ( ifthenelse b s1 s2 )-[ sigma , save ]=> sigma2 , save
| st_ifthenElseTrue : forall b s1 s2 sigma sigma1 save,
    b =B[ sigma ]B> booleanType true ->
    ( s1 )-[ sigma , save ]=> sigma1 , save ->
    ( ifthenelse b s1 s2 )-[ sigma , save ]=> sigma1 , save
| st_whilefalse : forall b s sigma save,
    b =B[ sigma ]B> booleanType false ->
    ( whileStmt b s )-[ sigma , save ]=> sigma , save
| st_whiletrue : forall b s sigma sigma1 save,
    b =B[ sigma ]B> booleanType true ->
    ( s ;; whileStmt b s )-[ sigma , save ]=> sigma1 , save ->
    ( whileStmt b s )-[ sigma , save]=> sigma1 , save
| st_break : forall sigma sigma' save save',
    save' = stack_null ->
    sigma' = MergeMemory save sigma->
    ( break )-[sigma, save]=> sigma', save'
| st_callFun : forall s L args stmt sigma sigma' sigma1 save,
    args = getArgs (getVal sigma s ) ->
    length L = length args ->
    sigma' = NewLocalStack L args sigma (DeleteLocal sigma)->
    stmt = getStmt (getVal sigma s ) ->
    ( stmt )-[ sigma' , sigma]=> sigma1 , save ->
    ( callFun s L )-[ sigma , save ]=> sigma1 , save
where "S -[ M1 , S1 ]=> M2 , S2" := (stmt_eval S M1 S1 M2 S2).

Reserved Notation "G -{ M1 }=> M2" (at level 60).
Inductive glb_eval : Glb -> LayerMemory -> LayerMemory -> Prop :=
| glb_secv : forall s1 s2 sigma sigma1 sigma2,
   ( s1 )-{ sigma }=> sigma1 ->
   ( s2 )-{ sigma1 }=> sigma2 ->
   ( s1 .' s2 )-{ sigma }=> sigma2
| glb_nat : forall s sigma sigma1,
  sigma1 = updateGlobal sigma s (numberType 0) (getGlobalMaxPos sigma) ->
  ( GNat s )-{ sigma }=> sigma1
| glb_bool : forall s sigma sigma1,
  sigma1 = updateGlobal sigma s (booleanType false) (getGlobalMaxPos sigma) ->
  ( Gboolean s )-{ sigma }=> sigma1
| glb_string : forall s sigma sigma1,
  sigma1 = updateGlobal sigma s (stringType "" ) (getGlobalMaxPos sigma) ->
  ( GSTring s )-{ sigma }=> sigma1
| glb_funMain : forall stmt sigma sigma1 save,
  save = stack_null ->
  ( stmt )-[ sigma , save ]=> sigma1 , save->
  ( mainDecl  stmt )-{ sigma }=> sigma1
| glb_function : forall s L  stmt sigma sigma1,
  sigma1 = updateGlobal sigma s (codeType L stmt) (getGlobalMaxPos sigma) ->
  ( functionDecl s L stmt )-{ sigma }=> sigma1
where "G -{ M1 }=> M2" := (glb_eval G M1 M2).

Example ex1 : exists stack', ( Boolean "x" ::= bfalse ;; "x" :b= btrue )-[ stack_null , stack_null ]=> stack' , stack_null
    /\ getVal stack' "x" = booleanType true.
Proof.
  eexists. 
  split.
  *eapply st_secv.
  +eapply st_bool.
  -eapply e_false.
  -unfold updateLocal. simpl. trivial.
  +eapply st_asignboolean.
  -simpl. trivial. 
  -eapply e_true.
  -unfold updateAtAdress. simpl. trivial.
  *simpl. unfold updateMemory. simpl. trivial.
Qed.

Definition testFunct :=
   GNat "x" .' 
   public_void "test" (("m")){
    "x" :n= "m" -' 20;;
    break
  }.'
  public_void main(){
     "x" :n= 45 ;;
     fun "test" (("x"));;
     break
  }.

Example ex2: exists stack', ( testFunct )-{ stack_null }=> stack'.
Proof.
   eexists.  
  -unfold testFunct. eapply glb_secv.
    + eapply glb_nat. unfold updateGlobal. simpl. trivial.
    + eapply glb_secv.
      ++ eapply glb_function. unfold updateGlobal. simpl. trivial.
      ++ eapply glb_funMain. trivial.
        ** eapply st_secv.
          ***eapply st_asignat. simpl. trivial. 
            eapply e_const. unfold updateAtAdress. simpl. trivial.
          *** eapply st_secv.
          ****eapply st_callFun; simpl; trivial.
             eapply st_secv.
             --eapply st_asignat; eauto.
              eapply e_sub. eapply e_var. eapply e_const. eauto.
            --eapply st_break; eauto.
          ****eapply st_break; eauto.
Qed.
