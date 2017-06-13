Require Import List
               NArith
               Bedrock.Word
               Fiat.Common
               Fiat.Computation.Core.
(*               Fiat.BinEncoders.Env.Common.Notations*)
(*               Fiat.BinEncoders.Env.Common.Transformer*)
(*               Fiat.BinEncoders.Env.Common.Specs.*)
             (*  Fiat.BinEncoders.Env.BinLib.Core. *)
Import ListNotations.
Local Open Scope N_scope.

Notation byte := (word 8).
Notation byteString := (list byte).

(*most significant it b8*)
Definition bWord (b8 b7 b6 b5 b4 b3 b2 b1 : bool) :=
  (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 (WS b8 WO)))))))).
  
Fixpoint bsLength (bs : byteString) : nat := 
  match bs with
    | []     => O
    | h :: t => (1%nat + (bsLength t))%nat
  end.

Fixpoint NbsLength (bs : byteString) : N :=
  match bs with
    | []     => N0
    | h :: t => 1 + NbsLength t
  end.

(* interprets byteString with h being most significant byte *)
Fixpoint bsToN_aux (bs : byteString) (len : nat) : N :=
  match bs with
    | nil    => 0
    | h :: t => match len with
                  | O   => 0
                  | S n => bsToN_aux t n + wordToN h * Npow2 (8 * (len - 1))
                end
  end.

Definition bsToN (bs : byteString) := bsToN_aux bs (bsLength bs).

(* Toplevel input, characters 7-12: *)
(* > Show. *)
(* > ^^^^^ *)
(* Error: No focused proof (No proof-editing in progress). *)
(* had to add extra argument of type nat for function below to compile,
   how to work around this? 
   
   Error:
   Recursive definition of natToBs is ill-formed.
   In environment
   natToBs : nat -> byteString
   n : nat
   Recursive call to natToBs has principal argument equal to 
   "n / 256" instead of a subterm of "n".
   Recursive definition is:
   "fun n : nat => natToBs (n / 256) ++ [natToWord 8 (n mod 256)]".
*)    
Fixpoint NToBs_aux (n : N) (m : nat) : byteString :=
  match n, m with
    | N0, _    => nil
    | _, S m' => (NToBs_aux (n / 256) m') ++ [NToWord 8 (Nmod n 256)]
    | _, _    => nil
  end.

(* can modify function above to print out fixed size byteString based on argument 'm'*)

Definition NToBs (n : N) : byteString := NToBs_aux n (N.size_nat n).

Inductive TagClass :=
| Universal
| Application
| ContextSpecific
| Private.

Definition byteToClass (b : byte) : TagClass :=
  if (NPeano.leb (wordToNat (b ^& WO~1~0~0~0~0~0~0~0)) 0) then
    if (NPeano.leb (wordToNat (b ^& WO~0~1~0~0~0~0~0~0)) 0) then Universal else Application
  else
    if (NPeano.leb (wordToNat (b ^& WO~0~1~0~0~0~0~0~0)) 0) then ContextSpecific else Private.

Definition classToWord  (tc : TagClass) : word 2 :=
  match tc with
    | Universal       => WO~0~0
    | Application     => WO~0~1
    | ContextSpecific => WO~1~0
    | Private         => WO~1~1
  end.
                     
Inductive contentsType : Type := Primitive | Constructed.

Definition byteToContentsType (b : byte) : contentsType :=
  if (NPeano.leb (wordToNat (b ^& WO~0~0~1~0~0~0~0~0)) 0) then Constructed else Primitive.

Definition contentsTypeToWord (ct : contentsType) : word 1 :=
  match ct with
    | Primitive   => WO~0
    | Constructed => WO~1
  end.

Definition NToFirstTagByte (n : N) : word 5 :=
  if (N.leb n 30) then NToWord 5 n else WO~1~1~1~1~1.

Inductive ASN_Type : Type := ASN_Nat | ASN_Bool | ASN_String.

Definition ASN_toContentsType (atype : ASN_Type) : contentsType :=
  match atype with
    | ASN_Nat    => Primitive
    | ASN_Bool   => Primitive
    | ASN_String => Primitive                                                      
  end.

Definition ASN_toTagN (atype : ASN_Type) : N :=
  match atype with
    | ASN_Nat     => 2
    | ASN_Bool    => 1
    | ASN_String  => 99
  end.

Definition ASN_firstTagByte (atype : ASN_Type) := (fun tc : TagClass =>
    combine (NToFirstTagByte (ASN_toTagN atype))
     (combine (contentsTypeToWord (ASN_toContentsType atype)) (classToWord tc))).
    
Fixpoint subTagBytes_aux (n : N) (m : nat) : byteString :=
  match n, m with
    | N0, _    => nil
    | _, S m' => (subTagBytes_aux (n / 128) m') ++ [combine (NToWord 7 (Nmod n 128)) WO~1]
    | _, _    => nil
  end.

(* can modify function above to print out fixed size byteString based on argument 'm'*)
(* need to make this better, so much work to set one bit *)
Definition subTagBytes (n : N) : byteString :=
  if N.leb n 30  then nil 
  else NToBs (bsToN (subTagBytes_aux n (N.size_nat n)) - 128).

Definition ASN_subsequentTagBytes (atype : ASN_Type) : byteString :=
  if N.leb (ASN_toTagN atype) 30 then nil
  else subTagBytes (ASN_toTagN atype).

Definition ASN_tag := fun (atype : ASN_Type) (tc : TagClass) =>
  [ASN_firstTagByte atype tc] ++ (ASN_subsequentTagBytes atype).

Definition asnToCoqType (atype : ASN_Type) : Type :=
  match atype with
    | ASN_Nat    => N
    | ASN_Bool   => bool 
    | AsN_String => list Ascii.ascii
  end.

(* rules for length encodeds defined in X.690 *)
(* long form uses N instead of nat to compare length and value byteStrings *)
(* may need to add logic saying values less than 127 must be short form, etc *)
(* asn types that are primitive must be encoded using definite form 
   this makes length dependent on asn type which is not captured here *)
Inductive bsLenValPair : byteString -> byteString -> Prop :=
| shortForm : forall (b7 b6 b5 b4 b3 b2 b1 : bool) (valBs : byteString),
                wordToNat (bWord false b7 b6 b5 b4 b3 b2 b1) = bsLength valBs
                -> bsLenValPair [(bWord false b7 b6 b5 b4 b3 b2 b1)] valBs
| longForm  : forall (b7 b6 b5 b4 b3 b2 b1 : bool) (lenBs valBs : byteString),
                wordToNat (bWord false b7 b6 b5 b4 b3 b2 b1) = bsLength lenBs
                -> bsToN lenBs = NbsLength valBs
                -> bsLenValPair ([(bWord true b7 b6 b5 b4 b3 b2 b1)] ++ lenBs) valBs
| nullTerm  : forall (valBs : byteString), 
                (exists (bs : byteString), valBs = bs ++ [wzero 8; wzero 8])
                -> bsLenValPair [WO~0~1~0~1~0~0~0~0] valBs.


Record Encoded_ByteString := {
         tag        : byteString;
         len        : byteString;
         val        : byteString;
         valid_pair : bsLenValPair len val 
}.


Inductive DER_R : forall (atype : ASN_Type), Type -> Encoded_ByteString -> Prop :=
| DER_Nat  : forall (atype : ASN_Type) (tc : TagClass) (ebs : Encoded_ByteString),
                   tag ebs = ASN_tag atype tc
                   -> DER_R ASN_Nat (asnToCoqType ASN_Nat) ebs
| DER_Bool : forall ebs : encoded_byteString 