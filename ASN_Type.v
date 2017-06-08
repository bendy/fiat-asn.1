Require Import Arith Div2 NArith Bool Omega Word List.
Import ListNotations.

Notation byte := (word 8).
Notation byteString := (list byte).

(* b8 is most significant bit *)
Definition bWord (b8 b7 b6 b5 b4 b3 b2 b1 : bool) :=
 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 (WS b8 WO)))))))).

  
Fixpoint bsLength (bs : byteString) : nat := 
  match bs with
    | []     => 0
    | h :: t => 1 + bsLength t
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
                  | 0   => 0
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


(* rules for length encodeds defined in X.690 *)
(* long form uses N instead of nat to compare length and value byteStrings *)
(* may need to add logic saying values less than 127 must be short form, etc *)
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
                                                        
                    
Inductive tlv : byte -> byteString -> byteString -> Prop :=
| TLV : forall (b : byte) (lenBs valBs : byteString),
          bsLenValPair lenBs valBs -> tlv b lenBs valBs.
 