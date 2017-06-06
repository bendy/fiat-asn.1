Require Import Lists.List
               Arith
               Ascii.
Import Lists.List.ListNotations.

Set Implicit Arguments.

Notation F := false.
Notation T := true.

Inductive hex := Hex (_ _ _ _ : bool) : hex.

Notation x0 := (Hex F F F F).
Notation x1 := (Hex F F F T).
Notation x2 := (Hex F F T F).
Notation x3 := (Hex F F T T).
Notation x4 := (Hex F T F F).
Notation x5 := (Hex F T F T).
Notation x6 := (Hex F T T F).
Notation x7 := (Hex F T T T).
Notation x8 := (Hex T F F F).
Notation x9 := (Hex T F F T).
Notation xA := (Hex T F T F).
Notation xB := (Hex T F T T).
Notation xC := (Hex T T F F).
Notation xD := (Hex T T F T).
Notation xE := (Hex T T T F).
Notation xF := (Hex T T T T).

Inductive hex_nat_R : hex -> nat -> Prop :=
  | R_0 : hex_nat_R x0 0
  | R_1 : hex_nat_R x1 1                 
  | R_2 : hex_nat_R x2 2
  | R_3 : hex_nat_R x3 3
  | R_4 : hex_nat_R x4 4
  | R_5 : hex_nat_R x5 5
  | R_6 : hex_nat_R x6 6                  
  | R_7 : hex_nat_R x7 7
  | R_8 : hex_nat_R x8 8
  | R_9 : hex_nat_R x9 9
  | R_A : hex_nat_R xA 10
  | R_B : hex_nat_R xB 11                 
  | R_C : hex_nat_R xC 12
  | R_D : hex_nat_R xD 13
  | R_E : hex_nat_R xE 14
  | R_F : hex_nat_R xF 15.

Definition hex_nat (x : hex) : nat :=
  match x with
    | Hex b1 b2 b3 b4 =>
       (2 *
        (2 *
         (2 *
             (if b1 then 1 else 0)
          + (if b2 then 1 else 0))
         + (if b3 then 1 else 0))
        + (if b4 then 1 else 0))  
  end.

Definition nat_hex (n : nat) : hex :=
  match n with
    | 1  => x1
    | 2  => x2
    | 3  => x3
    | 4  => x4
    | 5  => x5
    | 6  => x6
    | 7  => x7
    | 8  => x8
    | 9  => x9
    | 10 => xA
    | 11 => xB
    | 12 => xC
    | 13 => xD
    | 14 => xE
    | 15 => xF
    | _  => x0
  end.
             
Theorem hex_nat_R_equiv : forall x n, hex_nat_R x n <-> hex_nat x = n.
Proof. intros x n. split; intros H.
       -destruct H; simpl; try reflexivity.
       -destruct x. destruct b; destruct b0; destruct b1; destruct b2; simpl in H; subst;
                    constructor.
Qed.
        
Definition byte : Type := hex * hex.
Definition byte_string := list byte.


Definition byte_nat (b : byte) : nat :=
  match b with
  | (b1, b2) => 16 * hex_nat b1 + hex_nat b2 
  end.

Definition nat_byte (n : nat) : byte :=
  if PeanoNat.Nat.leb n 255  then (nat_hex (n / 16), nat_hex (n mod 16)) else (x0,x0).


Notation "'#' A" := (hex_nat A)(at level 60).
Notation "'#' A" := (byte_nat A)(at level 60).

Inductive byte_string_length_R : byte_string -> nat -> Prop :=
| bsl_0_R : byte_string_length_R [] 0
| bsl_1_R : forall (B : byte) (bs : byte_string) (n : nat),
              byte_string_length_R bs n -> byte_string_length_R (B :: bs) (1 + n).

Fixpoint byte_string_length (bs : byte_string) : nat :=
  match bs with
    | [] => 0
    | h :: t =>  1 + byte_string_length t
  end.

(*Theorem byte_string_length_R_equiv : forall bs n,
byte_string_length bs = n <-> byte_string_length_R bs n.
Proof. intros bs. induction bs; intros n; split; intros H.
       -simpl in H. rewrite <- H. apply bsl_0_R.
       -inversion H. reflexivity.
       - simpl in H. remember (byte_string_length bs) as m.
         rewrite <- H. apply bsl_1_R. apply IHbs. reflexivity.
       -simpl. inversion H. subst. apply eq_S. apply IHbs. apply H3.
Qed.    *)
         
(*'big endian' [(x0,x0); (x0,x1)] -> 256 *)
Inductive byte_string_nat_R : byte_string -> nat -> Prop :=
| bsn_0_R : byte_string_nat_R [] 0
| bsn_1_R : forall (B : byte) (bs : byte_string) (n m : nat),
              (# B) = m ->
              byte_string_nat_R bs n ->
              byte_string_nat_R (B :: bs) ((# B) + 256 * n).

Fixpoint byte_string_nat (bs : byte_string) : nat :=
  match bs with
    | [] => 0
    | h :: t => (# h) + 256 * byte_string_nat t
  end.

Theorem byte_string_nat_R_equiv : forall bs n, byte_string_nat_R bs n <-> byte_string_nat bs = n.
Proof. intros bs. induction bs. intros n. split; intros H.
       -simpl. inversion H.
        +reflexivity.
       -simpl in H. subst. apply bsn_0_R.
       -intros n. split; intros H.
        +inversion H. subst. apply IHbs in H4. 
         replace (byte_string_nat (a :: bs)) with ((# a) + 256 * byte_string_nat bs).
         rewrite H4. reflexivity. reflexivity.
        + replace (byte_string_nat (a::bs)) with ((#a) + 256 * byte_string_nat bs) in H.
          rewrite <- H. apply bsn_1_R with (m := (# a)). reflexivity. apply IHbs.
          reflexivity. reflexivity.
Qed.


Fixpoint nat_byte_string_aux (n m : nat) : byte_string :=
  match n, m with
    | 0, _ => nil
    | _, S m' => (nat_byte_string_aux (n / 256) m') ++ [nat_byte (n mod 256)]
    | _, _ => nil
  end.

(*error when n > 5000, need longer ints*)
Definition natToBS n := nat_byte_string_aux n n.

Notation "'#' A" := (byte_string_nat A)(at level 60).
Notation "'#len' A" := (byte_string_length A)(at level 60).

Inductive tlv : byte -> byte_string -> byte_string -> Prop :=
| TLV (T : byte) : forall L V, # L = #len V -> tlv T L V.

Inductive ASnat_Type : Type :=
  ASnat_nat | ASnat_Bool | ASnat_String.

Definition ASnat_TypeToType (atype : ASnat_Type) : Type :=
  match atype with
    | ASnat_nat => nat
    | ASnat_Bool => bool
    | ASnat_String => list ascii
    end.

Inductive DER_R : forall (atype : ASnat_Type),
    ASnat_TypeToType atype
    -> byte_string
    -> Prop :=
| DER_nat : forall (n : nat) (l v : byte_string),
    tlv (x0, x2) l (natToBS n)
    -> DER_R ASnat_nat n ([(x0,x2)] ++ l ++ (natToBS n)).       