Require Import Algebra OwnTacts Equal.

(* Natural numbers is is the simplest inductive type.                                                          *)

(* For a type to be natural numbers is has to have the following properties (The Peano Axioms) :               *)

(* 1 : forall n in N, *)
(*       There should exists a successor 'Succ' to n. (n + 1)                                                  *)

(* 2 : forall n, m in N,                                                                                       *)
(*       If n and m is different, their successors should be different.                                        *)

(* 3 : There should exist a element, which is not the successor of anything, denoted 'ZERO'.                   *)

(* 4 : For a property P, if 'P n' is true for 'ZERO' and for an element 'a' in N, then it implies that         *)
(*     that the successor of 'a' is also true, then 'P n' is true. Which is exactly the 'Induction principle'! *)
(*     And actually what we are doing when we prove theorems about natural numbers, is to construct the        *)
(*    'Induction Tree' for natural numbers: *)


(*                                 P (ZERO)     forall n in N, P (n) -> P (Succ n)                             *)
(*                                 ==============================================                              *)
(*                                                       P n                                                   *)

(* So we have a very strong relation between Natural Numbers and Induction and Induction and Recursion         *)
(* is intertwined, so inductive types are ideal for recursive functions.                                       *)
                                                                  
Inductive Nat : Set :=
  | ZERO : Nat                  (* Base case *)
  | Succ : Nat -> Nat.          (* Inductive case *)

(* As always, we need a way of telling if elements are equal. *)

(* This is our first recursive function, when working with recursive data structures in Coq *)
(* We use a fixpoint, which is able to call itself, compared to a definition which cannot.  *)
Fixpoint eq_Nat (n m : Nat) : Prop :=
  match n, m with
    | ZERO   , ZERO     => True
    | Succ n', ZERO     => False
    | ZERO   , Succ m' => False
    | Succ n', Succ m' => eq_Nat n' m'
  end.

Notation "A =N= B" := (eq_Nat A B) (at level 70, no associativity).

Lemma eq_Nat_ZERO_ZERO :
  ZERO =N= ZERO.
Proof.
  unfold eq_Nat.
  exact I.
Qed.

Lemma eq_Nat_Succ_ZERO :
  forall n : Nat,
    not (Succ n =N= ZERO).
Proof.
  intro n.
  unfold not.
  intro H.
  unfold eq_Nat in H.
  contradiction H.
Qed.

Lemma eq_Nat_ZERO_Succ :
  forall m : Nat,
    not (ZERO =N= Succ m).
Proof.
  intro n.
  unfold not.
  intro H.
  unfold eq_Nat in H.
  contradiction H.
Qed.

Lemma eq_Nat_Succ_Succ :
  forall n m : Nat,
    eq_Nat n m <-> eq_Nat (Succ n) (Succ m) .
Proof.
  intros n m.
  unfold eq_Nat.
  fold eq_Nat.
  split.
    intro H.
    exact H.

    intro H.
    exact H.
Qed.

Lemma eq_Nat_is_reflexive :
  Reflexive Nat eq_Nat.
Proof.
   unfold Reflexive.
   intro n.
   induction n as [ | n' IHn']. (* Whenever we have a inductive type, we use 'induction' to reason about *)
                                 (* the base case and inductive case of the type, assuming P n. *)
   (* Base case *)
    exact eq_Nat_ZERO_ZERO.

    apply <- eq_Nat_Succ_Succ.
    exact IHn'.
Qed.

Lemma eq_Nat_is_symmetric :
  Symmetric Nat eq_Nat.
Proof.
   unfold Symmetric.
   intros n.                  (* By waiting introducing all variables, we get a stronger induction hypothesis *)
   induction n as [ | n' IHn']; intros [ | m']; intro H.
     exact H.
        
     apply eq_Nat_ZERO_Succ in H.
     contradiction H.

     apply eq_Nat_Succ_ZERO in H.
     contradiction H.
      
     apply -> eq_Nat_Succ_Succ.
     apply (IHn' m').
     apply <- eq_Nat_Succ_Succ in H.
     exact H.
Qed.

Lemma eq_Nat_is_transitive :
  Transitive Nat eq_Nat.
Proof.
  unfold Transitive.
    intros n.
    induction n as [ | n' IHn']; intros [ | m'] l; intros H_1 H_2.
      exact H_2.

      case l as [ | l'].
        exact eq_Nat_ZERO_ZERO.

        apply eq_Nat_ZERO_Succ in H_1.
        contradiction H_1.

     apply eq_Nat_Succ_ZERO in H_1.
     contradiction H_1.

     case l as [ | l'].
        contradiction (eq_Nat_Succ_ZERO m' H_2). 

        apply (IHn' m' l').
        apply eq_Nat_Succ_Succ in H_1.
        exact H_1.

        apply eq_Nat_Succ_Succ in H_2.
        exact H_2.
Qed.

Theorem eq_Nat_is_a_valid_equal :
  Equal Nat eq_Nat.
Proof.
  unfold Equal.
  split.
    exact eq_Nat_is_reflexive.
  split.
    exact eq_Nat_is_symmetric.

    exact eq_Nat_is_transitive.
Qed.

(* The addition function for natural numbers *)

Definition unit_test_addtion (candidate : Nat -> Nat -> Nat) :=
  (candidate ZERO ZERO =N= ZERO) /\
  (candidate (Succ ZERO) ZERO =N= Succ ZERO) /\
  (candidate (Succ ZERO) (Succ ZERO) =N= Succ (Succ ZERO)).

Definition specification_of_addition (add' : Nat -> Nat -> Nat) : Prop :=
  (forall m : Nat,
     add' ZERO m =N= m) /\
  (forall n m,
     add' (Succ n) m =N= Succ (add' n m)). 

Theorem specification_of_addition_is_unique :
  forall add add' : Nat -> Nat -> Nat,
    specification_of_addition add ->
    specification_of_addition add' ->
    forall n m : Nat,
      add n m =N= add' n m.
Proof.
  intros add add'.
  unfold specification_of_addition.
  intros [H_add_ZERO H_add_Succ] [H_add'_ZERO H_add'_Succ].
  intro n.
  induction n as [ | n' IHn ]; intro m.
    assert (H_add_ZERO_m := H_add_ZERO m). (* We use 'assert' to make an assertion. This time we *)
                                           (* instantiate H_add_ZERO with the variable m. *)
    assert (H_add'_ZERO_m := H_add'_ZERO m).
    apply (eq_Nat_



(* TODO: Define everything self. *)

Require Import Arith.
(* Proving with the built-in nat *)

Theorem Nat_and_addition_is_a_monoid :
  Monoid nat plus eq.
Proof.
  unfold Monoid.
  split.
    unfold Neutral.
    exists O.  
    intro n.
    split.
      exact (plus_0_r n).

      exact (plus_0_l n).
     
    unfold Semi_Group.
    split.
      exact (eq_is_a_valid_Equal nat).
    
      unfold Associative.
      exact plus_assoc.
Qed.      

Theorem Nat_and_multiplication_is_a_monoid :
  Monoid nat mult eq.
Proof.
  unfold Monoid.
  split.
    unfold Neutral.
    exists 1.
    intro n.
    split.
      exact (mult_1_r n).
      
      exact (mult_1_l n).

   unfold Semi_Group.
     split.
       exact (eq_is_a_valid_Equal nat).
       
       unfold Associative.
       exact mult_assoc.
Qed.

Theorem Nat_and_max_is_a_monoid :
  Monoid nat max eq.
Proof.
  unfold Monoid.
  split.
    unfold Neutral.
    exists 0.
    intro n.
    split.
      exact (Max.max_0_r n).

      exact (Max.max_0_l n).
    
     unfold Semi_Group.
     split.
       exact (eq_is_a_valid_Equal nat).
       exact Max.max_assoc.
Qed.

Proposition Nat_and_min_is_NOT_a_monoid :
    not (Monoid nat min eq).
Proof.
  unfold Monoid.
  unfold not.
  intros [H_no_neutral_element _].
  unfold Neutral in H_no_neutral_element.
  destruct H_no_neutral_element as [not_O H_not_neutral].
  destruct (H_not_neutral (S not_O)) as [H_absurd _].
  rewrite -> Min.min_r in H_absurd.
  apply n_Sn in H_absurd.
  contradiction.

  exact (le_n_Sn not_O).
Qed.

(* Please continue with Lists *)
