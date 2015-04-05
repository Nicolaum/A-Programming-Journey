Require Import Algebra Tactics Equal.

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

Function eq_Nat (n m : Nat) : Prop :=
  f
  match n, m with


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
