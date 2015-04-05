Require Import Algebra Tactics Equal.

(* TODO: Define everything ground up. *)
  
Require Import List.
(* The proofs using built-in list and append *)

Definition append (T : Type) (a b : list T) := app a b. 

Theorem polymorphic_lists_and_append_is_associative :
  forall (T : Type),
    Associative (list T) (append T) eq.
Proof.         
  unfold Associative.
  exact app_assoc.
Qed.

Theorem polymorphic_lists_and_append_is_a_semi_group :
  forall (T : Type),
    Semi_Group (list T) (append T) eq.
Proof.
  intro T.
  unfold Semi_Group.
  split.
    exact (eq_is_a_valid_Equal (list T)).
    exact (polymorphic_lists_and_append_is_associative T).
Qed.

Theorem polymorphic_lists_and_append_have_a_neutral_element :
  forall T : Type,
  exists O : list T,
     Neutral (list T) (append T) O eq.
Proof.
  intro T.
  unfold Neutral.
  unfold append.
  exists nil.
  intro l.
    split.
      exact (app_nil_r l).
     
      exact (app_nil_l l).

Qed.

Corollary polymorphic_lists_and_append_is_a_monoid :
  forall T : Type,
    Monoid (list T) (append T) eq.
Proof.
  intro T.
  unfold Monoid.
  split.
   exact (polymorphic_lists_and_append_have_a_neutral_element T).
   exact (polymorphic_lists_and_append_is_a_semi_group T).
Qed.

(* Please continue with Integers. *)
