Require Import Equal Algebra OwnTacts.

(* One of the simplest types is the type of booleans *)

Inductive bool' : Type :=
| T : bool'
| F : bool'.

(* It is simply true or false. *)

(* First of we need a way of telling if the two types is equal. *)

Fixpoint eq_bool' (a b : bool') : Prop :=
  match a, b with
    | T, T => True
    | F, F => True
    | _, _ => False
  end.

(* We introduce infix notation for eq_bool' *)
Notation "A =B= B" := (eq_bool' A B) (at level 70, no associativity).

Lemma eq_bool'_T_T :
  T =B= T.
Proof.
  unfold eq_bool'.
  reflexivity.
Qed.

Lemma eq_bool'_F_F :
  F =B= F.
Proof.
  unfold eq_bool'.
  reflexivity.
Qed.

Lemma eq_bool'_T_F :
  ~ (T =B= F).
Proof.
  unfold not.
  unfold eq_bool'.
  intros H.
  contradiction.
Qed.

Lemma eq_bool'_F_T :
  ~ (F =B= T).
Proof.
  unfold not.
  unfold eq_bool'.
  intro H.
  contradiction.
Qed.

Theorem eq_bool'_is_reflexive :
  Reflexive bool' eq_bool'.
Proof.
  unfold Reflexive.
  intro a.
  case a as [ | ]. (* case is used to destruct types in their components. *)
    exact eq_bool'_T_T.
    exact eq_bool'_F_F.
Qed.
Theorem eq_bool'_is_symmetric :
  Symmetric bool' eq_bool'.          
Proof.
  unfold Symmetric.
  intros [ | ] [ | ].           (* We can also destruct directly, by pattern [ | ] *)
    intro H.
    exact H.

    intro H.
    apply eq_bool'_T_F.
    exact H.

    intro H.
    apply eq_bool'_F_T.
    exact H.

    intro H.
    exact H.
Qed.

Theorem eq_bool'_is_transitive :
  Transitive bool' eq_bool'.
Proof.
  unfold Transitive.
  intros [ | ] [ | ] [ | ] H H';
    (exact H || exact H'n ||
           contradiction (eq_bool'_F_T H) || 
           contradiction (eq_bool'_F_T H')). 
Qed.
  
Corollary eq_bool'_is_a_valid_equal :
  Equal bool' eq_bool'.
Proof.
  unfold Equal.
  split.
    exact eq_bool'_is_reflexive.
  split.
    exact eq_bool'_is_symmetric.
    
    exact eq_bool'_is_transitive.
Qed.

Corollary eq_is_a_valid_equal_for_bool' :
  Equal bool' eq.
Proof.
  exact (eq_is_a_valid_Equal bool').
Qed.

Theorem eq_and_eq_bool'_is_equivalent :
  forall a b : bool',
    (a = b) <-> (a =B= b).
Proof.
  intros [ | ] [ | ]; split; unfold eq_bool'; intro H.
    
    exact I.
    reflexivity.

    discriminate H.             (* We use discriminate when we have a *) 
                                (* primitive equality in  the hypothesises, *)
                                (* which is false. *)
    contradiction H.
    
    discriminate H.
    contradiction H.

    exact I.
    reflexivity.
Qed.

(* Conjunction or also know as and, is an importent function for booleans *)

(* Whenever we want to implement a new function, first off we define a small unit test. *)
(* This have multiple purposes, for one it gives a feel of the function and we can easily*)
(* test if our implemented function is correct. *)

(* We want the unit test to work with, eq_bool' instead of eq, since this is something *)
(* we calculate. *)

Definition unit_test_conj_b (candidate : bool' -> bool' -> bool') :=
  candidate T T =B= T /\
  candidate T F =B= F /\
  candidate F T =B= F /\
  candidate F F =B= F.  

(* We also need a specification, which serves the purpose of a unit test, except *)
(* it talks about all possible inputs instead of just a few. In this case however *)
(* they are similar. *)
(* From we use eq, so we can use what we learnt in Basic. *)
(* We have showed their equivalence so it does not matter which we use. *)

Definition specification_of_conjunction_for_booleans (conj_b : bool' -> bool' -> bool') :=
  conj_b T T = T /\
  conj_b T F = F /\
  conj_b F T = F /\
  conj_b F F = F.

(* Proving the uniqueness of a specification, makes us able to say that every  *)
(* function satifiyng the specification do exactly the same, eventhough they   *)
(* are implemented differently. This gives room for optimized algorithms, like *)
(* making a function tail recursive instead of the naive solution.             *)

Theorem specification_of_conjunction_for_booleans_is_unique :
  forall conj conj' : bool' -> bool' -> bool',
    specification_of_conjunction_for_booleans conj ->
    specification_of_conjunction_for_booleans conj' ->
    forall a b : bool',
      conj a b = conj' a b.
Proof.
  intros conj conj'.
  unfold specification_of_conjunction_for_booleans.
  intros [H_conj_T_T [H_conj_T_F [H_conj_F_T H_conj_F_F]]]
         [H_conj'_T_T [H_conj'_T_F [H_conj'_F_T H_conj'_F_F]]].
  intros [ | ] [ | ].
    rewrite -> H_conj_T_T.
    symmetry.
    exact H_conj'_T_T.

    rewrite -> H_conj_T_F.
    symmetry. 
    exact H_conj'_T_F.
    
    rewrite -> H_conj_F_T.
    symmetry.
    exact H_conj'_F_T.

    rewrite -> H_conj_F_F.
    symmetry.
    exact H_conj'_F_F.
Qed.

Function conj_b (a b : bool') : bool' :=
  match a, b with
    | T, T => T
    | _, _ => F
  end.

(* Introducing infix notation for conj_b *)

Notation "A &&' B" := (conj_b A B) (at level 40, left associativity).

(* Sanity Check *)
Compute (unit_test_conj_b conj_b).

(* Whenever we have implemented a function, we should make lemmas that *)
(* tell what the function do, instead of unfolding them. We use the  *)
(* unfold_tactic 'name' to do this. *)

Lemma conj_b_T_T :
  T &&' T = T.
Proof.
  unfold_tactic conj_b.         
Qed.

Lemma conj_b_T_F :
  T &&' F = F.
Proof.
  unfold_tactic conj_b.
Qed.

Lemma conj_b_F_T :
  F &&' T = F.
Proof.
  unfold_tactic conj_b.
Qed.

Lemma conj_b_F_F :
  F &&' F = F.
Proof.
  unfold_tactic conj_b.
Qed.

(* Now we can prove that the function satifies the specification, therefore *)
(* ensuring that it works correctly for all possible inputs.                *)

Lemma conj_b_satisfies_the_specification :
  specification_of_conjunction_for_booleans conj_b.
Proof.
  unfold specification_of_conjunction_for_booleans.
  split.
    exact conj_b_T_T.
  split.
    exact conj_b_T_F.
  split.
    exact conj_b_F_T.

    exact conj_b_F_F.
Qed.

(* Let us see if bool' and conj_b is associative. *)

Lemma conj_b_assoc :
  Associative bool' conj_b eq.
Proof.
  unfold Associative.
  intros [ | ] [ | ] [ | ]; 
    (rewrite -> conj_b_T_T ||  
     rewrite -> conj_b_T_F ||
     rewrite -> conj_b_F_T ||
     rewrite -> conj_b_F_F);
    (rewrite -> conj_b_T_T ||  
     rewrite -> conj_b_T_F ||
     rewrite -> conj_b_F_T ||
     rewrite -> conj_b_F_F);
  reflexivity.
Qed.

(* Exercise *, write the full proof without ';' *)
Lemma conj_b_assoc' :
  Associative bool' conj_b eq.
Proof.
Abort.

(* Exercise ***, write the proof using eq_bool' instead of eq. *)

Lemma conj_b_assoc'' :
  Associative bool' conj_b eq_bool'.
Proof.
Abort.

(* Now we conj_b is a semi group. *)

Corollary Bool'_and_conj_b_is_a_semi_group :
  Semi_Group bool' conj_b eq.
Proof.    
  unfold Semi_Group.
  split.
    exact (eq_is_a_valid_Equal bool').

    exact conj_b_assoc.
Qed.    

(* Exercise *** : write the proof using eq_bool' instead of eq. *)
Corollary Bool'_and_conj_b_is_a_semi_group' :
  Semi_Group bool' conj_b eq_bool'.
Proof.    
Abort.

(* Let us prove that true is a neutral element for bool' and conj_b *)

(* First that true is neutal on the left. *)
Lemma conj_b_T_l :
  forall a : bool',
    T &&' a = a.
Proof.
  intros [ | ].
    exact conj_b_T_T.
    exact conj_b_T_F.
Qed.

(* And on the right *)
Lemma conj_b_T_r :
  forall a : bool',
    a &&' T = a.
Proof.
  intros [ | ].
    exact conj_b_T_T.
    exact conj_b_F_T.
Qed.

(* Now we prove that there exists a neutal element. Which is T. *)
Theorem T_is_a_neutral_element_for_conj :
  Neutral bool' conj_b T eq.
Proof.
  unfold Neutral.
  intro a.
  split.
    exact (conj_b_T_r a).

    exact (conj_b_T_l a).
Qed.

(* Now, do bool' and conj_b for a monoid. *)
Corollary Bool'_and_conj_form_a_monoid :
  Monoid bool' conj_b eq.
Proof.
  unfold Monoid.
  split.
    exists T.
    exact T_is_a_neutral_element_for_conj.

    exact Bool'_and_conj_b_is_a_semi_group.
Qed.

(* Exercise *** : Prove that bool' and conj_b' form a monoid using eq_bool' *)

Lemma conj_b_T_l' :
  forall a : bool',
    conj_b T a =B= a.
Proof.
Abort.

Lemma conj_b_T_r' :
  forall a : bool',
    conj_b a T = a.
Proof.
Abort.

Theorem T_is_a_neutral_element_for_conj' :
  Neutral bool' conj_b T eq_bool'.
Proof.
Abort.

(* Exercises : *)
(* Create a unit test for disjunction (or) for bool' *)
(* Make a specification of disjunction and prove its uniqueness. *)
(* Implement a disjunction function and prove that it satifies the specification *)
(* Prove that your disjunction function and bool' forms a Monoid. *)


Require Import Bool.
(* Let us look into the proof for a monoid for the built-in bool *)

Corollary Booleans_and_conjunction_is_a_monoid :
  Monoid bool andb eq.
Proof.
  unfold Monoid.
  split.
    unfold Neutral.
    exists true.
    intro b.
    split.
      Search (_ && true = _).
      exact (andb_true_r b).
      Search (true && _ = _).
      exact (andb_true_l b).

  unfold Semi_Group.
  split.
    exact (eq_is_a_valid_Equal bool).

    unfold Associative.
    Search (_ && (_ && _) = (_ && _) && _).
    exact andb_assoc.
Qed.

Corollary booleans_and_disjunction_is_a_monoid :
  Monoid bool orb eq.
Proof.
  unfold Monoid.
  split.
  exists false.
  unfold Neutral.
  intro b.
  split.
    exact (orb_false_r b).
  
    exact (orb_false_l b).

  unfold Semi_Group.
  split.
    exact (eq_is_a_valid_Equal bool).
    exact orb_assoc.
Qed.

(* Please continue in Natural-Numbers *)
