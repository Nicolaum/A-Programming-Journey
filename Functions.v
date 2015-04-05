Require Import FunctionalExtensionality Algebra Tactics Equal.

Definition specification_of_composition (T : Type) 
                                        (comp : (T -> T) -> (T -> T) -> (T -> T)) :=
  forall (f g : T -> T),
    comp f g = fun x => g (f x).

Theorem specification_of_composition_is_unique :
  forall (T : Type) (comp1 comp2 : (T -> T) -> (T -> T) -> (T -> T)),
    specification_of_composition T comp1 ->
    specification_of_composition T comp2 ->
    forall f g : T -> T,
      comp1 f g = comp2 f g.
Proof.    
  intro T.
  intros comp1 comp2.
  unfold specification_of_composition.
  intros S_comp1 S_comp2.
  intros f g.
  rewrite -> (S_comp1 f g).
  symmetry.
  exact (S_comp2 f g).
Qed.

Definition C (T : Type) (f g : (T -> T)) : T -> T :=
  fun x => g (f x).

Lemma unfold_C :
  forall (T : Type)
         (f g : T -> T),
    C T f g = fun x => g (f x).
Proof.
  unfold_tactic C.
Qed.

Theorem Types_and_function_composition_is_Associative :
  forall T : Type,
    Associative (T -> T) (C T) eq.
Proof.
  intro T.
  unfold Associative.
  intros f g h.
  rewrite ->4 unfold_C.
  reflexivity.
Qed.

Corollary Types_and_function_composition_is_a_Semi_Group :
  forall T : Type,
    Semi_Group (T -> T) (C T) eq.
Proof.
  intro T.
  unfold Semi_Group.
  split.
    exact (eq_is_a_valid_Equal (T -> T)).
    exact (Types_and_function_composition_is_Associative T).
Qed.

Definition Id_function (T : Type) : (T -> T) := fun x => x.

Lemma C_id_l :
  forall (T : Type)
         (f : (T -> T)),
  C T (Id_function T) f = f.
Proof.
  intros T f.
  rewrite -> unfold_C.
  unfold Id_function.
  symmetry.
  exact (eta_expansion f).
Qed.

Lemma C_id_r :
  forall (T : Type)
         (f : (T -> T)),
  C T f (Id_function T) = f.
Proof.
  intros T f.
  rewrite -> unfold_C.
  unfold Id_function.
  symmetry.
  exact (eta_expansion f).
Qed.  

Theorem Types_and_function_composition_has_a_neutal_element :
  forall T : Type,
  exists O : (T -> T),
    Neutral (T -> T) (C T) O eq.
Proof.
  intro T.
  unfold Neutral.
  exists (Id_function T).
  intro f.
  split.
    exact (C_id_r T f).
    
    exact (C_id_l T f).
Qed.

Corollary Types_and_function_composition_is_a_monoid :
  forall T : Type,
    Monoid (T -> T) (C T) eq.
Proof.
  intro T.
  unfold Monoid.
  split.
  exact (Types_and_function_composition_has_a_neutal_element T).
  exact (Types_and_function_composition_is_a_Semi_Group T).
Qed.

(* Please continue with Lazy-Lists *)
