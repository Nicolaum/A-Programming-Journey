(* For a equal function to be valid it should be reflexive, symmetric and transitive. *)

Definition Reflexive (T : Type) (equal : T -> T -> Prop) :=
  forall e : T,
    equal e e.

Definition Symmetric (T : Type) (equal : T -> T -> Prop) :=
  forall e1 e2 : T,
    equal e1 e2 -> equal e2 e1.

Definition Transitive (T : Type) (equal : T -> T -> Prop) :=
  forall e1 e2 e3 : T,
    equal e1 e2 ->
    equal e2 e3 ->
    equal e1 e3. 

Definition Equal (T : Type)
                 (equal : T -> T-> Prop) :=
  Reflexive T equal /\
  Symmetric T equal /\
  Transitive T equal.

Corollary eq_is_a_valid_Equal :
  forall T : Type,
    Equal T eq.
Proof.  
  intro T.
  unfold Equal.
  split.
    unfold Reflexive.
    intro e.
    reflexivity.

    split.
      unfold Symmetric.
      intros e1 e2.
      intro H.
      symmetry.
      exact H.

      unfold Transitive.
      intros e1 e2 e3.
      intros H1 H2.
      rewrite -> H2 in H1.
      exact H1.
Qed.

(* Please continue with Algebra *)
