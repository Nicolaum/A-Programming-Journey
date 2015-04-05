Require Import Algebra Tactics Equal ZArith.
Open Scope Z_scope.

Inductive Vec3 : Type :=
  | vec3 : Z -> Z -> Z -> Vec3.

Definition specification_add_vec3 (add : Vec3 -> Vec3 -> Vec3) :=
  forall x1 y1 z1 x2 y2 z2 : Z,
    add (vec3 x1 y1 z1) 
        (vec3 x2 y2 z2) =
    vec3 (x1 + x2) 
          (y1 + y2)
          (z1 + z2).

Theorem specification_of_add_vec3_is_unique :
  forall add add' : Vec3 -> Vec3 -> Vec3,
    specification_add_vec3 add  ->
    specification_add_vec3 add' ->
    forall v1 v2 : Vec3,
      add v1 v2 = add' v1 v2.
Proof.
  intros add add'.
  unfold specification_add_vec3.
  intros S_add S_add'.
  intros v1 v2.
  destruct v1 as [x1 y1 z1].
  destruct v2 as [x2 y2 z2].
  rewrite -> S_add.
  symmetry.
  exact (S_add' x1 y1 z1 x2 y2 z2).
Qed.

Function add_vec3 (v1 v2 : Vec3) : Vec3 :=
  match v1, v2 with
    | vec3 x1 y1 z1, vec3 x2 y2 z2 =>
      vec3 (x1 + x2) (y1 + y2) (z1 + z2)
  end.

Lemma unfold_add_vec3 :
  forall x1 y1 z1 x2 y2 z2 : Z,
    add_vec3 (vec3 x1 y1 z1) 
              (vec3 x2 y2 z2) =
    vec3 (x1 + x2) 
          (y1 + y2)
          (z1 + z2).
Proof.
  unfold_tactic add_vec3.
Qed.

Theorem add_vec3_satisfies_the_specification :
  specification_add_vec3 add_vec3.
Proof.
  unfold specification_add_vec3.
  exact unfold_add_vec3.
Qed.

Theorem Vec3_and_addition_is_associative :
  Associative Vec3 add_vec3 eq.
Proof.
  unfold Associative.
  intros [x1 y1 z1] [x2 y2 z2] [x3 y3 z3].
  rewrite ->4 unfold_add_vec3.
  rewrite ->3 Z.add_assoc.
  reflexivity.
Qed.

Corollary Vec3_and_addition_is_a_semi_group :
    Semi_Group Vec3 add_vec3 eq.
Proof.
  unfold Semi_Group.
  split.
  exact (eq_is_a_valid_Equal Vec3).
  exact Vec3_and_addition_is_associative.
Qed.

Definition O_vec3 : Vec3 := vec3 0 0 0.

Lemma add_O_vec3_l :
  forall v : Vec3,
    add_vec3 O_vec3 v = v.
Proof.
  intros [x y z].
  unfold O_vec3.
  rewrite -> unfold_add_vec3.
  rewrite ->3 Z.add_0_l.
  reflexivity.
Qed.

Lemma add_O_vec3_r :
  forall v : Vec3,
    add_vec3 v O_vec3 = v.
Proof.
  intros [x y z].
  unfold O_vec3.
  rewrite -> unfold_add_vec3.
  rewrite ->3 Z.add_0_r.
  reflexivity.
Qed.

Theorem Vec3_and_addition_has_a_neutral_element :
  exists (O : Vec3), 
    Neutral Vec3 add_vec3 O eq.
Proof.
  unfold Neutral.
  exists O_vec3.
  intro v.
  split.
    exact (add_O_vec3_r v).

    exact (add_O_vec3_l v).
Qed.


Corollary Vec3_and_addition_is_a_monoid :
  Monoid Vec3 add_vec3 eq.
Proof.
  unfold Monoid.
  split.
  exact Vec3_and_addition_has_a_neutral_element.
  exact Vec3_and_addition_is_a_semi_group.
Qed.

Theorem Vec3_and_addition_is_commutative :
  Commutative Vec3 add_vec3 eq.
Proof.
  unfold Commutative.
  intros [x1 y1 z1] [x2 y2 z2].
  rewrite ->2 unfold_add_vec3.
  symmetry.
  rewrite -> (Z.add_comm x2 x1).
  rewrite -> (Z.add_comm y2 y1).
  rewrite -> (Z.add_comm z2 z1).
  reflexivity.
Qed.

Definition opp_vec3 (v : Vec3) : Vec3 :=
  match v with
    | vec3 x y z => vec3 (Z.opp x) (Z.opp y) (Z.opp z)
  end.

Lemma add_opp_vec3_r :
  forall v : Vec3,
    add_vec3 v (opp_vec3 v) = O_vec3.
Proof.
  intros [x y z].
  unfold opp_vec3.
  unfold O_vec3.
  rewrite -> unfold_add_vec3.
  rewrite ->3 Zegal_left; reflexivity.
Qed.

Lemma add_opp_vec3_l :
  forall v : Vec3,
    add_vec3 (opp_vec3 v) v = O_vec3.
Proof.
  intro v.
  rewrite -> (Vec3_and_addition_is_commutative (opp_vec3 v) v).
  exact (add_opp_vec3_r v).
Qed.

Theorem Vec3_and_addition_has_an_inverse :
  Inverse Vec3 add_vec3 eq.
Proof.
  unfold Inverse. 
  intro v.
  exists O_vec3.
  exists (opp_vec3 v).
  exact (add_opp_vec3_r v).
Qed.

Corollary Vec3_and_addition_is_a_Abelian_group :
  Abelian_Group Vec3 add_vec3 eq.
Proof.
  unfold Abelian_Group.
  split. 
    exact Vec3_and_addition_is_commutative.
    split.
      exact Vec3_and_addition_has_an_inverse.
      exact Vec3_and_addition_is_a_monoid.
Qed.

(* Vector multiplication is not assciative, because of its type : Vec3 -> Vec3 -> Z *)
(* Therefore it is not a semi group. *)
(* I assume that the vectors is transposed properly *)

Definition specification_of_vec3_multiplication (mult : Vec3 -> Vec3 -> Z) :=
  forall x1 y1 z1 x2 y2 z2 : Z,
    mult (vec3 x1 y1 z1) (vec3 x2 y2 z2) = x1 * x2 + y1 * y2 + z1 * z2.

Theorem specification_of_vec3_multiplication_is_unique :
  forall mult mult' : Vec3 -> Vec3 -> Z,
    specification_of_vec3_multiplication mult ->
    specification_of_vec3_multiplication mult' ->
    forall v w : Vec3,
      mult v w = mult' v w.
Proof.
  intros mult mult'.
  unfold specification_of_vec3_multiplication.
  intros S_mult S_mult'.
  intros [x1 y1 z1] [x2 y2 z2].
  rewrite -> S_mult.
  symmetry.
  exact (S_mult' x1 y1 z1 x2 y2 z2).
Qed.

Function mult_vec3 (v w : Vec3) : Z :=
  match v, w with
    | vec3 x1 y1 z1, vec3 x2 y2 z2 =>
      x1 * x2 + y1 * y2 + z1 * z2
  end.

Lemma unfold_mult_vec3 :
  forall x1 y1 z1 x2 y2 z2 : Z,
    mult_vec3 (vec3 x1 y1 z1) (vec3 x2 y2 z2) = x1 * x2 + y1 * y2 + z1 * z2.
Proof.
  unfold_tactic mult_vec3.
Qed.

Search (_ * _ = _ * _).

Theorem mult_vec3_is_commutative :
  forall v w : Vec3,
    mult_vec3 v w = mult_vec3 w v.
Proof.
  intros [x1 y1 z1] [x2 y2 z2].
  rewrite ->2 unfold_mult_vec3.
  symmetry.
  rewrite -> (Z.mul_comm x2 x1).
  rewrite -> (Z.mul_comm y2 y1).
  rewrite -> (Z.mul_comm z2 z1).
  reflexivity.
Qed.

(* Please continue with Matrix3x3 *)
