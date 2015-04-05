Require Import ZArith Vec3 Algebra Tactics Equal.
Open Scope Z_scope.

Inductive Matrix3x3 : Type :=
| matrix : Vec3 -> Vec3 -> Vec3 -> Matrix3x3.

(* Addition *)

Definition specification_of_add_matrix_3x3 (add : Matrix3x3 -> 
                                                  Matrix3x3 ->
                                                  Matrix3x3) :=
  forall v1 v2 v3 w1 w2 w3 : Vec3,
    add (matrix v1 v2 v3) (matrix w1 w2 w3) = matrix (add_vec3 v1 w1)
                                                     (add_vec3 v2 w2)
                                                     (add_vec3 v3 w3).

Theorem specification_of_add_matrix_3x3_is_unique :
  forall add add' : Matrix3x3 -> Matrix3x3 -> Matrix3x3,
    specification_of_add_matrix_3x3 add ->
    specification_of_add_matrix_3x3 add' ->
    forall A B : Matrix3x3,
      add A B = add' A B.
Proof.
  intros add add'.
  unfold specification_of_add_matrix_3x3.
  intros S_add S_add'.
  intros [v1 v2 v3] [w1 w2 w3].
  rewrite -> S_add.
  symmetry.
  exact (S_add' v1 v2 v3 w1 w2 w3).
Qed.

Function add_matrix (A B : Matrix3x3) : Matrix3x3 :=
  match A, B with
    | matrix v1 v2 v3, matrix w1 w2 w3 =>
      matrix (add_vec3 v1 w1)
             (add_vec3 v2 w2)
             (add_vec3 v3 w3)
  end.

Lemma unfold_add_matrix :
  forall v1 v2 v3 w1 w2 w3 : Vec3,
    add_matrix (matrix v1 v2 v3) (matrix w1 w2 w3) = matrix (add_vec3 v1 w1)
                                                            (add_vec3 v2 w2)
                                                            (add_vec3 v3 w3).
Proof.
  unfold_tactic add_matrix.
Qed.

Theorem add_matrix_satisfies_the_specification :
  specification_of_add_matrix_3x3 add_matrix.
Proof.
  unfold specification_of_add_matrix_3x3.
  exact unfold_add_matrix.
Qed.

Theorem Matrix3x3_and_addition_is_associative :
  Associative Matrix3x3 add_matrix eq.
Proof.
  unfold Associative.
  intros [v1 v2 v3] [w1 w2 w3] [x1 x2 x3].
  rewrite ->4 unfold_add_matrix.
  rewrite ->3 Vec3_and_addition_is_associative.
  reflexivity.
Qed.

Corollary Matrix3x3_and_addition_is_a_semi_group :
  Semi_Group Matrix3x3 add_matrix eq.
Proof.
  unfold Semi_Group.
  split.
  exact (eq_is_a_valid_Equal Matrix3x3).
  exact Matrix3x3_and_addition_is_associative.
Qed.

Definition O_matrix : Matrix3x3 := matrix O_vec3 O_vec3 O_vec3.

Lemma add_O_matrix_l :
  forall A : Matrix3x3,
    add_matrix O_matrix A = A.
Proof.
  intros [a b c].
  unfold O_matrix.
  rewrite -> unfold_add_matrix.
  rewrite ->3 add_O_vec3_l.
  reflexivity.
Qed.

Lemma add_O_matrix_r :
  forall A : Matrix3x3,
    add_matrix A O_matrix = A.
Proof.
  intros [a b c].
  unfold O_matrix.
  rewrite -> unfold_add_matrix.
  rewrite ->3 add_O_vec3_r.
  reflexivity.
Qed.

Theorem Matrix3x3_and_addition_have_neutral_element :
  exists O : Matrix3x3,
    Neutral Matrix3x3 add_matrix O eq.
Proof.
  unfold Neutral.
  exists O_matrix.
  intro A.
  split.
    exact (add_O_matrix_r A).
    
    exact (add_O_matrix_l A).
Qed.

Corollary Matrix3x3_and_addition_is_a_monoid :
  (exists O : Matrix3x3, Neutral Matrix3x3 add_matrix O eq) /\
  Semi_Group Matrix3x3 add_matrix eq.
Proof.
  split.
    exact Matrix3x3_and_addition_have_neutral_element.
    exact Matrix3x3_and_addition_is_a_semi_group.
Qed.

Theorem Matrix3x3_and_addition_is_commutative :
  Commutative Matrix3x3 add_matrix eq.
Proof.
  unfold Commutative.
  intros [v1 w1 x1] [v2 w2 x2].
  rewrite ->2 unfold_add_matrix.
  symmetry.
  rewrite -> (Vec3_and_addition_is_commutative v2 v1).
  rewrite -> (Vec3_and_addition_is_commutative w2 w1).
  rewrite -> (Vec3_and_addition_is_commutative x2 x1).
  reflexivity.
Qed.

Definition opp_matrix (A : Matrix3x3) : Matrix3x3 :=
  match A with
    | matrix a b c => matrix (opp_vec3 a) (opp_vec3 b) (opp_vec3 c)
  end.

Theorem Matrix3x3_and_addition_have_an_inverse :
  Inverse Matrix3x3 add_matrix eq.
Proof.
  unfold Inverse.
  intro A.
  exists O_matrix.
  exists (opp_matrix A).
  unfold opp_matrix.
  destruct A as [a b c].
  rewrite -> unfold_add_matrix.
  rewrite ->3 add_opp_vec3_r.
  fold O_matrix.
  reflexivity.
Qed.

Corollary Matrix3x3_and_addition_is_an_abelian_group :
  Abelian_Group Matrix3x3 add_matrix eq.
Proof.
  unfold Abelian_Group.
  split.
    exact Matrix3x3_and_addition_is_commutative.
    split.
      exact Matrix3x3_and_addition_have_an_inverse.
      exact Matrix3x3_and_addition_is_a_monoid.
Qed.

(* Multiplication *)

Definition specification_of_3x3_matrix_multiplication (mult : Matrix3x3 ->
                                                              Matrix3x3 ->
                                                              Matrix3x3) :=
  forall a11 a12 a13 a21 a22 a23 a31 a32 a33 b11 b12 b13 b21 b22 b23 b31 b32 b33 : Z,
    mult (matrix (vec3 a11 a12 a13) 
                 (vec3 a21 a22 a23) 
                 (vec3 a31 a32 a33))
         (matrix (vec3 b11 b12 b13)
                 (vec3 b21 b22 b23)
                 (vec3 b31 b32 b33)) =
    matrix (vec3 (mult_vec3 (vec3 a11 a12 a13) (vec3 b11 b21 b31))
                   (mult_vec3 (vec3 a11 a12 a13) (vec3 b12 b22 b32))
                   (mult_vec3 (vec3 a11 a12 a13) (vec3 b13 b23 b33)))
             (vec3 (mult_vec3 (vec3 a21 a22 a23) (vec3 b11 b21 b31))
                   (mult_vec3 (vec3 a21 a22 a23) (vec3 b12 b22 b32))
                   (mult_vec3 (vec3 a21 a22 a23) (vec3 b13 b23 b33)))
             (vec3 (mult_vec3 (vec3 a31 a32 a33) (vec3 b11 b21 b31))
                   (mult_vec3 (vec3 a31 a32 a33) (vec3 b12 b22 b32))
                   (mult_vec3 (vec3 a31 a32 a33) (vec3 b13 b23 b33))).

Theorem specification_of_3x3_matrix_multiplication_is_unique :
  forall mult mult' : Matrix3x3 -> Matrix3x3 -> Matrix3x3,
    specification_of_3x3_matrix_multiplication mult ->
    specification_of_3x3_matrix_multiplication mult' ->
    forall A B : Matrix3x3,
      mult A B = mult' A B.
Proof.    
  intros mult mult'.
  unfold specification_of_3x3_matrix_multiplication.
  intros S_mult S_mult'.
  intros [[a11 a12 a13] 
          [a21 a22 a23] 
          [a31 a32 a33]]

         [[b11 b12 b13] 
          [b21 b22 b23] 
          [b31 b32 b33]].
  rewrite -> S_mult.
  symmetry.
  exact (S_mult' a11 a12 a13 a21 a22 a23 a31 a32 a33 b11 b12 b13 b21 b22 b23 b31 b32 b33).
Qed.

Function mult_matrix (A B : Matrix3x3) : Matrix3x3 :=
  match A, B with
    | (matrix (vec3 a11 a12 a13) 
              (vec3 a21 a22 a23) 
              (vec3 a31 a32 a33)),
      (matrix (vec3 b11 b12 b13)
              (vec3 b21 b22 b23)
              (vec3 b31 b32 b33)) =>
      matrix (vec3 (mult_vec3 (vec3 a11 a12 a13) (vec3 b11 b21 b31))
                   (mult_vec3 (vec3 a11 a12 a13) (vec3 b12 b22 b32))
                   (mult_vec3 (vec3 a11 a12 a13) (vec3 b13 b23 b33)))
             (vec3 (mult_vec3 (vec3 a21 a22 a23) (vec3 b11 b21 b31))
                   (mult_vec3 (vec3 a21 a22 a23) (vec3 b12 b22 b32))
                   (mult_vec3 (vec3 a21 a22 a23) (vec3 b13 b23 b33)))
             (vec3 (mult_vec3 (vec3 a31 a32 a33) (vec3 b11 b21 b31))
                   (mult_vec3 (vec3 a31 a32 a33) (vec3 b12 b22 b32))
                   (mult_vec3 (vec3 a31 a32 a33) (vec3 b13 b23 b33)))
  end.

Lemma unfold_mult_matrix :
  forall a11 a12 a13 a21 a22 a23 a31 a32 a33 b11 b12 b13 b21 b22 b23 b31 b32 b33 : Z,
    mult_matrix (matrix (vec3 a11 a12 a13) 
                        (vec3 a21 a22 a23) 
                        (vec3 a31 a32 a33))
                (matrix (vec3 b11 b12 b13)
                        (vec3 b21 b22 b23)
                        (vec3 b31 b32 b33)) =
    matrix (vec3 (mult_vec3 (vec3 a11 a12 a13) (vec3 b11 b21 b31))
                   (mult_vec3 (vec3 a11 a12 a13) (vec3 b12 b22 b32))
                   (mult_vec3 (vec3 a11 a12 a13) (vec3 b13 b23 b33)))
             (vec3 (mult_vec3 (vec3 a21 a22 a23) (vec3 b11 b21 b31))
                   (mult_vec3 (vec3 a21 a22 a23) (vec3 b12 b22 b32))
                   (mult_vec3 (vec3 a21 a22 a23) (vec3 b13 b23 b33)))
             (vec3 (mult_vec3 (vec3 a31 a32 a33) (vec3 b11 b21 b31))
                   (mult_vec3 (vec3 a31 a32 a33) (vec3 b12 b22 b32))
                   (mult_vec3 (vec3 a31 a32 a33) (vec3 b13 b23 b33))).
Proof.
  unfold_tactic mult_matrix.
Qed.

Theorem mult_matrix_satifies_the_specification_of_matrix_multiplication :
  specification_of_3x3_matrix_multiplication mult_matrix.
Proof.
  unfold specification_of_3x3_matrix_multiplication.
  exact unfold_mult_matrix.
Qed.

Theorem Matrix3x3_and_multiplication_is_associative :
  Associative Matrix3x3 mult_matrix eq.
Proof.
  unfold Associative.
  intros [[a11 a12 a13] 
          [a21 a22 a23] 
          [a31 a32 a33]]

         [[b11 b12 b13] 
          [b21 b22 b23] 
          [b31 b32 b33]]

         [[c11 c12 c13] 
          [c21 c22 c23] 
          [c31 c32 c33]].
  rewrite ->4 unfold_mult_matrix.
  assert (H_row : forall (a11 a12 a13 : Z)
                         (b11 b12 b13 b21 b22 b23 b31 b32 b33 : Z)
                         (c11 c21 c31 : Z),                            
                    (vec3
                       (mult_vec3 (vec3 a11 a12 a13)
                                  (vec3 (mult_vec3 (vec3 b11 b12 b13) (vec3 c11 c21 c31))
                                        (mult_vec3 (vec3 b21 b22 b23) (vec3 c11 c21 c31))
                                        (mult_vec3 (vec3 b31 b32 b33) (vec3 c11 c21 c31))))
                       (mult_vec3 (vec3 a11 a12 a13)
                                  (vec3 (mult_vec3 (vec3 b11 b12 b13) (vec3 c12 c22 c32))
                                        (mult_vec3 (vec3 b21 b22 b23) (vec3 c12 c22 c32))
                                        (mult_vec3 (vec3 b31 b32 b33) (vec3 c12 c22 c32))))
                       (mult_vec3 (vec3 a11 a12 a13)
                                  (vec3 (mult_vec3 (vec3 b11 b12 b13) (vec3 c13 c23 c33))
                                        (mult_vec3 (vec3 b21 b22 b23) (vec3 c13 c23 c33))
                                        (mult_vec3 (vec3 b31 b32 b33) (vec3 c13 c23 c33))))) =
                    (vec3
                       (mult_vec3
                          (vec3 (mult_vec3 (vec3 a11 a12 a13) (vec3 b11 b21 b31))
                                (mult_vec3 (vec3 a11 a12 a13) (vec3 b12 b22 b32))
                                (mult_vec3 (vec3 a11 a12 a13) (vec3 b13 b23 b33)))
                          (vec3 c11 c21 c31))
                       (mult_vec3
                          (vec3 (mult_vec3 (vec3 a11 a12 a13) (vec3 b11 b21 b31))
                                (mult_vec3 (vec3 a11 a12 a13) (vec3 b12 b22 b32))
                                (mult_vec3 (vec3 a11 a12 a13) (vec3 b13 b23 b33)))
                          (vec3 c12 c22 c32))
                       (mult_vec3
                          (vec3 (mult_vec3 (vec3 a11 a12 a13) (vec3 b11 b21 b31))
                                (mult_vec3 (vec3 a11 a12 a13) (vec3 b12 b22 b32))
                                (mult_vec3 (vec3 a11 a12 a13) (vec3 b13 b23 b33)))
                          (vec3 c13 c23 c33)))).
    intros a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 b8 b9 c1 c2 c3.
    unfold mult_vec3.
    assert (H_entry : forall x1 x2 x3 y1 y2 y3 y4 y5 y6 y7 y8 y9 z1 z2 z3 : Z,
                                (x1 * (y1 * z1 + y2 * z2 + y3 * z3) + 
                                 x2 * (y4 * z1 + y5 * z2 + y6 * z3) +
                                 x3 * (y7 * z1 + y8 * z2 + y9 * z3)) =
                                ((x1 * y1 + x2 * y4 + x3 * y7) * z1 + 
                                 (x1 * y2 + x2 * y5 + x3 * y8) * z2 +
                                 (x1 * y3 + x2 * y6 + x3 * y9) * z3)).
      intros; ring.                     

    rewrite ->3 H_entry.
    reflexivity.
    rewrite ->3 H_row.
    reflexivity.
    Show Proof.
Qed.

Corollary Matrix3x3_and_multiplication_is_a_semi_group :
  Semi_Group Matrix3x3 mult_matrix eq.
Proof.
  unfold Semi_Group.
  split.
  exact (eq_is_a_valid_Equal Matrix3x3).
  exact Matrix3x3_and_multiplication_is_associative.
Qed.

Definition I : Matrix3x3 :=
  matrix (vec3 1 0 0)
         (vec3 0 1 0)
         (vec3 0 0 1).

Lemma mult_matrix_I_l :
  forall A : Matrix3x3,
    mult_matrix I A = A.
Proof.
  intros [[a b c]
          [d e f]
          [g h i]].
  unfold I.
  rewrite -> unfold_mult_matrix.
  rewrite ->9 unfold_mult_vec3.
  rewrite ->9 Z.mul_0_l.
  rewrite ->10 Z.add_0_r.
  rewrite ->6 Z.add_0_l.
  rewrite ->9 Z.mul_1_l.
  reflexivity.
Qed.

Lemma mult_matrix_I_r :
  forall A : Matrix3x3,
    mult_matrix A I = A.
Proof.
  intros [[a b c]
          [d e f]
          [g h i]].
  unfold I.
  rewrite -> unfold_mult_matrix.
  rewrite ->9 unfold_mult_vec3.
  rewrite ->9 Z.mul_0_r.
  rewrite ->10 Z.add_0_r.
  rewrite ->6 Z.add_0_l.
  rewrite ->9 Z.mul_1_r.
  reflexivity.
Qed.


Theorem Matrix3x3_and_multiplication_have_a_neutral_element :
  (exists O : Matrix3x3,
     Neutral Matrix3x3 mult_matrix O eq).
Proof.
  unfold Neutral.
  exists I.
  intro A.
  split.
    exact (mult_matrix_I_r A).

    exact (mult_matrix_I_l A).
Qed.

Corollary Matrix3x3_and_multiplication_is_a_monoid :
  Monoid Matrix3x3 mult_matrix eq.
Proof.
  unfold Monoid.
  split.
  exact Matrix3x3_and_multiplication_have_a_neutral_element.
  exact Matrix3x3_and_multiplication_is_a_semi_group.
Qed.

Proposition Matrix3x3_and_multiplication_is_NOT_in_the_Abelian_Group :
  not (Abelian_Group Matrix3x3 mult_matrix eq).
Proof.  
  unfold Abelian_Group.
  unfold not.
  intros [H_comm [H_inv H_Monoid]].
  unfold Commutative in H_comm.
  assert (H_comm_absurd := H_comm (matrix (vec3 1 0 1)
                                          (vec3 0 1 0)
                                          (vec3 0 0 1))
                                  (matrix (vec3 1 0 0)
                                          (vec3 1 1 0)
                                          (vec3 0 0 1))).
    rewrite ->2 unfold_mult_matrix in H_comm_absurd.
    rewrite ->17 unfold_mult_vec3 in H_comm_absurd.
    compute in H_comm_absurd.
    discriminate.
Qed.

Lemma mult_matrix_distr_add_matrix_l :
  forall A B C: Matrix3x3,
    mult_matrix A (add_matrix B C) =
    add_matrix (mult_matrix A B) (mult_matrix A C).
Proof.
  intros [[a11 a12 a13] 
          [a21 a22 a23] 
          [a31 a32 a33]]

         [[b11 b12 b13] 
          [b21 b22 b23] 
          [b31 b32 b33]]

         [[c11 c12 c13] 
          [c21 c22 c23] 
          [c31 c32 c33]].
  rewrite -> unfold_add_matrix.
  rewrite ->3 unfold_add_vec3.
  rewrite -> unfold_mult_matrix.
  rewrite ->9 unfold_mult_vec3.
  symmetry.
  rewrite ->2 unfold_mult_matrix.
  rewrite ->18 unfold_mult_vec3.
  rewrite -> unfold_add_matrix.
  rewrite ->3 unfold_add_vec3.
  assert (H_row : forall a1 a2 a3 b1 b2 b3 c1 c2 c3 : Z,
                    (a1 * b1 + a2 * b2 + a3 * b3 + (a1 * c1 + a2 * c2 + a3 * c3)) = 
                    (a1 * (b1 + c1) + a2 * (b2 + c2) + a3 * (b3 + c3))).
   intros; ring.
 rewrite ->9 H_row.
 reflexivity.
Qed.

Lemma mult_matrix_distr_add_matrix_r :
  forall A B C: Matrix3x3,
    mult_matrix (add_matrix A B) C =
    add_matrix (mult_matrix A C) (mult_matrix B C).
Proof.
  intros [[a11 a12 a13] 
          [a21 a22 a23] 
          [a31 a32 a33]]

         [[b11 b12 b13] 
          [b21 b22 b23] 
          [b31 b32 b33]]

         [[c11 c12 c13] 
          [c21 c22 c23] 
          [c31 c32 c33]].
  rewrite -> unfold_add_matrix.
  rewrite ->3 unfold_add_vec3.
  rewrite -> unfold_mult_matrix.
  rewrite ->9 unfold_mult_vec3.
  symmetry.
  rewrite ->2 unfold_mult_matrix.
  rewrite ->18 unfold_mult_vec3.
  rewrite -> unfold_add_matrix.
  rewrite ->3 unfold_add_vec3.
  assert (H_row : forall a1 a2 a3 b1 b2 b3 c1 c2 c3 : Z,
                     (a1 * c1 + a2 * c2 + a3 * c3 + (b1 * c1 + b2 * c2 + b3 * c3)) = 
                     ((a1 + b1) * c1 + (a2 + b2) * c2 + (a3 + b3) * c3)).
   intros; ring.
 rewrite ->9 H_row.
 reflexivity.
Qed.

Theorem Matrix3x3_multiplication_distributes_over_addition :
  Distributive Matrix3x3 mult_matrix add_matrix eq.
Proof.
  unfold Distributive.
  intros A B C.
  split.
  exact (mult_matrix_distr_add_matrix_l A B C).
  exact (mult_matrix_distr_add_matrix_r A B C).
Qed.

Corollary Matrix3x3_forms_a_ring :
  Ring Matrix3x3 mult_matrix add_matrix eq.
Proof.
  unfold Ring.
  split.
    exact Matrix3x3_multiplication_distributes_over_addition.
    split.
    exact Matrix3x3_and_addition_is_an_abelian_group.
    exact Matrix3x3_and_multiplication_is_a_monoid.
Qed.

(* Please continue with Functions. *)
