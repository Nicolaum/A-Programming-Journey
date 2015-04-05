Require Import Algebra Tactics Equal.

CoInductive Lazy_List (T : Type) : Type :=
| lazy_nil : Lazy_List T
| lazy_cons : T -> Lazy_List T -> Lazy_List T.

CoInductive Bisimilar_Lazy_List (T : Type) : Lazy_List T -> Lazy_List T -> Prop :=
| Bisimilar_Lazy_List_Nil : 
    Bisimilar_Lazy_List T (lazy_nil T) (lazy_nil T)
| Bisimilar_Lazy_List_Cons :
    forall (x1 x2 : T) (x1s x2s : Lazy_List T),
      x1 = x2 ->
      Bisimilar_Lazy_List T x1s x2s ->
      Bisimilar_Lazy_List T (lazy_cons T x1 x1s) (lazy_cons T x2 x2s).

Definition decompose_Lazy_List (T : Type) (xs : Lazy_List T) :=
  match xs with
    | lazy_nil => lazy_nil T
    | lazy_cons x xs' => lazy_cons T x xs'
  end.

Lemma unfold_decompose_Lazy_List_Nil :
  forall T : Type,
    decompose_Lazy_List T (lazy_nil T) = (lazy_nil T).
Proof.
  unfold_tactic decompose_Lazy_List.
Qed.

Lemma unfold_decompose_Lazy_List_Cons :
  forall (T : Type) (x : T) (xs' : Lazy_List T),
    decompose_Lazy_List T (lazy_cons T x xs') = lazy_cons T x xs'.
Proof.
  unfold_tactic decompose_Lazy_List.
Qed.

Theorem decomposition_Lazy_List :
  forall (T : Type) (xs : Lazy_List T),
    xs = decompose_Lazy_List T xs.
Proof.
  intro T; intros [ | n ns']; unfold decompose_Lazy_List; reflexivity.
Qed.

Lemma Bisimilar_Lazy_List_is_reflexive :
  forall (T : Type) (xs : Lazy_List T),
    Bisimilar_Lazy_List T xs xs.
Proof.
  cofix coIH.
  intro T.
  intros [ | x xs'].

  exact (Bisimilar_Lazy_List_Nil T).

  apply (Bisimilar_Lazy_List_Cons T).
  reflexivity.
  exact (coIH T xs').
Qed.

Lemma Bisimilar_Lazy_List_is_symmetric :
  forall (T : Type) (xs ys : Lazy_List T),
    Bisimilar_Lazy_List T xs ys ->
    Bisimilar_Lazy_List T ys xs.
Proof.
  cofix CoIH.
  intros T xs ys H_xs_ys.
  destruct H_xs_ys as [ | x y xs' ys' H_x_y H_xs'_ys' ].
    exact (Bisimilar_Lazy_List_Nil T).
  apply (Bisimilar_Lazy_List_Cons T).
  symmetry.
  exact H_x_y.
  apply CoIH.
  exact H_xs'_ys'.
Qed.

Lemma not_Nil_and_Cons : 
  forall (T : Type) (y : T) (ys' : Lazy_List T),
    not (Bisimilar_Lazy_List T (lazy_nil T) (lazy_cons T y ys')).
Proof.
  unfold not.
  intros T y ys' H_absurd.
  remember (lazy_nil T) as xs' eqn:H_xs.  
  remember (lazy_cons T y ys') as ys eqn:H_ys.
  destruct H_absurd as [ | x' y' xs'' ys'' H_x'_y' H_xs''_ys''].
    discriminate H_ys.
  discriminate H_xs.
Qed.

Lemma converse_of_Bisimilar_Cons :
  forall (T : Type) 
         (x y : T) 
         (xs' ys' : Lazy_List T),
    Bisimilar_Lazy_List T (lazy_cons T x xs') (lazy_cons T y ys') ->
    x = y /\ Bisimilar_Lazy_List T xs' ys'.
Proof.
  intros T x y xs' ys' H.
  remember (lazy_cons T x xs') as xs eqn:H_xs.
  remember (lazy_cons T y ys') as ys eqn:H_ys.

  destruct H as [ | x' y' xs'' ys'' H_x'_y' H_xs''_ys''].
    discriminate H_xs.
  injection H_xs as H_xs''_xs' H_x'_x.
  injection H_ys as H_ys''_ys' H_y'_y.
  rewrite <- H_x'_x.
  rewrite <- H_y'_y.
  rewrite <- H_xs''_xs'.
  rewrite <- H_ys''_ys'.
  split; assumption.
Qed.

Lemma Bisimilar_Lazy_List_is_transitive :
  forall (T : Type) (xs ys zs : Lazy_List T),
    Bisimilar_Lazy_List T xs ys ->
    Bisimilar_Lazy_List T ys zs ->
    Bisimilar_Lazy_List T xs zs.
Proof.
  cofix coIH.
  intros T xs ys zs H_xs_ys H_ys_zs.
  destruct H_ys_zs as [ | y z ys' zs' H_y_z H_ys'_zs'].
    exact H_xs_ys.
  case xs as [ | x xs'].
    apply (not_Nil_and_Cons T y ys') in H_xs_ys.
    contradiction H_xs_ys.
  apply converse_of_Bisimilar_Cons in H_xs_ys.
  destruct H_xs_ys as [H_x_y H_xs'_ys'].
    apply (Bisimilar_Lazy_List_Cons T).
    rewrite <- H_y_z.
    exact H_x_y.
  exact (coIH T xs' ys' zs' H_xs'_ys' H_ys'_zs').
Qed.

Theorem Bisimilar_Lazy_List_is_valid_equal :
  forall T : Type,
    Equal (Lazy_List T) (Bisimilar_Lazy_List T).
Proof.
  intro T.
  unfold Equal.
  split.
    exact (Bisimilar_Lazy_List_is_reflexive T).
  split.
    exact (Bisimilar_Lazy_List_is_symmetric T).

    exact (Bisimilar_Lazy_List_is_transitive T).
Qed.    

Definition specification_of_lazy_append (T : Type)
             (lazy_app : Lazy_List T -> Lazy_List T -> Lazy_List T) :=
  (forall ys : Lazy_List T,
     lazy_app (lazy_nil T) ys = ys) /\
  (forall (x : T) (xs ys : Lazy_List T),
     lazy_app (lazy_cons T x xs) ys = lazy_cons T x (lazy_app xs ys)).

CoFixpoint append_Lazy_List (T : Type) (xs ys : Lazy_List T ) : Lazy_List T :=
  match xs with
    | lazy_nil => ys
    | lazy_cons x xs' => lazy_cons T x (append_Lazy_List T xs' ys)
  end.

Lemma unfold_append_Lazy_List_nil :
  forall (T : Type) (ys : Lazy_List T),
    append_Lazy_List T (lazy_nil T) ys = ys.
Proof.
  intro T.
  intros ys.
  rewrite -> (decomposition_Lazy_List T (append_Lazy_List T (lazy_nil T) ys)).
  unfold decompose_Lazy_List.
  unfold append_Lazy_List.
  destruct ys as [ | y ys']; reflexivity.
Qed.

Lemma unfold_append_Lazy_List_cons :
  forall (T : Type) (x : T) (xs' ys : Lazy_List T),
    append_Lazy_List T (lazy_cons T x xs') ys = lazy_cons T x (append_Lazy_List T xs' ys). 
Proof.
  intro T.
  intros x xs' ys.
  rewrite -> (decomposition_Lazy_List T (append_Lazy_List T (lazy_cons T x xs') ys)).
  unfold decompose_Lazy_List.
  unfold append_Lazy_List.
  reflexivity.
Qed.

Lemma append_lazy_associative :
  forall T : Type,
    Associative (Lazy_List T) (append_Lazy_List T) (Bisimilar_Lazy_List T).
Proof.
  intro T.
  unfold Associative.
      cofix CoIH.
    intros xs ys zs.
    destruct xs as [ | x xs' ].
      rewrite -> (unfold_append_Lazy_List_nil T (append_Lazy_List T ys zs)).
      rewrite -> (unfold_append_Lazy_List_nil T ys).
      exact (Bisimilar_Lazy_List_is_reflexive T (append_Lazy_List T ys zs)).

      rewrite -> (unfold_append_Lazy_List_cons T x xs' (append_Lazy_List T ys zs)).
      rewrite -> (unfold_append_Lazy_List_cons T x xs' ys).
      rewrite -> (unfold_append_Lazy_List_cons T x (append_Lazy_List T xs' ys) zs).
      apply (Bisimilar_Lazy_List_Cons T).
        reflexivity.

        exact (CoIH xs' ys zs).
Qed.

Lemma append_lazy_nil_l :
  forall (T  : Type)
         (xs : Lazy_List T),
    Bisimilar_Lazy_List T (append_Lazy_List T (lazy_nil T) xs) xs. 
Proof.
  intro T.
  intro xs.
  destruct xs as [ | x xs'].
    rewrite -> (unfold_append_Lazy_List_nil T (lazy_nil T)).
    exact (Bisimilar_Lazy_List_is_reflexive T (lazy_nil T)).

    rewrite -> (unfold_append_Lazy_List_nil T (lazy_cons T x xs')).
    exact (Bisimilar_Lazy_List_is_reflexive T (lazy_cons T x xs')).
Qed.

Lemma append_lazy_nil_r :
  forall (T  : Type)
         (xs : Lazy_List T),
    Bisimilar_Lazy_List T (append_Lazy_List T xs (lazy_nil T)) xs. 
Proof.
  intro T.
  cofix CoIH.
  intro xs.
  destruct xs as [ | l xs'].
    rewrite -> (unfold_append_Lazy_List_nil T (lazy_nil T)).
    exact (Bisimilar_Lazy_List_is_reflexive T (lazy_nil T)).

    rewrite -> (unfold_append_Lazy_List_cons T l xs' (lazy_nil T)).
    apply (Bisimilar_Lazy_List_Cons T).
      reflexivity.
          
      exact (CoIH xs').
Qed.

Theorem lazy_nil_is_neutral_for_append :
  forall T : Type,
    Neutral (Lazy_List T) (append_Lazy_List T) (lazy_nil T) (Bisimilar_Lazy_List T).
Proof.
  intro T.
  unfold Neutral.
  intro xs.
  split.
    exact (append_lazy_nil_r T xs).
 
    exact (append_lazy_nil_l T xs).
Qed.

Theorem lazy_lists_and_append_is_a_monoid :
  forall T : Type, 
    Monoid (Lazy_List T) (append_Lazy_List T) (Bisimilar_Lazy_List T).
Proof.
  intro T.
  unfold Monoid.
  split.
    exists (lazy_nil T).
    exact (lazy_nil_is_neutral_for_append T).

    unfold Semi_Group.
    split.
      exact (Bisimilar_Lazy_List_is_valid_equal T).
      exact (append_lazy_associative T).    
Qed.

Theorem natural_number_lazy_lists_with_append_is_a_monoid :
  Monoid (Lazy_List nat) (append_Lazy_List nat) (Bisimilar_Lazy_List nat).
Proof.
  exact (lazy_lists_and_append_is_a_monoid nat).
Qed.
