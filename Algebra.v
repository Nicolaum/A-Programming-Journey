Require Import Equal.

(* Algebraic Groups *)

(* A semigroup is a structure which is associative for a function and a Type.  *)
(* Which gives us the knowledge that the order of computation                  *)
(* do not have influence of the results, Which makes program that              *)
(* satifies being a semigroup able to run concurrent, accros                   *)
(* multiple cpu's, even in a distributed system.                               *)

Definition Associative (T           : Type)
                       (application : T -> T -> T)
                       (equal       : T -> T -> Prop) : Prop :=
  forall e1 e2 e3 : T,
    equal 
      (application e1 (application e2 e3 )) 
      (application (application e1 e2) e3).

Definition Semi_Group (T        : Type)
                     (application : T -> T -> T)
                     (equal : (T -> T -> Prop)) :=
  Equal T equal /\
  Associative T application equal.

(* A monoid is a structure with a neutral element, which makes us able to   *)
(* have the notion of an option, which makes us able to do noting in a      *)
(* computation.                                                             *)

Definition Neutral (T : Type)
                  (application : T -> T -> T)
                  (O           : T)
                  (equal    : T -> T -> Prop) : Prop :=
  forall e : T,
    equal (application e O) e /\
    equal (application O e) e.

Definition Monoid (T           : Type)
                  (application : T -> T -> T)
                  (equal       : T -> T -> Prop) : Prop :=
  (exists (O : T), Neutral T application O equal) /\
  (Semi_Group T application equal).

Lemma The_natual_element_is_unique :
  forall (T : Type)
         (application : T -> T -> T)
         (equal : T -> T -> Prop),
    Equal T equal ->
    forall (O1 O2 : T), 
      Neutral T application O1 equal ->
      Neutral T application O2 equal ->
      equal O1 O2.
Proof.
  intro T.
  intros application equal.
  intro H_eq.
  intros O1 O2.
  unfold Neutral.
  intros H_neutral H_neutral'.
  destruct (H_neutral O2) as [H_eq_r _].
  destruct (H_neutral' O1) as [_ H_eq_l].
  unfold Equal in H_eq.
  destruct H_eq as [H_ref [H_sym H_trans]].
  unfold Symmetric in H_sym.
  unfold Transitive in H_trans.
  unfold Reflexive in H_ref.
  apply (H_sym (application O2 O1) O1) in H_eq_l. 
  exact (H_trans O1 (application O2 O1) O2 H_eq_l H_eq_r).
Qed.

(* The Abelian group is commutiative, so suddenly the order *)
(* we write our code does not matter anymore and has an inverse   *)
(* which means that we can start to remove stuff                  *)

Definition Commutative (T           : Type)
                       (application : T -> T -> T)
                       (equal       : T -> T -> Prop) : Prop :=
  forall e1 e2 : T,
    equal
      (application e1 e2)
      (application e2 e1).

Definition Inverse (T           : Type)
                   (application : T -> T -> T)
                   (equal       : T -> T -> Prop) : Prop :=
    forall e : T,
    exists (O : T)
           (Inv : T),
      equal
        (application e Inv)
        O.

Definition Abelian_Group (T           : Type)
                         (application : T -> T -> T)
                         (equal       : T -> T -> Prop) : Prop :=
  
  (Commutative T application equal) /\
  (Inverse T application equal) /\
  (Monoid T application equal).

(* A type forms a ring if it has a addition function which in the Abelian Group, *)
(* a monadic multiplication function and that multiplication distributes over   *)
(* addition. Rings are really nice, since we can automate a proof, if the type  *)
(* forms a ring. *)

Definition Distributive (T : Type) 
                        (multiplication : T -> T -> T) 
                        (addition : T -> T -> T) 
                        (equal : T -> T -> Prop) :=
  forall e1 e2 e3 : T,
    equal (multiplication e1 (addition e2 e3))
          (addition (multiplication e1 e2) (multiplication e1 e3)) /\
    equal (multiplication (addition e1 e2) e3)
          (addition (multiplication e1 e3) (multiplication e2 e3)).

Definition Ring (T : Type) 
                (multiplication : T -> T -> T) 
                (addition : T -> T -> T) 
                (equal : T -> T -> Prop) :=
  Distributive T multiplication addition equal /\
  Abelian_Group T addition equal /\
  Monoid T multiplication equal.

(* Please continue with Booleans. *)
