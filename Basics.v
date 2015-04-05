(* Coq is a proof assistant, which helps proving different properties    *)
(* about types.                                                          *)

(* This is done though predicate logic, which is on the form: *)

(* form := 	True 	(True)                                           *)
(*   	| 	False 	(False)                                          *)
(*   	| 	~ form 	(not)                                            *)
(*   	| 	form /\ form 	(and)                                    *)
(*   	| 	form \/ form 	(or)                                     *)
(*   	| 	form -> form 	(primitive implication)                  *)
(*   	| 	form <-> form 	(iff)                                    *)
(*   	| 	forall ident : type , form 	(primitive for all)      *)
(*   	| 	exists ident [: specif] , form 	(ex)                     *)
(*   	| 	exists2 ident [: specif] , form & form 	(ex2)            *)
(*   	| 	term = term 	(eq)                                     *)
(*   	| 	term = term :> specif 	(eq)                             *)

Lemma proving_true :
  True.
Proof.
  Search True.     (* Search is used for searching for a lemma that states something. *)
  Check I.         (* Check is used to see what a lemma says. *)
  exact I.         (* We use exact if the goal is exactly the goal. *)
Qed.

Lemma proving_reflective_statement :
  forall A : Prop,
    A = A.
Proof.
  intro A.
  reflexivity.                  (* When we have two statements which is textually, *)
                                (* we use reflexivity to prove the proposition. *)
Qed.

Lemma proving_with_implication :
  forall A : Prop,
    A -> A.
Proof.
  intro A.                      (* We introduce variables and Hypotheis  *)
  intro H.                      (* with 'intro'.                           *)
  exact H.                      (* We use 'exact' when a hypothesis is     *)
                                (* out exact goal.                       *)

  Restart.

  intros A H.                   (* We can introduce multiple variables and hypotheisis *)
                                (* with 'intros' *)
  exact H.
Qed.

Lemma proving_symmetric_statement :
  forall A B : Prop,
    A = B -> B = A.
Proof.
  intros A B H_A_B.
  symmetry.                     (* We can use 'symmetry' to turn a proposition around '=' *)
  exact H_A_B.

  Restart.
  intros A B H_A_B.
  symmetry in H_A_B.            (* 'symmetry' can also be used in the hypothesises *)
  exact H_A_B.
Qed.

Lemma proving_transitive_statement :
  forall A B C : Prop,
    A = B -> B = C -> A = C.
Proof.
  intros A B C H_A_B H_B_C.
  rewrite -> H_A_B.             (* We use 'rewrite' to rewrite the goal with a Hypothesis *)
  exact H_B_C.

  Restart.

  intros A B C H_A_B H_B_C.
  rewrite <- H_A_B in H_B_C.    (* We can also rewrite in the hypotesis with 'in'. *)
  exact H_B_C.
Qed.

Lemma proving_using_apply :
  forall A B C : Prop,
    A -> (A -> B = C) -> B = C.
Proof.
  intros A B C H_A H_A_implies_B_C.
  apply H_A_implies_B_C.        (* We can 'apply' a hypotesis, now we need to prove *)
                                (* that the left side of the implication holds. *)
  exact H_A.
Qed.

Lemma proving_not_false :
  ~ False.
Proof.
  unfold not.                   (* We use 'unfold' to get the definition of a statement. *)
  intro H.
  exact H.
Qed.

Lemma proving_conjunctions :
  forall A B : Prop,
    A -> B -> A /\ B.
Proof.
  intros A B H_A H_B.
  split.                        (* When a conjunction in the goal is meet, *)
                                (* we use 'split' to split the goal into two *)
                                (* subgoal which we should prove induvidually. *)
  exact H_A.
  exact H_B.
Qed.

Lemma proving_with_conjunction_in_hypotheis :
  forall A B : Prop,
    A /\ B -> A.
Proof.
  intros A B H_A_and_B.
  destruct H_A_and_B as [H_A H_B].  (* When we have a conjunction in the hypotheis, *)
                                    (* we use 'destruct' and a pattern [_ _] *)
  exact H_A.

  Restart.

  intros A B [H_A H_B].         (* We can also destruct directly under the introduction*)
  exact H_A.
Qed.

Lemma proving_disjunctions_left :
  forall A B : Prop,
    A -> A \/ B.
Proof.
  intros A B H_A.
  left.                         (* We use 'left' to prove the left side *)
                                (* of the disjunction. *)
  exact H_A.
Qed.

Lemma proving_disjunctions_right :
  forall A B : Prop,
    B -> A \/ B.
Proof.
  intros A B H_B.
  right.                        (* We use 'right' to prove the right side *)
                                (* of the disjunction. *)
  exact H_B.
Qed.

Lemma proving_with_disjunctions_in_hypotheisis :
  forall A B : Prop,
    A \/ B -> B \/ A.
Proof.
  intros A B H_A_or_B.
  destruct H_A_or_B as [H_A | H_B]. (* Like conjunction, we use 'destruct', but with the *)
                                    (* pattern [ | ]. *)
  right.
    exact H_A.

  left.
    exact H_B.

  Restart.

  intros A B [H_A | H_B].       (* We can also destruct the hypotheis directly. *)
  
  right.
    exact H_A.

  left.
    exact H_B.
Qed.

Lemma proving_a_bi_implication :
  forall A B : Prop,
    A = B <-> B = A.
Proof.
  intros A B.
  split.                        (* Like conjunction we use 'split' to split the *)
                                (* bi implication into two goals. *)
                                (* This works because a bi implication is defined as: *)
                                (* A <-> B = A -> B /\ B -> A. *)
    intro H_A_B.
    symmetry.
    exact H_A_B.

    intro H_B_A.
    symmetry in H_B_A.            
    exact H_B_A.
Qed.

Lemma proving_that_an_element_exists :
  exists A : Prop,
    A = True.
Proof.
  exists True.                  (* We use 'exists' when we have exists in the goal. *)
  reflexivity.
Qed.

Lemma proving_with_exists_in_hypotesis :
  forall A : Prop,
    (exists B : Prop, A /\ B) -> A.
Proof.
  intros A H_exists_B_A_B.
  destruct H_exists_B_A_B as [B [H_A H_B]]. (* We use 'destruct' of we have exists in hypothesis *)
  exact H_A.
Qed.

Lemma proving_absurdities :
  forall A : Prop,
    False -> A.
Proof.
  intros A H_Absurd.
  contradiction H_Absurd.       (* We use 'contradiction' if we have a false hypothesis *)
Qed.

Lemma proving_similar_sub_goals :
  forall A : Prop,
    A -> (A /\ A) /\ (A /\ A).
Proof.
  intros A H_A.
  split.
    split.
      exact H_A.
      exact H_A.
    split.
      exact H_A.
      exact H_A.

  Restart.                      (* It is seen that we the proof for each sub goal is *)
                                (* exactly the same, to do something on each sub goal, *)
                                (* we can use ';' which apply the next tactic to  *)
                                (* each subgoal. *)
  intros A H_A; split; split; exact H_A.
Qed.

Lemma proving_nearly_similar_sub_goals :
  forall A B : Prop,
    A -> B -> (A /\ B) /\ (B /\ A).
Proof.
  intros A B H_A H_B.
  split.
    split.
      exact H_A.
      exact H_B.
  
    split.
      exact H_B.
      exact H_A.

  Restart.                      (* We can again use ';' to prove this. *)
                                (* But it is not the same hypothesis we *)
                                (* Apply in each sub goal. *)

  intros A B H_A H_B; split; split.
    exact H_A.
    exact H_B.
    exact H_B.
    exact H_A.

  Restart.                      (* We can however use the pattern (tac1 || tac2) *)
                                (* Where coq starts tries each tactic until it *)
                                (* the sub goal is proved. *)
  intros A B H_A H_B; split; split; (exact H_A || exact H_B).
Qed.

Lemma exercise_1 :
  forall A B C D E F : Prop,
    A -> (A -> (B /\ C)) -> (B -> D) -> (C -> E) -> E = F -> F /\ D.
Proof.           
Abort.

(* Write more exercises! *)

(* Please continue with Equal. *)
