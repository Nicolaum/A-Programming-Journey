(* Tactics : *)

(* 
  The unfold tactic is used when we have implemented a function 
according to some specification a we want a Lemma about, what 
the function do depending on the input.
 *)

Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.
