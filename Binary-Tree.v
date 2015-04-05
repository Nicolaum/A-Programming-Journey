Require Import Algebra Equal OwnTacts String.
Open Scope string_scope.

Inductive BT (LeafT NodeT : Type) : Type :=
  | Leaf : LeafT -> BT LeafT NodeT
  | Node : NodeT -> BT LeafT NodeT -> BT LeafT NodeT .


Definition Movie_and_copies_sold_BT : BT (nat * string) nat := (Leaf (nat * string) nat (1, "Star Wars")).

Compute Movie_and_copies_sold_BT.
