Definition arr (A:Type) (B:Type) := A -> B.
Definition imp (P Q: Prop) := P -> Q.
Definition all (A:Type) (P:A->Prop) := forall x:A, P x.

Hint Unfold imp arr all.

Infix "imp" := imp (at level 80, right associativity).
Infix "arr" := arr (at level 80, right associativity).