Require Import SetTacticInTerm.

Set Implicit Arguments.

Class Setter {R T} (proj: R -> T) :=
  { set: T -> R -> R;
    set_get: forall v r, proj (set v r) = v;
    set_eq: forall r, set (proj r) r = r; }.
Arguments set {R T} proj {Setter}.

Notation "x [ proj := v ]" := (set proj v x)
                                (at level 12, left associativity,
                                 format "x [ proj  :=  v ]").

Ltac SetInstance_t :=
  match goal with
  | |- Setter ?A => unshelve eapply Build_Setter;
                  [ set_tac A | intros ? r; destruct r | intros r; destruct r ];
                  intros; reflexivity
  end.

Hint Extern 1 (Setter _) => SetInstance_t : typeclass_instances.

Module SimpleExample.

  Record X := mkX { A: nat;
                    B: nat;
                    C: unit }.

  Instance etaX : Updateable _ := mkUpdateable (pure mkX <*> A <*> B <*> C).

  Definition setAB a b x := x[A := a][B := b].

End SimpleExample.

Module IndexedType.
  Record X {T} := mkX { A: T;
                        B: T;
                        C: unit }.
  Arguments X T : clear implicits.

  Instance etaX T: Updateable (X T) :=
    mkUpdateable (pure (mkX (T:=T)) <*> A <*> B <*> C).

  Definition setAB T a b (x: X T) := x[A := a][B := b].

End IndexedType.
