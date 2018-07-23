Require Import SetTacticInTerm.

Set Implicit Arguments.

Class Setter {R T} (proj: R -> T) :=
  { set: T -> R -> R;
    set_get: forall v r, proj (set v r) = v;
    set_eq: forall r, set (proj r) r = r; }.
Arguments set {R T} proj {Setter}.

Ltac SetInstance_t :=
  match goal with
  | |- Setter ?A => unshelve eapply Build_Setter;
                  [ set_tac A | intros ? r; destruct r | intros r; destruct r ];
                  intros; simpl; eauto
  end.

Notation SetInstance := ltac:(SetInstance_t) (only parsing).

Notation "x [ proj := v ]" := (set proj v x)
                                (at level 12, left associativity,
                                format "x [ proj  :=  v ]").

Module SimpleExample.

  Record X := mkX { A: nat;
                    B: nat;
                    C: unit }.

  Instance etaX : Updateable _ := mkUpdateable (pure mkX <*> A <*> B <*> C).

  Instance fA: Setter A := SetInstance.
  Instance fB: Setter B := SetInstance.
  Instance fC: Setter C := SetInstance.

  Definition setAB a b x := x[A := a][B := b].

End SimpleExample.

Module IndexedType.
  Record X {T} := mkX { A: T;
                        B: T;
                        C: unit }.
  Arguments X T : clear implicits.

  Instance etaX T: Updateable (X T) :=
    mkUpdateable (pure (mkX (T:=T)) <*> A <*> B <*> C).

  Instance fA T : Setter (@A T) := SetInstance.
  Instance fB T : Setter (@B T) := SetInstance.
  Instance fC T : Setter (@C T) := SetInstance.

  Definition setAB T a b (x: X T) := x[A := a][B := b].

End IndexedType.
