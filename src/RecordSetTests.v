From RecordUpdate Require Import RecordSet.

Set Implicit Arguments.

Module SimpleExample.

  Record X := mkX { A: nat;
                    B: nat;
                    C: unit }.

  Instance etaX : Settable _ := settable! mkX <A; B; C>.

  Import RecordSetNotations.
  Definition setAB a b x := x[A := a][B := b].
  Definition updateAB a b x := x[A ::= plus a][B ::= minus b].

End SimpleExample.

Module IndexedType.
  Record X {T} := mkX { A: T;
                        B: T;
                        C: unit }.
  Arguments X T : clear implicits.

  Instance etaX T: Settable (X T) :=
    settable! (mkX (T:=T)) < A; B; C>.

  Import RecordSetNotations.
  Definition setAB T a b (x: X T) := x[A := a][B := b].

End IndexedType.

Module DependentExample.
  Record X := mkX { T: Type;
                    A: T;
                    B: nat }.

  Instance etaX : Settable X :=
    settable! mkX <T; A; B>.

  Import RecordSetNotations.
  Definition setB b x := x[B := b].
End DependentExample.
