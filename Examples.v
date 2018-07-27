Require Import RecordSet.
Import RecordSetNotations.

Set Implicit Arguments.

Module SimpleExample.

  Record X := mkX { A: nat;
                    B: nat;
                    C: unit }.

  Instance etaX : Settable _ := mkSettable (pure mkX <*> A <*> B <*> C).

  Definition setAB a b x := x[A := a][B := b].

End SimpleExample.

Module IndexedType.
  Record X {T} := mkX { A: T;
                        B: T;
                        C: unit }.
  Arguments X T : clear implicits.

  Instance etaX T: Settable (X T) :=
    mkSettable (pure (mkX (T:=T)) <*> A <*> B <*> C).

  Definition setAB T a b (x: X T) := x[A := a][B := b].

End IndexedType.
