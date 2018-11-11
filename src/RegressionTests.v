From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Module GH2.
  Record X := mkX { A: nat;}.

  Instance etaX : Settable _ := mkSettable (pure mkX <*> A).

  (* name r should not prevent finding a Setter A instance *)
  Definition setA (r : nat) x := x[A := 32].
End GH2.
