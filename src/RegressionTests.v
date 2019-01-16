From RecordUpdate Require Import RecordSet.
Import ApplicativeNotations RecordSetNotations.

Module GH2.
  Record X := mkX { A: nat;}.

  Instance etaX : Settable _ := mkSettable (constructor mkX <*> A)%set.

  (* name r should not prevent finding a Setter A instance *)
  Definition setA (r : nat) x := x[A := 32].
End GH2.
