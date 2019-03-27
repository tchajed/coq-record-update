From RecordUpdate Require Import RecordUpdate.

Module GH2.
  Record X := mkX { A: nat;}.

  Instance etaX : Settable _ := settable! mkX <A>.

  (* name r should not prevent finding a Setter A instance *)
  Definition setA (r : nat) x := x[A := 32].
End GH2.
