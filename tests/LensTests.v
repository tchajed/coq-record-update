From RecordUpdate Require Import RecordUpdate Lens.

Record X := mkX { A: nat; B: nat; C: bool; }.
Instance etaX : Settable _ := settable! mkX <A; B; C>.

(* lenses require much more boilerplate than setters (if you want them to look
like Haskell lenses) *)
Definition _A := field_lens A.
Definition _B := field_lens B.
Definition _C := field_lens C.

Definition set_A_to_3 (x:X) := over _A (fun _ => 3) x.
