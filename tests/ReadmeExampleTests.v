From RecordUpdate Require Import RecordSet.

Record X := mkX { A: nat; B: nat; C: bool; }.

(* all you need to do is provide something like this, listing out the fields of your record: *)
#[export] Instance etaX : Settable _ := settable! mkX <A; B; C>.

(* and now you can update fields! *)
Definition setAB x a b := set B (set A x a) b.

(* you can also use a notation for the same thing: *)
Import RecordSetNotations.
Definition setAB' a b x := x <|A := a|> <|B := b|>.
