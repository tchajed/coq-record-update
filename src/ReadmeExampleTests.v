From RecordUpdate Require Import RecordSet.

Record X := mkX { A: nat; B: nat; C: bool; }.

(* all you need to do is provide something like this, listing out the fields of your record: *)
Instance etaX : Settable _ := settable! mkX <A; B; C>.

(* and now you can update fields! *)
Definition setAB a b x := set B b (set A a x).

(* you can also use a notation for the same thing: *)
Import RecordSetNotations.
Definition setAB' a b x := x <|A := a|> <|B := b|>.
