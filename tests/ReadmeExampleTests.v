From RecordUpdate Require Import RecordSet.

Record X := mkX { A: nat; B: nat; C: bool; }.

(* all you need to do is provide something like this, listing out the fields of your record: *)
#[export] Instance etaX : Settable _ := settable! mkX <A; B; C>.

(* and now you can set fields! *)
Definition setAB a b x := set B (fun _ => b) (set A (fun _ => a) x).

(* and do updates that use the old value! *)
Definition updateAB a b x := set B (Nat.add b) (set A (Nat.add a) x).

(* you can also use notations for these things: *)
Import RecordSetNotations.
Definition setAB' a b x := x <|A := a|> <|B := b|>.
Definition updateAB' a b x := x <|A ::= Nat.add a|> <|B ::= Nat.add b|>.
