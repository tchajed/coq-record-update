From RecordUpdate Require Import RecordUpdate.

Record X := mkX { A: nat; B: nat; C: bool; }.

(* [set] operates on any record, allowing field updates *)
Definition setAB a b x := set B (fun _ => b) (set A (fun _ => a) x).

(* These updates can also make use of the original field value: *)
Definition updateAB a b x := set B (Nat.add b) (set A (Nat.add a) x).

(* You can also use notations for these things: *)
Definition setAB' (a: nat) (b: nat) x := x <|A := a|> <|B := b|>.
Definition updateAB' a b x := x <|A ::= Nat.add a|> <|B ::= Nat.add b|>.

(* The notation also allows you to update nested fields by giving the "path"
through several records: *)
Record Inner := mkInner { n : nat }.
Record Middle := mkMiddle { c : Inner }.
Record Outer := mkOuter { b : Middle }.

Definition setNested n' (x: Outer) := x <| b; c; n := n' |>.
Definition incNested (x: Outer) := x <| b; c; n ::= S |>.
