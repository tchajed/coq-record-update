From RecordUpdate Require Import RecordUpdate.

Record X := mkX { A: nat; B: nat; C: bool }.
(* you can omit the X; it's there to clarify the Settable class for the paper *)
Instance: Settable X := settable! mkX <A; B; C>.

Definition add3_to_B x := set B (plus 3) x.
Definition setB_to_3 x := set B (fun _ => 3) x.
Definition setB_to_3_notation x := x <|B:=3|>.

Instance set_B : Setter B := _.

Theorem set_B_convertible_to f x :
  set_B f x =
  let a := x.(A) in
  let b' := f x.(B) in
  let c := x.(C) in
  mkX a b' c.
Proof. reflexivity. Qed.

Theorem set_B_is f x :
  set_B f x =
  mkX x.(A) (f x.(B)) x.(C).
Proof.
  unfold set_B.
  Show.
  match goal with
  | |- ?x = ?x => reflexivity
  | _ => fail 1 "not an exact match"
  end.
Qed.

Theorem simpl_behavior x :
  (set A (fun _ => 2) (set B (fun _ => 3) x)).(B) = 3.
Proof.
  simpl.
  Show.
  match goal with
  | |- ?x = ?x => reflexivity
  | _ => fail 1 "did not simplify correctly"
  end.
Qed.
