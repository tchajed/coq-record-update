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

Fail Definition error_not_field := set plus.

Definition get_A x := A x.
(* the Ltac produces a better error message, but typeclass resolution swallows
up the error *)
Fail Definition error_not_proj := set get_A.

Record several_nats :=
  { nat1: nat; nat2: nat; nat3: nat; }.

Definition add2 (x:several_nats) := nat1 x + nat2 x.
Definition nat1_synonym x := nat1 x.

(* fails with a typechecking error, because the constructed identity function
doesn't typecheck (we could do better by using tactics-in-terms to fail with a
custom error message) *)
Fail Instance: Settable _ := settable! Build_several_nats <nat1; nat3>.
(* fails because fields are out-of-order *)
Fail Instance: Settable _ := settable! Build_several_nats <nat1; nat3; nat2>.
(* one of these just isn't a field, so the result isn't an identity function *)
Fail Instance: Settable _ := settable! Build_several_nats <add2; nat2; nat3>.
(* this isn't intentionally supported, but now we can only set nat1 via its
synonym (actually, the only thing special about nat1 vs nat1_synonym is that Coq
auto-generated nat1) *)
Instance: Settable _ := settable! Build_several_nats <nat1_synonym; nat2; nat3>.

(* this no longer works because the Settable several_nats doesn't say anything
about nat1 *)
Fail Definition set_nat1 f (x: several_nats) := set nat1 f x.
Definition set_nat1 f (x: several_nats) := set nat1_synonym f x.
