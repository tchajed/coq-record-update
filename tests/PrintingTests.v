From RecordUpdate Require Import RecordUpdate.

Record X := mkX { A: nat; B: nat; }.
#[export] Instance etaX : Settable _ := settable! mkX <A; B>.

Definition setA (x:X) n := x <|B:=n|>.
Print setA.

Definition updateA (x:X) n := x <|B::=Nat.add n|>.
Print updateA.

Record Nested := mkNested { anX: X; aNat: nat; }.
#[export] Instance etaNested : Settable _ := settable! mkNested <anX; aNat>.

Definition setXB (n:Nested) := n <|anX; B:=3|>.
Print setXB.

Definition updateXB (n:Nested) := n <|anX; B::=S|>.
Print updateXB.

Lemma test_reduction :
  (mkNested (mkX 2 3) 7) <|aNat := 4|> =
  mkNested (mkX 2 3) 4.
Proof.
  (* this should reduce the LHS to the RHS *)
  simpl. Show.
  reflexivity.
Qed.

Lemma test_reduction2 :
  (mkNested (mkX 2 3) 7) <|anX := mkX 3 2|> <|aNat := 1|> =
  mkNested (mkX 3 2) 1.
Proof.
  (* this should reduce the LHS to the RHS *)
  cbn. Show.
  reflexivity.
Qed.
