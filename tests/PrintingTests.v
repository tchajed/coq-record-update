From RecordUpdate Require Import RecordUpdate.

Record X := mkX { A: nat; B: nat; }.
Instance etaX : Settable _ := settable! mkX <A; B>.

Definition setA (x:X) n := x <|B:=n|>.
Print setA.

Definition updateA (x:X) n := x <|B::=Nat.add n|>.
Print updateA.

Record Nested := mkNested { anX: X; aNat: nat; }.
Instance etaNested : Settable _ := settable! mkNested <anX; aNat>.

Definition setXB (n:Nested) := n <|anX; B:=3|>.
Print setXB.

Definition updateXB (n:Nested) := n <|anX; B::=S|>.
Print updateXB.
