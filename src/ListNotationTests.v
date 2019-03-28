From RecordUpdate Require Import RecordSet.
Require Import List.

Import ListNotations.
Import RecordSetNotations.

Module GH4.

  Record foo := { a : bool ;
                  b : bool }.

  Global Instance etaX_RtlExprs : Settable _ :=
    settable!
            Build_foo <a; b>.


  Definition bar := {| a := true ; b := true |}.
  Definition baz := bar<|a := false|>.

End GH4.

Definition l := [1; 2; 3].
Record foo := { a : list nat;
                b : list bool; }.

Instance eta_foo : Settable _ := settable! Build_foo <a; b>.
Definition m_foo (x:foo) := x <| a := [1;2;3] |> <| b := [] |>.
