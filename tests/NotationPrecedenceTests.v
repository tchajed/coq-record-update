From RecordUpdate Require Import RecordUpdate.

Module ApplicationPrecedence.
  Record Inner := mkInner { value : nat; untouched : nat }.
  Record Outer := mkOuter { inner : Inner; outer_untouched : nat }.

  Definition initial := mkInner 7 8.
  Definition initial_outer := mkOuter initial 9.
  Definition reset (_ : Inner) := mkInner 0 99.
  Definition reset_outer (_ : Outer) := mkOuter (mkInner 0 99) 88.

  (* Updates bind less tightly than application: update the returned record,
     rather than the argument passed to [reset]. *)
  Example set_application :
    reset initial <| value := 1 |> = mkInner 1 99.
  Proof. reflexivity. Qed.

  Example update_application :
    reset initial <| value ::= Nat.add 3 |> = mkInner 3 99.
  Proof. reflexivity. Qed.

  Example nested_set_application :
    reset_outer initial_outer <| inner; value := 1 |> =
    mkOuter (mkInner 1 99) 88.
  Proof. reflexivity. Qed.

  Example nested_update_application :
    reset_outer initial_outer <| inner; value ::= Nat.add 3 |> =
    mkOuter (mkInner 3 99) 88.
  Proof. reflexivity. Qed.

  (* Repeated updates apply from left to right. *)
  Example chained_updates :
    initial <| value := 1 |> <| value ::= S |> = mkInner 2 8.
  Proof. reflexivity. Qed.

  Example chained_nested_updates :
    initial_outer <| inner; value := 1 |> <| inner; value ::= S |> =
    mkOuter (mkInner 2 8) 9.
  Proof. reflexivity. Qed.

  (* The outer notation must not capture ordinary applications or partial
     applications of [set] when printing. *)
  Definition ordinary_application (f : Inner -> Inner) x := f x.
  Print ordinary_application.

  Definition setter_function := set value S.
  Print setter_function.

  Definition update_after_application x := reset x <| value := 1 |>.
  Print update_after_application.
End ApplicationPrecedence.
