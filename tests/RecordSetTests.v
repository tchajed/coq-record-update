From RecordUpdate Require Import RecordSet.

Set Implicit Arguments.

Module SimpleExample.

  Record X := mkX { A: nat;
                    B: nat;
                    C: unit }.

  Instance etaX : Settable _ := settable! mkX <A; B; C>.

  Import RecordSetNotations.
  Definition setAB a b x := x <|A := a|> <|B := b|>.
  Definition updateAB a b x := x <|A ::= plus a|> <|B ::= minus b|>.

End SimpleExample.

Module IndexedType.
  Record X {T} := mkX { A: T;
                        B: T;
                        C: unit }.
  Arguments X T : clear implicits.

  Instance etaX T: Settable (X T) :=
    settable! (mkX (T:=T)) < A; B; C>.

  Import RecordSetNotations.
  Definition setAB T a b (x: X T) := x <|A := a|> <|B := b|>.

End IndexedType.

Module DependentExample.
  Record X := mkX { T: Type;
                    A: T;
                    B: nat }.

  Instance etaX : Settable X :=
    settable! mkX <T; A; B>.

  Import RecordSetNotations.
  Definition setB b x := x <|B := b|>.
End DependentExample.

Module WellFormedExample.

  Record X := mkX { A: nat;
                    B: nat;
                    C: unit }.

  Instance etaX : Settable _ := settable! mkX <A; B; C>.

  Definition setAB a b x := set A (fun _ => a) (set B (fun _ => b) x).

  (* Resolving an instance for SetterWf proves some correctness properties of
  the setter. You can also require constructing this instance by accessing the
  setter through set_wf. *)
  Instance set_A : SetterWf A.
  Proof.
    apply _.
  Qed.

  Definition setAB_wf a b x := set_wf A (fun _ => a) (set_wf B (fun _ => b) x).
End WellFormedExample.

Module DependentWfExample.
  Record X := mkX { T: Type;
                    A: T;
                    B: nat }.

  Instance etaX : Settable X :=
    settable! mkX <T; A; B>.

  Instance set_A : SetterWf B.
  Proof.
    apply _.
  Qed.
End DependentWfExample.

Module NestedExample.
  Record C := mkC { n : nat }.
  Record B := mkB { c : C }.
  Record A := mkA { b : B }.

  Instance etaC : Settable _ := settable! mkC<n>.
  Instance etaB : Settable _ := settable! mkB<c>.
  Instance etaA : Settable _ := settable! mkA<b>.

  Import RecordSetNotations.
  Definition setNested n' x := x <| b; c; n := n' |>.
End NestedExample.

Module TypeParameterExample.
  Record X T := mkX { a: nat; b: T; c: T * T; }.
  Arguments a {T}.
  Arguments b {T}.
  Arguments c {T}.

  Instance etaX T : Settable _ := settable! (@mkX T) <a;b;c>.

  Import RecordSetNotations.
  Definition set_a (x:X unit) := x <| a := 3 |>.
  Definition set_b (x:X unit) := x <| b := tt |>.
  Definition set_b' {T} (x:X T) (v:T) := x <| b := v |>.
  Definition set_c {T} (x:X T) (v:T) := x <| c := (v,v) |>.
End TypeParameterExample.

Module TypeParameterLimitation.
  Record X T := mkX { a: nat; b: T; }.
  Arguments a {T}.
  Arguments b {T}.

  Instance etaX T : Settable _ := settable! (@mkX T) <a;b>.

  Import RecordSetNotations.
  Definition set_a (x:X unit) := x <| a := 3 |>.
  Definition set_b {T} (x:X T) (v:T) := x <| b := v |>.

  (* unsupported by RecordUpdate: the pattern trick could do this in principle,
  but the type of [set] in the [Setter] typeclass is too restrictive to allow
  the change in X's type.

  We could give [Setter] a broader type (where the type of the record can
  change), but then I'd worry about type inference being underconstrained in the
  common case. *)
  Definition strong_update_to_b {T1 T2} (x: X T1) (v: T2) : X T2 :=
    mkX (a x) v.
End TypeParameterLimitation.
