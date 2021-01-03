(*|
============================
How coq-record-update works
============================

A detailed explanation of how coq-record-update is implemented. This is a re-implementation that omits the safety checks in the actual implementation, so that the basic story is as clear as possible.

This explanation interleaves a simplified re-implementation of the library with demo modules that demonstrate features as they are added. These demo modules each import the previous, but we hide that command to avoid cluttering the output.

First, our basic goal is to implement the following typeclass for each record type `R` and projection function `proj`. The implicit arguments are set up so that setting a field `A` is as simple as `set A (fun a => a + 1) x`, which will increment the field `A` in a record `x`.
|*)

Class Setter {R T:Type} (proj: R -> T) :=
  set : (T -> T) -> (R -> R).

Arguments set {R T} proj {_} _ _ : assert.
Global Hint Mode Setter - - + : typeclass_instances.

Module demo1.

(*|
My favorite running example, a simple record with three fields.
|*)

  Record X := mkX { A: nat; B: nat; C: bool; }.

(*|
With just the above definition, we would still need to implement the typeclass for every field of every record. Here's the particular form of implementation that we'll automate with this library.
|*)

  Instance setA : Setter A :=
    fun (f:nat -> nat) (x:X) => mkX (f (A x)) (B x) (C x).
  Instance setB : Setter B :=
    fun (f:nat -> nat) (x:X) => mkX (A x) (f (B x)) (C x).
  Instance setC : Setter C :=
    fun (f:bool -> bool) (x:X) => mkX (A x) (B x) (f (C x)).
End demo1.

(*|
The basis for the automation will be to extract the common parts of the above, an "eta expansion" that doesn't set any fields but reconstructs a record from all of its fields. The user will provide the eta expansion by implementing the `Settable` typeclass.
|*)

Class Settable (R: Type) :=
  mkRecord : R -> R.

Arguments mkRecord R _ _ : assert, clear implicits.
Global Hint Mode Settable + : typeclass_instances.

Module demo2.
  Import demo1. (* .none *)

(*|
Here's how we intend to implement `Settable`. This is equal to `fun x => x`, but we won't actually call `mkRecord`, instead we'll look up the implementation of `Settable` and actually look at the definition (rather than using the instances opaquely).
|*)

  Instance etaX : Settable X :=
    fun x => mkX (A x) (B x) (C x).
End demo2.

(*|
Looking up a typeclass instance is pretty simple if you think about it: we just typecheck `_ : Settable R`, which will trigger typeclass resolution to fill in the underscore!
|*)

Ltac get_eta R :=
  let eta := eval hnf in (_ : Settable R) in
  eta.

(*|
Given an eta expansion (recall they look like `fun x => mkX (A x) (B x) (C
x)`), we want to substitute an update function in the place of some projection
function `proj`. The way we can do that is with the `pattern` tactic.

Let's say we call `make_setter eta B`, where `eta` is the above eta expansion.
`setter_r` factors it into `(fun B_f => mkX (A x) (B_f x) (C x)) B`. This is
almost what we want, except the `set` function doesn't allow any function of the
whole record, only of `B x`, so we actually use `fun r => f (B r)` as the
replacement for `B` (note that this is just `f ∘ B`, expanded out).
|*)

Ltac make_setter eta proj :=
  let setter_r := (eval pattern proj in eta) in
  lazymatch setter_r with
  | ?set_f _ =>
    let setter := constr:(fun f => set_f (fun r => f (proj r))) in
    (* we can clean up the actual setter term by beta-reducing it *)
    let setter := (eval cbn beta in setter) in
    setter
  end.

Module demo3.
  Import demo1 demo2. (* .none *)

(*|
Let's see what the above tactics do before we tie everything together into a nice user interface.

Recall that we've already implemented `Settable X`, so `get_eta X` can look it up.
|*)

  Goal True. (* .in .messages *)
    let eta := get_eta X in
    idtac eta. (* .in .messages .unfold *)
    let eta := get_eta X in
    let setter_B := make_setter eta B in
    idtac setter_B. (* .in .messages .unfold *)
  Abort.

End demo3.

(*|
Finally, we want to use `make_setter` without any fancy syntax. The way we do that is to implement the `Setter` typeclass using Ltac, rather than the usual mechanism of adding definitions as instances. Instance resolution turns out to just be a (slightly modified) `eauto` search using the `typeclass_instances` hint database, so we can register a `Hint Extern` to use `make_setter` to resolve `Setter`.

First we package up `get_eta` and `make_setter` into a single tactic that will solve goals of the form `Setter proj`, as long as `Settable` is implemented for the relevant record type.
|*)

Ltac solve_setter R proj :=
  let eta := get_eta R in
  let setter := make_setter eta proj in
  exact setter.

(*|
Now we add `solve_setter` as a way to prove `Setter` during typeclass resolution.
|*)

Global Hint Extern 1 (@Setter ?R _ ?proj) =>
         solve_setter R proj : typeclass_instances.

(*|
To make the library usable, we provide a notation that builds the eta expansion from a list of record fields, which is much easier to type than the actual eta expansion.
|*)

Notation "'settable!' mk < f1 ; .. ; fn >" :=
  (fun x => .. (mk (f1 x)) .. (fn x))
    (at level 0, mk at level 10, f1, fn at level 9, only parsing).

Module demo4.
  Import demo1. (* .none *)

(*|
Before we had to write out the expansion of X carefully; now we can just list out the constructor and fields:
|*)

  Instance etaX : Settable _ := settable! mkX <A;B;C>.
End demo4.

(*|
We also provide notations for the `set` function that make multiple updates, and updates to constants easier to read and write.
|*)

Notation "x <| proj ::= f |>" :=
  (set proj f x)
    (at level 12, f at next level, left associativity,
    format "x  <| proj  ::=  f |>").
Notation "x <| proj := v |>" :=
  (set proj (fun _ => v) x)
    (at level 12, left associativity,
    format "x  <| proj  :=  v |>").

Module test.
  Record X := mkX { A: nat;
                    B: nat;
                    C: unit }.

  Instance eta : Settable X := settable! mkX <A;B;C>.

  Definition setAB a b x := x <|A := a|> <|B := b|>.
  Definition updateAB a b x := x <|A ::= plus a|> <|B ::= minus b|>.
End test.
