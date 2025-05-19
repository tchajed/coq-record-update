# Coq record update library

[![CI](https://github.com/tchajed/coq-record-update/actions/workflows/coq-action.yml/badge.svg)](https://github.com/tchajed/coq-record-update/actions/workflows/coq-action.yml)

In a nutshell, this library automatically provides a generic way to update record fields. Here's a teaser example:

```coq
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
```

Coq has no record update syntax, nor does it create updaters for setting individual fields of a record. This small library automates creating such updaters.

The library is based on a typeclass `Settable` that constructs a record from individual fields. It constructs this record using Ltac2.

Using `Settable T`, the library can resolve the typeclass `Setter F` for all the fields `F` of `T`, so that a generic setter `set T A (F: T -> A) : forall {_:Setter F}, A -> T -> T` works. There is also a notation `x <| proj := v |>` for calling `set proj v x`.

As a bonus, the `Setter F` typeclass includes some theorems showing the updater is correct. In addition, `Settable T` has a theorem showing that the fields are listed correctly. Together, these help catch bugs before they result in an incorrect implementation of `Setter`.

## Feedback and contributions

If you have feedback or need some improvement to make this library useful to you, **please open an issue**. I do actively maintain it.

## Building and installing

To build and install:

``` sh
git clone https://github.com/tchajed/coq-record-update.git
cd coq-record-update
make   # or make -j <number-of-cores-on-your-machine>
make install
```

## Wait, what? How does that work?

I'm glad you asked! There are three tricks here:

1. First, we represent the fields of the record. The representation is actually just an identity function for the record, but it re-constructs the record from its fields; for example, it might look like `fun x => mkX (A x) (B x) (C x)`. I think of this expression as the record's eta expansion, since it deconstructs the record and then re-assembles it.
2. The second trick is that we can take this identity function and make a small tweak to it to turn it into an updater for a single field: if we replace a field with `f: R -> T` in the eta expansion (where `R` is the record type and `T` is the field type), instead of putting the field back as-is, we can substitute some update function.

    To actually implement this substitution without doing it by hand, we use the `pattern` tactic. This is easiest to illustrate with an example: `pattern field2 in (fun x => mkX (field1 x) (field2 x) (field3 x))` evaluates to `(fun f => (fun x => mkX (field1 x) (f x) (field3 x))) field2`. The first function is essentially the updater we want! We can now extract it with a simple Ltac pattern match. We do make one tweak which is rather than allowing the user to pass any function of the whole record, of type `R -> T`, we only allow a function of the current field value, of type `T -> T`.
3. The final piece of the puzzle is to get all of this Ltac to run. Here we (abuse) typeclasses, in two ways. You might notice that the `set` function in coq-record-update is just part of the class `Setter r field`. To resolve that class, we use a tactic rather than user-provided instances, and that tactic implements the `pattern` trick --- the tactic is easy to install because typeclass resolution is just an `auto`-like search using the `typeclass_instances` hint database, and we can sneak a `Hint Extern` into that database. That's the first typeclass trick. The second is used to look up the record eta expansion when resolving `Setter r field`. Here we have the user write a typeclass `Settable r` with the eta expansion and in Ltac we look up the eta expansion and then unfold it to look at the syntax, since the actual expression is relevant and not just its use as a function. In fact, you can implement `Settable` by providing the identity function and then setting won't work because the Ltac can't do anything with it.

It's pretty cool what you can do with Coq typeclasses.
