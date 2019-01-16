# Coq record update library

[![Build Status](https://travis-ci.org/tchajed/coq-record-update.svg?branch=master)](https://travis-ci.org/tchajed/coq-record-update)

In a nutshell, this library automatically provides a generic way to update record fields. Here's a teaser example:

```coq
Require Import RecordSet.
Import ApplicativeNotations.

Record X := mkX { A: nat; B: nat; C: bool; }.

(* all you need to do is provide something like this, listing out the fields of your record: *)
Instance etaX : Settable _ := mkSettable (constructor mkX <*> A <*> B <*> C)%set.

(* and now you can update fields! *)
Definition setAB a b x := set B b (set A a x).

(* you can also use a notation for the same thing: *)
Import RecordSetNotations.
Definition setAB' a b x := x[A := a][B := b].
```

Coq has no record update syntax, nor does it create updaters for setting individual fields of a record. This small library automates creating such updaters.

To use the library with a record, one must implement a typeclass `Settable` to provide the syntax for constructing a record from individual fields. This implementation lists out the record's constructor and every field accessor function.

Once `Settable T` is implemented, Coq will be able to resolve the typeclass `Setter F` for all the fields `F` of `T`, so that a generic setter `set T A (F: T -> A) : forall {_:Setter F}, A -> T -> T` works. There is also a notation `x [proj := v]` for calling `set proj v x`.

As a bonus, the `Setter F` typeclass includes some theorems showing the updater is correct. In addition, `Settable T` has a theorem showing that the fields are listed correctly. Together, these ensure that the library cannot be used incorrectly; for `Setter` this catches potential bugs in the library, while the property in `Settable` ensures that fields aren't listed out-of-order or duplicated.
