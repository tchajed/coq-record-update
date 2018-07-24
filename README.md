# Coq record update library

Coq has no record update syntax, nor does it create updaters for setting individual fields of a record. This small library automates creating such updaters.

To use the library with a record, one must implement a typeclass `Settable` to provide the syntax for constructing a record from individual fields. This implementation lists out the record's constructor and every field accessor function.

Once `Settable T` is implemented, Coq will be able to resolve the typeclass `Setter F` for all the fields `F` of `T`, so that a generic setter `set T A (F: T -> A) : forall {_:Setter F}, A -> T -> T` works. There is also a notation `x [proj := v]` for calling `set proj v x`.
