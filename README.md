# Coq record update library

Coq has no record update syntax, nor does it create updaters for setting individual fields of a record. This small library automates creating such updaters.

To use the library with a record, one must implement a typeclass `Updateable` to provide the syntax for constructing a record from individual fields. This implementation lists out the record's constructor and every field accessor function.

Once `Updateable T` is implemented `set proj` for each projection function `proj: T -> F` of the record `T` will create a setter for that field (using Ltac via tactics-in-terms), with type `F -> T -> T`.
