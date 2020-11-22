From RecordUpdate Require Import RecordSet.

(* borrowed from
https://github.com/bedrocksystems/coq-lens/blob/master/theories/Lens.v, with a
function to define a field lens based on the [Setter] typeclass. This isn't as
convenient to use, since we can't generate a lens per field without the kind of
metaprograming in meta-coq or using a Coq plugin. *)

Record Lens A1 A2 T1 T2 :=
  mkLens { view : A1 -> T1;
           over : (T1 -> T2) -> (A1 -> A2);
         }.

Arguments view {_ _ _ _} _ _ : assert.
Arguments over {_ _ _ _} _ _ _ : assert.

Definition field_lens {A T} (proj: A -> T) `{!Setter proj} : Lens A A T T :=
  {| view := proj;
     over := set proj; |}.

Definition lens_compose {A1 A2 T1 T2 C1 C2}
           (l1 : Lens A1 A2 T1 T2)
           (l2 : Lens T1 T2 C1 C2) :=
  {| view x := view l2 (view l1 x);
     over f := over l1 (over l2 f);
  |}.
