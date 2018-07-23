Require Export ReaderApplicative.

(** Updateable is a way of accessing a constructor for a record of type T. The
syntactic form of this definition is important: it must be an eta-expanded
version of T's constructor, written generically over the field accessors of T.
The best way to do this for a record X := mkX { A; B; C} is [pure mkX <*> A <*>
B <*> C]. *)
Class Updateable T := { mkT: Reader T T;
                        mkT_ok: forall x, mkT x = get x }.
Arguments mkT T mk : clear implicits, rename.

Local Ltac mkUpdateable e :=
  refine {| mkT := e |};
  (match goal with
   | |- forall x, _ = _ => solve [ destruct x; cbv; f_equal ]
   end).

(** mkUpdateable creates an instance of Updateable from an expression like [pure
mkX <*> A <*> B <*> C] *)
Notation mkUpdateable e := (ltac:(mkUpdateable e)) (only parsing).

(** [updater] creates a setter based on an eta-expanded record constructor and a
particular field projection proj *)
Local Ltac updater etaT proj :=
  let set :=
      (match eval pattern proj in etaT with
       | ?updater ?proj => constr:(fun x => updater (pure x))
       end) in
  let set := (eval cbv [pure ap] in set) in
  exact set.

(* Combining the above, [getSetter'] looks up the eta-expanded version of T with
the Updateable typeclass, and calls [updater] to create an updater. *)
Local Ltac getSetter' T proj :=
  match constr:(mkT T _) with
  | mkT _ ?updateable =>
    let updateable := (eval hnf in updateable) in
    match updateable with
    | {| mkT := ?mk |} =>
      updater mk proj
    end
  end.

(* [getSetter] looks up the record type from the projection [proj] and then
calls [getSetter'] *)
Local Ltac getSetter proj :=
  let T := match type of proj with
           | ?T -> _ => T
           end in
  getSetter' T proj.

(* [set proj] is a sets the field projected by [proj].

The record type T that [proj] accesses should have an instance Updateable T. *)
Notation set proj := (ltac:(getSetter proj)) (only parsing).

Ltac set_tac proj := getSetter proj.

Module Example.

  Record X := mkX { A : nat;
                    B: nat;
                    C: unit; }.

  Instance etaX : Updateable _ := mkUpdateable (pure mkX <*> A <*> B <*> C).

  Definition setA := set A.
  Print setA.

End Example.
