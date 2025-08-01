From RecordUpdate Require Import RecordEta.
Set Implicit Arguments.

(** Settable is a way of accessing a constructor for a record of type T. The
syntactic form of this definition is important: it must be an eta-expanded
version of T's constructor, written generically over the field accessors of T.
The best way to do this for a record X := mkX { A; B; C} is
[settable! mkX <A; B; C>]. *)
Class Settable T := { mkT: T -> T;
                      mkT_ok: forall x, mkT x = x }.
Arguments mkT T mk : clear implicits, rename.

Local Ltac solve_mkT_ok :=
  lazymatch goal with
  | [ |- forall x, _ = _ ] =>
    first [ solve [ let x := fresh "x" in
                    intro x; destruct x; reflexivity ]
          | fail 1 "incorrect settable! declaration (perhaps fields are out-of-order?)" ]
  end.

(** settable! creates an instance of Settable from a constructor and list of
fields. *)
Notation "'settable!' mk < f1 ; .. ; fn >" :=
  (Build_Settable
     (fun x => .. (mk (f1 x)) .. (fn x))
     ltac:(solve_mkT_ok)) (at level 0, mk at level 10, f1, fn at level 9, only parsing).

Ltac solve_settable :=
  lazymatch goal with
  | |- Settable ?R =>
      let eta := RecordEta.eta R in
      refine (Build_Settable eta ltac:(solve_mkT_ok))
  | _ => fail "not a Settable goal"
  end.

#[global]
Hint Extern 2 (Settable ?R) => solve_settable : typeclass_instances.

(** [setter] creates a setter based on an eta-expanded record constructor and a
particular field projection proj *)
Local Ltac setter etaT proj :=
  lazymatch etaT with
  | context[proj] => idtac
  | _ => fail 1 proj "is not a field"
  end;
  let set :=
      (match eval pattern proj in etaT with
       | ?setter _ => constr:(fun f => setter (fun r => f (proj r)))
       end) in
  exact set.

(* Combining the above, [getSetter'] looks up the eta-expanded version of T with
the Settable typeclass, and calls [setter] to create a setter. *)
Local Ltac get_setter T proj :=
  match constr:(mkT T _) with
  | mkT _ ?updateable =>
    let updateable := (eval hnf in updateable) in
    match updateable with
    | {| mkT := ?mk |} =>
      setter mk proj
    end
  end.

(* Setter provides a way to change a field given by a projection function, along
with correctness conditions that require the projected field and only the
projected field is modified. *)
Class Setter {R T} (proj: R -> T) := set : (T -> T) -> R -> R.
(* This command sets implicits and controls reduction behavior. [set] reduces
under [simpl] and [cbn] if supplied all its arguments and the last argument (the
record) is a constructor. *)
#[global] Arguments set {R T} proj {Setter} _ !_ / : simpl nomatch.

Class SetterWf {R T} (proj: R -> T) :=
  { set_wf : Setter proj;
    set_get: forall v r, proj (set proj v r) = v (proj r);
    set_eq: forall f r, f (proj r) = proj r -> set proj f r = r; }.
#[global] Existing Instance set_wf.

Arguments set_wf {R T} proj {SetterWf}.

Local Ltac SetterInstance_t :=
  match goal with
  | |- @Setter ?T _ ?A => get_setter T A
  end.

Local Ltac SetterWfInstance_t :=
  match goal with
  | |- @SetterWf ?T _ ?A =>
    unshelve notypeclasses refine (Build_SetterWf _ _ _);
    [ get_setter T A |
      let r := fresh in
      intros ? r; destruct r; reflexivity |
      let f := fresh in
      let r := fresh in
      intros f r; destruct r; cbv [set]; cbn; intros ->; reflexivity ]
  end.

Global Hint Extern 1 (Setter _) => SetterInstance_t : typeclass_instances.
Global Hint Extern 1 (SetterWf _) => SetterWfInstance_t : typeclass_instances.

Module RecordSetNotations.
  Declare Scope record_set.
  Delimit Scope record_set with rs.
  Open Scope rs.
  Notation "x <| proj  ::=  f |>" := (set proj f x)
                                     (at level 12, f at next level, left associativity) : record_set.
  Notation "x <| proj  :=  v |>" := (set proj (fun _ => v) x)
                                    (at level 12, left associativity) : record_set.
  Notation "x <| proj1 ; proj2 ; .. ; projn ::= f |>" :=
    (set proj1 (set proj2 .. (set projn f) ..) x)
    (at level 12, f at next level, left associativity) : record_set.
  (* TODO: this notation and the one above have a common prefix. They do still
  have an effect, so the warning is disabled for now. *)
  Notation "x <| proj1 ; proj2 ; .. ; projn := v |>" :=
    (set proj1 (set proj2 .. (set projn (fun _ => v)) ..) x)
    (at level 12, left associativity) : record_set.
End RecordSetNotations.
