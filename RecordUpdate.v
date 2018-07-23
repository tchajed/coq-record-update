Definition Reader E T := E -> T.

Definition get {E} : Reader E E := fun e => e.

Definition pure {E T} (x:T) : Reader E T := fun _ => x.

Definition ap {E A B} (f: Reader E (A -> B)) : Reader E A -> Reader E B :=
  fun x => fun e => f e (x e).

Infix "<*>" := (ap) (at level 11, left associativity).

Definition bind {E T T'} (x: Reader E T) (f: T -> Reader E T') : Reader E T' :=
  fun e => f (x e) e.

Notation "f =<< x" := (bind x f) (at level 0).

Ltac prove_updater_ok :=
  match goal with
  | |- forall x, _ = _ =>
    solve [ destruct x; cbv; f_equal ]
  end || fail "updater appears to change record".

Ltac updater t proj :=
  let t := eval hnf in t in
  let set :=
      (match eval pattern proj in t with
       | ?updater ?getter => constr:(fun x => updater (pure x))
       end) in
  let set := (eval cbv [pure ap] in set) in
  exact set.

Tactic Notation "_updater" constr(t) constr(proj) := updater t proj.

Notation mkUpdater x proj := ltac:(_updater x proj).

Module Example.

  Record X := mkX { A : nat;
                    B: nat;
                    C: unit; }.

  Class Recordy T := mkT : Reader T T.
  Arguments mkT T mk : clear implicits, rename.

  Instance etaX : Recordy X := pure mkX <*> A <*> B <*> C.

  Notation set T FA :=
    (ltac:(match constr:(mkT T _) with
          | mkT _ ?mk => updater mk FA
          end)) (only parsing).

  Definition setA := set X A.

End Example.
