Definition Reader E T := E -> T.

Definition get {E} : Reader E E := fun e => e.

Definition pure {E T} (x:T) : Reader E T := fun _ => x.

Definition ap {E A B} (f: Reader E (A -> B)) : Reader E A -> Reader E B :=
  fun x => fun e => f e (x e).

Infix "<*>" := (ap) (at level 11, left associativity).

Definition bind {E T T'} (x: Reader E T) (f: T -> Reader E T') : Reader E T' :=
  fun e => f (x e) e.

Notation "f =<< x" := (bind x f) (at level 0).

Ltac updater etaT proj :=
  let set :=
      (match eval pattern proj in etaT with
       | ?updater ?proj => constr:(fun x => updater (pure x))
       end) in
  let set := (eval cbv [pure ap] in set) in
  exact set.

Class Updateable T := { mkT: Reader T T;
                        mkT_ok: forall x, mkT x = get x }.
Arguments mkT T mk : clear implicits, rename.

Ltac prove_mkT_ok :=
  match goal with
  | |- forall x, _ = _ =>
    solve [ destruct x; cbv; f_equal ]
  end || fail "updater appears to change record".

Ltac mkUpdateable e :=
  refine {| mkT := e |};
  (match goal with
   | |- forall x, _ = _ => solve [ destruct x; cbv; f_equal ]
   end).

Notation mkUpdateable e := (ltac:(mkUpdateable e)) (only parsing).

Notation set T FA :=
  (ltac:(match constr:(mkT T _) with
         | mkT _ ?updateable =>
           let updateable := (eval hnf in updateable) in
           match updateable with
           | {| mkT := ?mk |} =>
             updater mk FA
           end
         end))
    (only parsing).

Module Example.

  Record X := mkX { A : nat;
                    B: nat;
                    C: unit; }.

  Instance etaX : Updateable _ := mkUpdateable (pure mkX <*> A <*> B <*> C).

  Definition setA := set X A.
  Print setA.

End Example.
