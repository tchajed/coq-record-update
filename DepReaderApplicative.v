Definition Reader E T := forall (e:E), T e.

Definition get {E} : Reader E (fun _ => E) := fun e => e.

Definition pure {E T} (x: T) : Reader E (fun _ => T) := fun e => x.
Definition deppure {E T} (x: forall e, T e) : Reader E T := fun e => x e.

Definition ap {E A B} (f: Reader E (fun e => A e -> B e)) : Reader E A -> Reader E B :=
  fun x => fun e => f e (x e).

Infix "<*>" := (ap) (at level 11, left associativity).
