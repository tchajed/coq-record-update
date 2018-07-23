Definition Reader E T := E -> T.

Definition get {E} : Reader E E := fun e => e.

Definition pure {E T} (x:T) : Reader E T := fun _ => x.

Definition ap {E A B} (f: Reader E (A -> B)) : Reader E A -> Reader E B :=
  fun x => fun e => f e (x e).

Infix "<*>" := (ap) (at level 11, left associativity).
