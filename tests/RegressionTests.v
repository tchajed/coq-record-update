From RecordUpdate Require Import RecordUpdate.

Module GH2.
  Record X := mkX { A: nat;}.

  Instance etaX : Settable _ := settable! mkX <A>.

  (* name r should not prevent finding a Setter A instance *)
  Definition setA (r : nat) x := x <|A := 32|>.
End GH2.

Module GH5.
  Record X := mkX { A: nat; }.
  Instance etaX : Settable _ := settable! mkX <A>.

  Definition getA (x:X) := let 'mkX a := x in a.

  (* should not succeed, getA is not a projection *)
  Fail Definition setA (r: X) (a: nat) := set getA (fun _ => a) r.
End GH5.

Module GH10.
  Record X := mkX { A: nat; B: nat; x: bool; }.
  Instance etaX : Settable _ := settable! mkX <A; B; x>.
End GH10.

Module GH13.
  Axiom Registers: Type.
  Axiom word: Type.

  Record ThreadState := mkThreadState {
                            Regs: Registers;
                            Pc: word;
                          }.

  Instance ThreadStateSettable : Settable ThreadState := settable! mkThreadState <Regs; Pc>.

  Definition test(s: ThreadState)(newRegs: Registers): ThreadState := s <| Regs := newRegs |>.

  (* should be printed with set notation, not update notation *)
  Print test.
End GH13.
