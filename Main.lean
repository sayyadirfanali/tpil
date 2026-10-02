def main : IO Unit :=
  IO.println s!"hello, world"

def m : Nat := 1

#check Nat.succ

#check Nat -> Nat

#check Type

#check Type 1

variable (P Q R : Prop)

theorem modus_ponens (p : P) (h : P -> Q) : Q := by
  exact h p

#print modus_ponens

#check @Eq.trans
