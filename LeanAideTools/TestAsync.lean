import LeanAideTools.AsyncMode


#eval autoTactics


example : 1 = 1 := byy

opaque sillyN : Nat

axiom silly : sillyN = 2

/--
warning: declaration uses 'sorry'
-/
example : sillyN ≤ 3 := byy
  sorry

/--
info: Try this: by
  rw [silly]
  simp_all only
---
warning: declaration uses 'sorry'
-/
example : sillyN ≤ 6 := byy
  rw [silly]

example : sillyN ≤ 7 := by
    rw [silly]
    simp only [Nat.reduceLE]

#autos [aesop, rw [Nat.succ]]
