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
example : sillyN ≤ 4 := byy
  rw [silly]
