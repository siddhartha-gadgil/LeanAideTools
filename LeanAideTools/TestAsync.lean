import LeanAideTools.AsyncMode

example : 1 = 1 := by exact?

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
example : sillyN ≤ 4 := by
with_aide
  rw [silly]
  sorry
