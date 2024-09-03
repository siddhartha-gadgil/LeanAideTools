import LeanAideTools.AsyncMode


#eval autoTactics

-- set_option trace.leanaide.auto_tactic.info true
-- set_option leanaide.auto_tactic.debug true

example : 1 = 1 := byy

opaque sillyN : Nat

axiom silly : sillyN = 2

-- #autos [rw [silly], simp [silly]]

set_option leanaide.auto_tactic.delay 0 in
example : sillyN ≤ 3 := byy
  rw [silly]
  skip
  sleep 100


/--
info: Try this: by
  rw [silly]
  simp_all only
---
warning: declaration uses 'sorry'
-/
example : sillyN ≤ 6 := byy
  rw [silly]
  sleep 200

example : sillyN ≤ 7 := byy
    rw [silly]
    sleep 200

#autos [aesop, rw [Nat.succ]]

#auto (sleep 300; simp [silly])

example : sillyN ≤ 8 := byy
  skip
  sorry
