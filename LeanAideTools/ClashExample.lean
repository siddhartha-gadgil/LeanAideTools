import LeanAideTools.InstanceClash
import LeanAideTools.AsyncMode
/-!
Example usage
-/

instance collapseInst : HAdd String String String where
  hAdd := String.append

def collapse (a b: String): String :=
  @HAdd.hAdd String String String collapseInst a b

instance collapseInst' : HAdd String String String where
  hAdd := fun a b => a ++ " " ++ b

def collapse' (a b: String): String :=
  @HAdd.hAdd String String String collapseInst' a b


/--
error: instances clash: `collapseInst'` and `collapseInst` are instances of the same typeclass `HAdd String String
  String` with different instances.
-/
#guard_msgs in
example (a b  : String) : collapse' a b = collapse a b := by
  unfold collapse collapse'
  check_clashes

/--
warning: instances clash: `collapseInst'` and `collapseInst` are instances of the same typeclass `HAdd String String
  String` with different instances.
---
error: unsolved goals
a b : String
⊢ a + b = a + b
-/
#guard_msgs in
example (a b  : String) : collapse' a b = collapse a b := by
  unfold collapse collapse'
  warn_clashes

example (a b  : String) : collapse' a b = collapse a b := by
  unfold collapse collapse'
  try check_clashes
  sorry

example (a b  : String) : collapse' a b = collapse a b := by
  unfold collapse collapse'
  warn_clashes
  sorry

/--
error: Error in fail tactic check_clashes: instances clash: `collapseInst'` and `collapseInst` are instances of the same typeclass `HAdd
  String String String` with different instances.
---
error: unsolved goals
a b : String
⊢ a + b = a + b
-/
#guard_msgs in
example (a b  : String) : collapse' a b = collapse a b := byy
  unfold collapse collapse'
