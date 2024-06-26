import Lean
open Lean Meta Elab Command Syntax


/-!
## Spotting multiple instances of the same typeclass

The goal of this file is to write code that checks if two instances of the same typeclass are used in a term. This leads to confusing errors.
-/


/--
Check if two expressions are instances of the same typeclass.
-/
def clashInstances (a b : Expr) : MetaM Bool := do
  let aType ← inferType a
  let bType ← inferType b
  match ((← isClass? aType), (← isClass? bType)) with
  | (some x, some y) =>
    if (x = y) && (← isDefEq aType  bType) then
        let instancesEqual ← isDefEq a b
        return !instancesEqual
      else
        return false
  | _ =>
    return false

/--
Extract all subexpressions of an expression.
-/
def subExprs : Expr →  List Expr
| .app f a => subExprs f ++ subExprs a
| .lam _ d b _ => subExprs d ++ subExprs b
| .forallE _ d b _ => subExprs d ++ subExprs b
| .letE _ t v b _ => subExprs t ++ subExprs v ++ subExprs b
| .lit e => [.lit e]
| .const n l => [.const n l]
| _ => []

structure InstanceClash where
  e1 : Expr
  e2 : Expr
  type : Expr

def instanceClash? (e : Expr) : MetaM (Option InstanceClash) := do
  let subExprs := subExprs e
  for e in subExprs do
    for e' in subExprs do
      let res ← clashInstances e e'
      if res then
        let type ← inferType e
        return some {e1 := e, e2 := e', type := type}
  return none

open Lean.Elab.Tactic
elab "check_clashes" : tactic => do
  withMainContext do
    let goal ← getMainTarget
    let clash? ← instanceClash? goal
    match clash? with
    | none => return ()
    | some {e1 := e, e2 := e', type := type} => do
        Lean.throwError m!"instances clash: `{← ppExpr e}` and `{← ppExpr e'}` are instances of the same typeclass `{← ppExpr type}` with different instances."
        throwAbortTactic

elab "warn_clashes" : tactic => do
  withMainContext do
    let goal ← getMainTarget
    let clash? ← instanceClash? goal
    match clash? with
    | none => return ()
    | some {e1 := e, e2 := e', type := type} => do
        logWarning m!"instances clash: `{← ppExpr e}` and `{← ppExpr e'}` are instances of the same typeclass `{← ppExpr type}` with different instances."
        return ()
