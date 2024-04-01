import Lean
import Lean.Elab.Tactic
import Lean.Meta.Tactic.TryThis
import Aesop

open Lean Meta Elab Term Tactic Core Parser Tactic
open Std.Tactic

/-!
# Asynchronous tactic execution

We provide methods for executing tactics asynchronously. These are modelled on the `checkpoint` tactic.

* We run tactics and store resulting states in a cache.
* We use a more robust key than that for checkpoints.

## Indexing

We index by

* the current goal
* the current local context converted into lists

## Running tactics

We have a function of type `TacticM Unit` which

* executes the tactic
* stores the resulting states in the cache

## Fetching results

* We fetch final states based on the current goal and local context.
* We then restore these states.
-/

initialize autoTacticStringsIO : IO.Ref (List String) ←
  IO.mkRef ["rfl", "simp?", "exact?", "aesop?"]

syntax (name:= leanaide_auto) "#auto" tactic : command

open Command
@[command_elab leanaide_auto] def autoCmd : CommandElab := fun stx =>
  match stx with
  | `(command|#auto $tac) => do
    let tac := tac.raw.reprint.get!
    autoTacticStringsIO.modify fun l => l  ++ [tac]
    return ()
  | _ => throwUnsupportedSyntax

def autoTactics : CoreM <| List (TSyntax `tactic) := do
  let autoTacticStrings ← autoTacticStringsIO.get
  let ts ← autoTacticStrings.filterMapM (fun s => do
    let tac? := runParserCategory (← getEnv) `tactic s
    pure tac?.toOption)
  return ts.map (fun t => ⟨t⟩)

def getTactics (tacSeq : TSyntax ``tacticSeq) : Array (TSyntax `tactic) :=
  match tacSeq with
  | `(tacticSeq| { $[ $tacs ]* }) => tacs
  | `(tacticSeq| $[ $tacs ]*) => tacs
  | _ => #[]

def concatTactics (s : TSyntax ``tacticSeq) (h: TSyntax `tactic):
  CoreM (TSyntax ``tacticSeq) := do
  match s with
  | `(tacticSeq| { $[$t]* }) =>
      let ts' := t.push h
      `(tacticSeq| { $[$ts']* })
  | `(tacticSeq| $[$t]*) =>
      let ts' := t.push h
      `(tacticSeq| $[$ts']*)
  | _ => pure s

def tacAsSeq (tac : TSyntax `tactic) : CoreM (TSyntax ``tacticSeq) := do
  let ts := #[tac]
  `(tacticSeq| $[ $ts ]*)

def concatTactics' (s? : Option (TSyntax ``tacticSeq))
  (h: TSyntax `tactic): CoreM (TSyntax ``tacticSeq) := do
  match s? with
  | some s => concatTactics s h
  | none => tacAsSeq h

def appendTactics' (ts : Array (TSyntax `tactic))
    (s : TSyntax ``tacticSeq) :
  MetaM (TSyntax ``tacticSeq) := do
  match s with
  | `(tacticSeq| { $[$t]* }) =>
      let ts' := ts ++ t
      `(tacticSeq| { $[$ts']* })
  | `(tacticSeq| $[$t]*) =>
      let ts' := ts ++ t
      `(tacticSeq| $[$ts']*)
  | _ => `(tacticSeq| $[$ts]*)

def EIO.runToIO' (eio: EIO Exception α) : IO α  := do
  match ←  eio.toIO' with
  | Except.ok x =>
      pure x
  | Except.error e =>
      let msg ← e.toMessageData.toString
      IO.throwServerError msg

register_option aided_by.delay : Nat :=
  { defValue := 50
    group := "aided_by"
    descr := "Time to wait after launching a task." }

def isSorry (tacticCode: TSyntax `tactic) : TermElabM Bool := do
  let goal ← mkFreshExprMVar (mkConst ``False)
  try
    let (goals, _) ← Elab.runTactic  goal.mvarId! tacticCode
    return goals.isEmpty
  catch _ =>
    return false

deriving instance BEq, Hashable, Repr for LocalDecl

structure GoalKey where
  goal : Expr
  lctx : List <| Option LocalDecl
deriving BEq, Hashable, Repr

structure ProofState where
  tacticRun : TSyntax `tactic
  core   : Core.State
  meta   : Meta.State
  term?  : Option Term.State
  script : TSyntax ``tacticSeq

def GoalKey.get : TacticM GoalKey := do
  let lctx ← getLCtx
  let goal ← getMainTarget
  pure { goal := goal, lctx := lctx.decls.toList }

section Caches

initialize tacticCache : IO.Ref (HashMap GoalKey (Array ProofState))
        ← IO.mkRef ∅

initialize spawnedKeys :
  IO.Ref (HashSet <| GoalKey)
        ← IO.mkRef  ∅

def isSpawned (key : GoalKey) : IO Bool := do
  let m ← spawnedKeys.get
  return m.contains key

def markSpawned (key : GoalKey)  : IO Unit := do
  spawnedKeys.modify fun m => m.insert key

def putTactic (key : GoalKey) (s : ProofState) : MetaM Unit := do
  tacticCache.modify fun m =>
    m.insert key <| (m.findD key #[]).push s

def getStates (key : GoalKey) : TacticM <| Array ProofState := do
  let m ← tacticCache.get
  return m.find? key |>.getD #[]

def clearCache : IO Unit := do
  tacticCache.modify fun _ => ∅
  spawnedKeys.modify fun _ => ∅

end Caches



def runAndCacheM
  (tac : TSyntax `tactic)(goal: MVarId) (target : Expr)  : MetaM Unit :=
  goal.withContext do
    let lctx ← getLCtx
    let key : GoalKey := { goal := target, lctx := lctx.decls.toList }
    if ←isSpawned key then
      return ()
    markSpawned key
    let core₀ ← getThe Core.State
    let meta₀ ← getThe Meta.State
    try
      let (goals, ts) ← runTactic  goal (← tacAsSeq tac)
      unless goals.isEmpty do
        throwError m!"Tactic not finishing, remaining goals:\n{goals}"
      let s : ProofState := {
        tacticRun := tac
        core   := (← getThe Core.State)
        meta   := (← getThe Meta.State)
        term?   := some ts
        script := ← tacAsSeq tac
        }
      putTactic key s
    catch _ =>
      pure ()
    set core₀
    set meta₀

def runAndCacheIO
  (tac: TSyntax `tactic) (goal: MVarId) (target : Expr)
  (mctx : Meta.Context) (ms : Meta.State)
  (cctx : Core.Context) (cs: Core.State) : IO Unit :=
  let eio :=
  (runAndCacheM  tac goal target).run' mctx ms |>.run' cctx cs
  let res := eio.runToIO'
  res

def fetchProofs  : TacticM <| Array ProofState :=
  focus do
  let key ← GoalKey.get
  getStates key

syntax (name := autoTacs) "with_aide" ("from_by")? (tacticSeq)? : tactic

example : 1 = 1 := rfl

macro "byy" tacs:tacticSeq : term =>
  `(by with_aide from_by $tacs)

macro "byy"  : term =>
  `(by with_aide from_by)


@[tactic autoTacs] def autoStartImpl : Tactic := fun stx =>
withMainContext do
match stx with
| `(tactic| with_aide from_by  $tacticCode) =>
    autoStartImplAux stx tacticCode true
| `(tactic| with_aide $tacticCode) =>
    autoStartImplAux stx tacticCode false
| `(tactic| with_aide from_by) => do
    autoStartImplAux' stx true
| `(tactic| with_aide) => do
    autoStartImplAux' stx false
| _ => throwUnsupportedSyntax
where
  initialSearch (stx: Syntax)
    (fromBy: Bool) : TacticM Unit :=
    withMainContext do
    if (← getUnsolvedGoals).isEmpty then
        return ()
    for autoCode in (← autoTactics) do
      let ioSeek : IO Unit := runAndCacheIO
        autoCode  (← getMainGoal) (← getMainTarget)
                (← readThe Meta.Context) (← getThe Meta.State )
                (← readThe Core.Context) (← getThe Core.State)
      let _ ← ioSeek.asTask
    try
      let delay  := aided_by.delay.get (← getOptions)
      dbgSleep delay.toUInt32 fun _ => do
        let pfs ← fetchProofs
        let scripts := pfs.map (fun pf => pf.script)
        if fromBy then
          let byScripts ←  scripts.mapM (fun s => `(by $s))
          let suggestions :=  byScripts.map (
            fun s => {suggestion := s})
          TryThis.addSuggestions stx suggestions
        else
          let suggestions :=  scripts.map (
            fun s => {suggestion := s})
          TryThis.addSuggestions stx suggestions
        if !pfs.isEmpty then
          evalTactic (← `(tactic|sorry))
          return ()

    catch _ =>
      pure ()
  autoStartImplAux (stx: Syntax)
  (tacticCode : TSyntax ``tacticSeq)(fromBy: Bool) : TacticM Unit :=
  withMainContext do
    initialSearch stx  fromBy
    let allTacs := getTactics tacticCode
    let mut cumTacs :  Array (TSyntax `tactic) := #[]
    for tacticCode in allTacs do
      evalTactic tacticCode
      if ← isSorry tacticCode then
        return ()
      cumTacs := cumTacs.push tacticCode
      if (← getUnsolvedGoals).isEmpty then
        unless tacticCode.raw.reprint.get!.trim.endsWith "sorry" do
          if fromBy then
            TryThis.addSuggestion stx (← `(by $[$cumTacs]*))
          else
            TryThis.addSuggestion stx (← `(tacticSeq|$[$cumTacs]*))
        return ()
      for autoCode in (← autoTactics) do
        let ioSeek : IO Unit := runAndCacheIO
          autoCode  (← getMainGoal) (← getMainTarget)
                  (← readThe Meta.Context) (← getThe Meta.State )
                  (← readThe Core.Context) (← getThe Core.State)
        let _ ← ioSeek.asTask
      try
        let delay  := aided_by.delay.get (← getOptions)
        dbgSleep delay.toUInt32 fun _ => do
          let pfs ← fetchProofs
          let scripts ←  pfs.mapM
            (fun pf => appendTactics' cumTacs pf.script)
          if fromBy then
            let byScripts ←  scripts.mapM (fun s => `(by $s))
            let suggestions :=  byScripts.map (
              fun s => {suggestion := s})
            TryThis.addSuggestions stx suggestions
          else
            let suggestions :=  scripts.map (
              fun s => {suggestion := s})
            TryThis.addSuggestions stx suggestions
          if !pfs.isEmpty then
            evalTactic (← `(tactic|sorry))
            return ()
      catch _ =>
        pure ()
  autoStartImplAux' (stx: Syntax)(fromBy: Bool) : TacticM Unit :=
    withMainContext do
    initialSearch stx fromBy
    if (← getUnsolvedGoals).isEmpty then
        return ()
