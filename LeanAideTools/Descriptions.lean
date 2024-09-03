import LeanAideTools.Aides
import LeanAideTools.ChatClient
import Lean
open Lean Meta Elab PrettyPrinter Parser

abbrev ContextTerm := TSyntax [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder]

def excludeSuffixes := #[`dcasesOn, `recOn, `casesOn, `rawCast, `freeVar, `brec, `brecOn, `rec, `recOn, `cases, `casesOn, `dcases, `below, `ndrec]

partial def idents : Syntax → List String
| Syntax.ident _ s .. => [s.toString]
| Syntax.node _ _ ss => ss.toList.bind idents
| _ => []

open Lean.Parser.Term in
partial def arrowHeads (type: Syntax.Term)
    (accum: Array ContextTerm := #[]) :
        CoreM <| (Array ContextTerm) × Syntax.Term := do
    match type with
    | `(depArrow|$bb → $body) => do
        let accum := accum.push bb
        arrowHeads body accum
    | _ => return (accum, type)

def mkStatementStx (name?: Option Name)(type: Syntax.Term)
    (value?: Option Syntax.Term)(isProp: Bool) :
        CoreM (TSyntax `command) := do
    let (ctxs, tailType) ← arrowHeads type
    let value := value?.getD (← `(by sorry))
    let hash := hash type.raw.reprint
    let inner_name :=
        Name.num (Name.mkSimple "aux") hash.toNat
    let name := mkIdent <| name?.getD inner_name
    if isProp
    then
        `(command| theorem $name $ctxs* : $tailType := $value)
    else
        `(command| def $name:ident $ctxs* : $tailType := $value)

def mkStatement (name?: Option Name)(type: Syntax.Term)
    (value?: Option Syntax.Term)(isProp: Bool) :
        CoreM String := do
    let stx ← mkStatementStx name? type value? isProp
    let fmt ← ppCategory `command stx
    return fmt.pretty

def mkTheoremWithDoc (name: Name)(thm: String)
    (doc: String) :
        CoreM String := do
    let type? := runParserCategory (← getEnv) `term thm |>.toOption
    match type? with
    | none => return ""
    | some type => do
        let type : Syntax.Term := ⟨type⟩
        let name := mkIdent name
        let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (doc ++ " -/")]
        let stx ← `(command| $docs:docComment theorem $name : $type := by sorry)
        let fmt ← ppCategory `command stx
        return fmt.pretty

structure DefnTypes where
    name: Name
    type: String
    isProp : Bool
    docString? : Option String
    value : Option String
    statement : String
    deriving Repr, ToJson, FromJson

namespace DefnTypes
def withDoc (dfn: DefnTypes) : String :=
  match dfn.docString? with
  | some doc => s!"/-- {doc} -/\n{dfn.statement}"
  | none => dfn.statement

def thmFromName? (name : Name) : MetaM <| Option DefnTypes := do
  let env ← getEnv
  let doc? ← findDocString? env name
  let info? := env.find? name
  match info? with
    | some (.thmInfo dfn) =>
        let type := dfn.type
        let fmt ← Meta.ppExpr type
        let isProp := true
        let value := none
        let typeStx ← PrettyPrinter.delab type
        let valueStx? := none
        let statement ←
          mkStatement (some name) typeStx valueStx? isProp
        return some ⟨name, fmt.pretty, isProp, doc?, value, statement⟩
    | _ => return none

def thmFromNameCore? (name : Name) : CoreM <| Option DefnTypes :=
    (thmFromName? name).run'

def defFromName? (name : Name) : MetaM <| Option DefnTypes := do
  let env ← getEnv
  let doc? ← findDocString? env name
  let info? := env.find? name
  match info? with
    | some (.defnInfo dfn) =>
        let term := dfn.value
        let type := dfn.type
        let fmt ← Meta.ppExpr type
        let isProp := false
        let value :=
            some <| (← Meta.ppExpr term).pretty
        let typeStx ← PrettyPrinter.delab type
        let valueStx ←  PrettyPrinter.delab term
        let valueStx? := if isProp then none else some valueStx
        let statement ←
          mkStatement (some name) typeStx valueStx? isProp
        return some ⟨name, fmt.pretty, isProp, doc?, value, statement⟩
    | _ => return none

end DefnTypes

def theoremAndDefs (name: Name) : MetaM <|
  Option (String × (List String)) := do
  let env ← getEnv
  let info? := env.find? name
  match info? with
    | some (.thmInfo dfn) =>
        let type := dfn.type
        let typeStx ← PrettyPrinter.delab type
        let valueStx? := none
        let statement ←
          mkStatement (some name) typeStx valueStx? true
        let doc? ← findDocString? env name
        let statement := match doc? with
          | some doc => s!"/-- {doc} -/\n" ++ statement
          | none => statement
        let defNames := idents typeStx |>.eraseDups
        let defs ←  defNames.filterMapM <| fun n =>
          DefnTypes.defFromName? n.toName
        let defViews := defs.map <| fun df => df.withDoc
        let defViews := defViews.filter fun df => df.length < 600
        return some (statement, defViews)
    | _ => return none


def theoremStatement (name: Name) : MetaM <|
  Option (String) := do
  let env ← getEnv
  let info? := env.find? name
  match info? with
    | some (.thmInfo dfn) =>
        let type := dfn.type
        let typeStx ← PrettyPrinter.delab type
        let valueStx? := none
        let statement ←
          mkStatement (some name) typeStx valueStx? true
        let doc? ← findDocString? env name
        let statement := match doc? with
          | some doc => s!"/-- {doc} -/\n" ++ statement
          | none => statement
        return some statement
    | _ => return none

def filteredNames (names: Array Name) : Array Name :=
  let common := [``Eq.mp, ``Eq.mpr, ``congrArg, ``id, ``Eq.refl, ``trans, ``of_eq_true, ``trans, ``rfl, `symm, ``eq_self, `Eq, ``congr, ``propext, ``funext, ``Exists.intro, `left, `right, ``Iff.rfl, ``iff_self, `CategoryTheory.Functor.toPrefunctor, ``forall_congr, ``Eq.rec, ``Eq.ndrec, `Iff, ``And.left, ``And.right, ``And.intro, ``And.elim, ``And.rec, ``implies_congr, `obj, `map, ``And, `app, `hom, ``Not, ``Exists, ``eq_true, `self, ``HEq, ``HEq.refl, `congr_arg, `congr_fun, ``Subtype.property, ``Iff.trans, ``False, ``eq_false, ``true, ``false, ``not_false_eq_true, ``Trans.trans, ``True, ``inferInstance, `Set.ext,
  `elim, `inst]
  names.filter fun n =>
    !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n)) &&
    !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf n)) &&
    !common.contains n


def theoremAndLemmas (name: Name)
  (lemmaFilter : Array Name → Array Name := id) : MetaM <|
  Option (String × (Array String)) := do
  let env ← getEnv
  let info? := env.find? name
  match info? with
    | some (.thmInfo dfn) =>
        let type := dfn.type
        let typeStx ← PrettyPrinter.delab type
        let valueStx? := none
        let statement ←
          mkStatement (some name) typeStx valueStx? true
        let doc? ← findDocString? env name
        let statement := match doc? with
          | some doc => s!"/-- {doc} -/\n" ++ statement
          | none => statement
        let consts := dfn.value.getUsedConstants
        let consts := consts.filter fun name =>
          !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf name))
        let consts := consts.filter fun name =>
          ![``Eq.mp, ``Eq.mpr, ``congrArg, ``id].contains name
        let consts := lemmaFilter consts
        let lemmas ← consts.filterMapM theoremStatement
        return some (statement, lemmas)
    | _ => return none

def theoremPrompt (name: Name) : MetaM <| Option (String × String) := do
  (← theoremAndDefs name).mapM fun (statement, dfns) =>
    if dfns.isEmpty then
      return (← fromTemplate "describe_theorem" [("theorem", statement)], statement)
    else
      let defsBlob := dfns.foldr (fun acc df => acc ++ "\n\n" ++ df) ""
      return (← fromTemplate "describe_theorem_with_defs" [("theorem", statement), ("definitions", defsBlob.trim)],
      statement)

def getDescriptionM (name: Name)(chatClient := ChatClient.openAI)(params: ChatParams := {}) : MetaM <| Option (String × String) := do
  let prompt? ← theoremPrompt name
  prompt?.mapM fun (prompt, statement) => do
    let messages ← mkMessages prompt #[] (← sysPrompt)
    let fullJson ←  chatClient.query messages params
    let outJson :=
        (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
    let contents ← getMessageContents outJson
    return (contents[0]!, statement)

-- #eval getDescriptionM ``Nat.le_refl
