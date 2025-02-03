import LeanAideTools.Client
import Lean

open Lean Meta Elab Parser Tactic Command

namespace LeanAideTools

syntax (name := thmCommand) "#theorem" (ident)? (":")? str : command
@[command_elab thmCommand] def thmCommandImpl : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #theorem $s:str) =>
    let s := s.getString
    go s stx none
  | `(command| #theorem $name:ident $s:str) =>
    let s := s.getString
    let name := name.getId
    go s stx (some name)
  | `(command| #theorem : $s:str) =>
    let s := s.getString
    go s stx none
  | `(command| #theorem $name:ident : $s:str) =>
    let s := s.getString
    let name := name.getId
    go s stx (some name)
  | _ => throwUnsupportedSyntax
  where go (s: String) (stx: Syntax) (name? : Option Name) : TermElabM Unit := do
    if s.endsWith "." then
      let js ← translateTheorem s (← leanaideUrl)
      let name ← match name? with
      | some name => pure name
      | none =>
          let js ← theoremName s (← leanaideUrl)
          let some name := js.getObjValAs? Name "name" |>.toOption | throwError "Could not obtain name"
          pure name
      let name := mkIdent name
      match js.getObjValAs? String "theorem" with
      | Except.ok thm =>
        checkResult js
        let some stx'' := runParserCategory (← getEnv) `term thm |>.toOption | throwError s!"Could not parse {thm}.\nMaybe some imports are missing"
        let stx' : Syntax.Term := ⟨stx''⟩
        let cmd ← `(command| theorem $name : $stx' := by sorry)
        TryThis.addSuggestion stx cmd
        let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ " -/")]
        let cmd ←
          `(command| $docs:docComment theorem $name:ident : $stx' := by sorry)
        TryThis.addSuggestion stx cmd (header := "Try This (with docstring): ")
        return
      | .error e =>
        logWarning "No valid lean code found, suggesting best option"
        let cmd := s!"theorem {name} : {e} := by sorry"
        TryThis.addSuggestion stx cmd
        let cmd := s!"/-- {s} -/\ntheorem {name} : {e} := by sorry"
        TryThis.addSuggestion stx cmd (header := "Try This (with docstring): ")

    else
      logWarning "To translate a theorem, end the string with a `.`."

syntax (name := defCommand) "#def"  str : command
@[command_elab defCommand] def defCommandImpl : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #def $s:str) =>
    let s := s.getString
    go s stx
  | _ => throwUnsupportedSyntax
  where go (s: String) (stx: Syntax) : TermElabM Unit := do
    if s.endsWith "." then
      let js ← translateDef s (← leanaideUrl)
      match js.getObjValAs? String "definition" with
      | Except.ok dfn =>
        checkResult js
        let some stx'' := runParserCategory (← getEnv) `command dfn |>.toOption | throwError s!"Could not parse {dfn}.\nMaybe some imports are missing"
        let cmd : Syntax.Command := ⟨stx''⟩
        TryThis.addSuggestion stx cmd
        let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ " -/")]
        match cmd with
        | `(command| def $name $args* : $stx' := $val) =>
          let cmd ←
            `(command| $docs:docComment def $name $args* : $stx' := $val)
          TryThis.addSuggestion stx cmd (header := "Try This (with docstring): ")
        | `(command| noncomputable def $name:ident $args* : $stx' := $val) =>
          let cmd ←
            `(command| $docs:docComment noncomputable def $name:ident $args* : $stx' := $val)
          TryThis.addSuggestion stx cmd (header := "Try This (with docstring): ")
        | _ => pure ()
        return
      | .error e =>
        throwError s!"No definition in server response: {e}"
    else
      logWarning "To translate a theorem, end the string with a `.`."

syntax (name:= addDocs) "#doc" command : command

open Command in
@[command_elab addDocs] def elabAddDocsImpl : CommandElab := fun stx =>
  match stx with
  | `(#doc theorem $id:ident $ty:declSig $val:declVal) =>
    Command.liftTermElabM do
    let name := id.getId
    let stx' ← `(command| theorem $id:ident $ty $val)
    let fmt ← PrettyPrinter.ppCommand stx'
    let js ← theoremDoc fmt.pretty name.toString (← leanaideUrl)
    let some desc :=
      js.getObjValAs? String "doc" |>.toOption | throwError "No description found"
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (desc ++ " -/")]
    let stx' ← `(command| $docs:docComment theorem $id:ident $ty $val)
    TryThis.addSuggestion stx stx'
  | `(#doc def $id:ident $args* : $ty:term := $val:term) =>
    Command.liftTermElabM do
    let name := id.getId
    let stx' ← `(command| def $id:ident $args* : $ty:term := $val:term)
    let fmt ← PrettyPrinter.ppCommand stx'
    let js ← defDoc fmt.pretty name.toString (← leanaideUrl)
    let some desc :=
      js.getObjValAs? String "doc" |>.toOption | throwError "No description found"
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (desc ++ " -/")]
    let stx' ← `(command| $docs:docComment def $id:ident $args* : $ty:term := $val:term)
    TryThis.addSuggestion stx stx'
  | `(#doc noncomputable def $id:ident $args* : $ty:term := $val:term) =>
    Command.liftTermElabM do
    let name := id.getId
    let stx' ← `(command| noncomputable def $id:ident $args* : $ty:term := $val:term)
    let fmt ← PrettyPrinter.ppCommand stx'
    let js ← defDoc fmt.pretty name.toString (← leanaideUrl)
    let some desc :=
      js.getObjValAs? String "doc" |>.toOption | throwError "No description found"
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (desc ++ " -/")]
    let stx' ← `(command| $docs:docComment noncomputable def $id:ident $args* : $ty:term := $val:term)
    TryThis.addSuggestion stx stx'
  | _ => throwError "unexpected syntax"

syntax (name := proveCommand) "#prove"  str : command
@[command_elab proveCommand] def proveCommandImpl : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #prove $s:str) =>
    let s := s.getString
    go s stx
  | _ => throwUnsupportedSyntax
  where go (s: String) (stx: Syntax) : TermElabM Unit := do
    if s.endsWith "." then
      let code ← getLeanCode s (← leanaideUrl)
      TryThis.addSuggestion stx code
    else
      logWarning "To translate a theorem, end the string with a `.`."

syntax (name := provePropCommand) "#prove"  term ":=" : command
@[command_elab provePropCommand] def provePropCommandImpl : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #prove $t:term :=) =>
    go t stx
  | _ => throwUnsupportedSyntax
  where go (t: Syntax.Term) (stx: Syntax) : TermElabM Unit := do
    let code ← getPropLeanCodeStx t (← leanaideUrl)
    TryThis.addSuggestion stx code

#theorem "There are infinitely many natural numbers"

#def "A number is defined to be cube-free if it is not divisible by the cube of a prime number"
