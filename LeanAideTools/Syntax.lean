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
      let js ← translateTheorem s
      let name ← match name? with
      | some name => pure name
      | none =>
          pure Name.anonymous
      let name := mkIdent name
      match js.getObjValAs? String "theorem" with
      | Except.ok thm =>
        let stx'' := runParserCategory (← getEnv) `term thm |>.toOption.get!
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
