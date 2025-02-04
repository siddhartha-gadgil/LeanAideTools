import Lean
import LeanAideTools.Aides
open Lean

namespace LeanAideTools

register_option leanaide.url : String := {
  defValue := "http://localhost:7654"
  descr := "URL of the LeanAide server"
  group := "leanaide"
}

register_option lean_aide.examples.docstrings : Nat :=
  { defValue := 10
    group := "lean_aide"
    descr := "Number of document strings in a prompt (default 10)" }

register_option lean_aide.examples.concise_descriptions : Nat :=
  { defValue := 0
    group := "lean_aide"
    descr := "Number of concise descriptions in a prompt (default 0)" }

register_option lean_aide.examples.descriptions : Nat :=
  { defValue := 0
    group := "lean_aide"
    descr := "Number of descriptions in a prompt (default 0)" }

register_option lean_aide.custom : Bool :=
  { defValue := false
    group := "lean_aide"
    descr := "Whether to use custom model or parameters." }

register_option lean_aide.examples.custom : Bool :=
  { defValue := false
    group := "lean_aide"
    descr := "Whether to customize examples." }

register_option lean_aide.query.choices : Nat :=
  { defValue := 10
    group := "leanaide"
    descr := "Number of outputs to request in a query (default 5)." }

register_option lean_aide.query.model : String :=
  { defValue := "gpt-4o"
    group := "leanaide"
    descr := "Model to use (gpt-4o)." }

register_option lean_aide.query.azure : Bool :=
  { defValue := false
    group := "leanaide"
    descr := "Whether to use Azure OpenAI." }

register_option lean_aide.query.gemini : Bool :=
  { defValue := false
    group := "leanaide"
    descr := "Whether using the gemini API." }

register_option lean_aide.query.url? : String :=
  { defValue := ""
    group := "leanaide"
    descr := "Local or generic url to query. Empty string for none" }

register_option lean_aide.query.authkey? : String :=
  { defValue := ""
    group := "leanaide"
    descr := "Authentication key for OpenAI or generic model" }

register_option lean_aide.query.examples_url? : String :=
  { defValue := ""
    group := "leanaide"
    descr := "Local or generic url to query for embeddings. Empty string for none" }

register_option lean_aide.query.greedy : Bool :=
  { defValue := false
    group := "leanaide"
    descr := "Whether to choose the first elaboration." }

register_option lean_aide.query.reasoning : Bool :=
  { defValue := false
    group := "leanaide"
    descr := "Whether using a reasoning model." }

register_option lean_aide.query.has_sysprompt : Bool :=
  { defValue := true
    group := "leanaide"
    descr := "Whether the server has a system prompt." }

register_option lean_aide.query.temperature10 : Nat :=
  { defValue := 8
    group := "leanaide"
    descr := "temperature * 10." }

register_option lean_aide.query.max_tokens : Nat :=
  { defValue := 1600
    group := "leanaide"
    descr := "Maximum tokens to generate." }

def config : CoreM Json := do
  let opts ← getOptions
  if lean_aide.custom.get opts then
    let url := lean_aide.query.url?.get opts
    let url? := if url == "" then none else some url
    let authkey? := if lean_aide.query.authkey?.get opts == "" then none else some (lean_aide.query.authkey?.get opts)
    let temp  :=
    match JsonNumber.fromFloat? <|
      (Float.ofNat <| lean_aide.query.temperature10.get opts)/10 with
      | .inr temp => temp
      | _ => 1.0
    let server :=
      Json.mkObj [
        ("model", Json.str <| lean_aide.query.model.get opts),
        ("gemini", Json.bool <| lean_aide.query.gemini.get opts),
        ("azure", Json.bool <| lean_aide.query.azure.get opts),
        ("authkey", Json.str <| lean_aide.query.authkey?.get opts),
        ("examples_url", Json.str <| lean_aide.query.examples_url?.get opts),
        ("greedy", Json.bool <| lean_aide.query.greedy.get opts),
        ("reasoning", Json.bool <| lean_aide.query.reasoning.get opts),
        ("has_sysprompt", Json.bool <| lean_aide.query.has_sysprompt.get opts),
        ("temperature", Json.num  <| temp),
        ("max_tokens", Json.num <| JsonNumber.fromNat <| lean_aide.query.max_tokens.get opts),
        ]
    let server := match url? with
    | some url => server.mergeObj <| Json.mkObj [("url", Json.str url)]
    | none => server
    let response := Json.mkObj [("server", server)]
    let response := match authkey? with
    | some authkey => response.mergeObj <| Json.mkObj [("auth_key", Json.str authkey)]
    | none => response
    let response := if lean_aide.examples.custom.get opts then
      let examples := Json.mkObj [
        ("docstrings", Json.num <| JsonNumber.fromNat <| lean_aide.examples.docstrings.get opts),
        ("concise_descriptions", Json.num <| JsonNumber.fromNat <| lean_aide.examples.concise_descriptions.get opts),
        ("descriptions", Json.num <| JsonNumber.fromNat <| lean_aide.examples.descriptions.get opts),
        ]
      let examples_url := lean_aide.query.examples_url?.get opts
      let examples_url? := if examples_url == "" then none else some examples_url
      let examples := match examples_url? with
      | some url => examples.mergeObj <| Json.mkObj [("examples_url", Json.str url)]
      | none => examples
      response.mergeObj <| Json.mkObj [("examples", examples)]
    else
      response
    return response
  else
    let authkey := lean_aide.query.authkey?.get opts
    let authkey := if authkey == "" then none else some authkey
    match authkey with
    | some authkey => return Json.mkObj [("auth_key", Json.str authkey)]
    | none =>
        return Json.mkObj []


def leanaideUrl : CoreM String := do
  return leanaide.url.get (← getOptions)

def callLeanAide (data: Json) (url: String ) : CoreM <| Json := do
  let data := data.mergeObj (← config)
  let out ←
    IO.Process.output
      {cmd:= "curl", args:=#["-X", "POST", "-H", "\"Content-Type: application/json\"", "-d", data.compress, url]}
  if out.exitCode != 0 then IO.throwServerError out.stderr
  match Json.parse out.stdout with
  | Except.error e =>
    IO.throwServerError s!"Error parsing server output as Json:{e}; output: {out.stdout}"
  | Except.ok js => return js

def translateTheorem (s: String) (url: String ) : CoreM Json := do
  let js := Json.mkObj [("task", "translate_thm"), ("text", s)]
  callLeanAide js url

def translateDef (s: String) (url: String ) : CoreM Json := do
  let js := Json.mkObj [("task", "translate_def"), ("text", s)]
  callLeanAide js url

def theoremDoc (cmd name: String) (url: String ) : CoreM Json := do
  let js := Json.mkObj [("task", "theorem_doc"), ("name", name), ("command", cmd)]
  callLeanAide js url

def defDoc (cmd name: String) (url: String ) : CoreM Json := do
  let js := Json.mkObj [("task", "def_doc"), ("name", name), ("command", cmd)]
  callLeanAide js url

def theoremName (text: String) (url: String ) : CoreM Json := do
  let js := Json.mkObj [("task", "theorem_name"), ("text", text)]
  callLeanAide js url

def checkResult (js: Json) : CoreM Unit := do
  match js.getObjValAs? String "result" with
  | Except.ok "error" =>
    let error := js.getObjValAs? String "error" |>.toOption |>.getD "internal error"
    throwError s!"Error in LeanAide server: {error}.S"
  | Except.ok "fallback" =>
      logInfo "No valid response found, suggesting best option."
  | Except.ok "success" => pure ()
  | Except.error e => throwError s!"Error in LeanAide server: {e}."
  | Except.ok _ => throwError "Unexpected result from LeanAide server."

-- #eval translateTheorem "There are infinitely many prime numbers."

-- #eval defDoc "def isCube (n: Nat) : Prop := ∃ m, m * m * m = n" "isCube" (url :="http://localhost:7654")

def getCodeJson (thm: String) (url: String) (elaborate: Bool := true) : CoreM Json := do
  let tasks := ["prove", "structured_json_proof", "lean_from_json_structured"]
  let tasks := if elaborate then tasks ++ ["elaborate"] else tasks
  let js := Json.mkObj [("tasks", toJson tasks), ("theorem", thm)]
  callLeanAide js url

def getLeanCode (thm: String) (url: String) (elaborate: Bool := true) : CoreM Syntax.Command := do
  let js ← getCodeJson thm url elaborate
  checkResult js
  match js.getObjValAs? String "lean_code" with
  | Except.ok lean =>
    let lean := lean.replace "\\n" "\n"
    let parsed? := Parser.runParserCategory (← getEnv) `command lean
    match parsed? with
    | Except.ok stx => return ⟨stx⟩
    | _ => throwError s!"Could not parse {lean}.\nMaybe some imports are missing"
  | Except.error e => throwError s!"Error in LeanAide server: {e}."

def getPropCodeJson (prop : String) (url: String) (elaborate: Bool := true) : MetaM Json := do
  let tasks := ["prove_prop", "structured_json_proof", "lean_from_json_structured"]
  let tasks := if elaborate then tasks ++ ["elaborate"] else tasks
  let js := Json.mkObj [("tasks", toJson tasks), ("prop", prop)]
  callLeanAide js url

def getPropLeanCode (prop: String) (url: String) (elaborate: Bool := true) : MetaM Syntax.Command := do
  let js ← getPropCodeJson prop url elaborate
  checkResult js
  match js.getObjValAs? String "lean_code" with
  | Except.ok lean =>
    let lean := lean.replace "\\n" "\n"
    let parsed? := Parser.runParserCategory (← getEnv) `command lean
    match parsed? with
    | Except.ok stx => return ⟨stx⟩
    | _ => throwError s!"Could not parse {lean}.\nMaybe some imports are missing"
  | Except.error e => throwError s!"Error in LeanAide server: {e}."

def getPropLeanCodeExpr (type: Expr) (url: String) (elaborate: Bool := true) : MetaM Syntax.Command := do
  let prop ← ppExprDetailed type
  getPropLeanCode prop url elaborate

def getPropLeanCodeStx (type: Syntax.Term) (url: String) (elaborate: Bool := true) : MetaM Syntax.Command := do
  let prop ← PrettyPrinter.ppTerm type
  let prop := prop.pretty
  getPropLeanCode prop url elaborate

end LeanAideTools
