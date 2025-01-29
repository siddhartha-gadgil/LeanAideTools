import Lean
open Lean

namespace LeanAideTools

register_option leanaide.url : String := {
  defValue := "http://localhost:7654"
  descr := "URL of the LeanAide server"
  group := "leanaide"
}

def leanaideUrl : CoreM String := do
  return leanaide.url.get (← getOptions)

def callLeanAide (data: Json) (url: String := "http://localhost:7654") : IO <| Json := do
  let out ←
    IO.Process.output
      {cmd:= "curl", args:=#["-X", "POST", "-H", "\"Content-Type: application/json\"", "-d", data.compress, url]}
  if out.exitCode != 0 then IO.throwServerError out.stderr
  match Json.parse out.stdout with
  | Except.error e =>
    IO.throwServerError s!"Error parsing server output as Json:{e}; output: {out.stdout}"
  | Except.ok js => return js

def translateTheorem (s: String) (url: String := "http://localhost:7654") : IO Json := do
  let js := Json.mkObj [("task", "translate_thm"), ("text", s)]
  callLeanAide js url

def translateDef (s: String) (url: String := "http://localhost:7654") : IO Json := do
  let js := Json.mkObj [("task", "translate_def"), ("text", s)]
  callLeanAide js url

def theoremDoc (cmd name: String) (url: String := "http://localhost:7654") : IO Json := do
  let js := Json.mkObj [("task", "theorem_doc"), ("name", name), ("command", cmd)]
  callLeanAide js url

def defDoc (cmd name: String) (url: String := "http://localhost:7654") : IO Json := do
  let js := Json.mkObj [("task", "def_doc"), ("name", name), ("command", cmd)]
  callLeanAide js url

def theoremName (text: String) (url: String := "http://localhost:7654") : IO Json := do
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

-- #eval defDoc "def isCube (n: Nat) : Prop := ∃ m, m * m * m = n" "isCube"

end LeanAideTools
