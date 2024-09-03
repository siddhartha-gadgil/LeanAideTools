import Lean
import LeanAideTools.Aides
import LeanAideTools.Template

open Lean Meta System

def openAIKey : IO (Option String) := IO.getEnv "OPENAI_API_KEY"

def azureKey : IO (Option String) := IO.getEnv "AZURE_OPENAI_KEY"

def azureEndpoint : IO (Option String) := IO.getEnv "AZURE_OPENAI_ENDPOINT"

def azureURL (deployment: String := "GPT4TestDeployment") : IO String := do
  let endpoint ← azureEndpoint
  match endpoint with
  | none => throw <| IO.userError "AZURE_OPENAI_ENDPOINT not set"
  | some endpoint =>
    return s!"{endpoint}/openai/deployments/{deployment}/chat/completions?api-version=2023-05-15"

def openAIURL : IO String := do
  pure "https://api.openai.com/v1/chat/completions"

def projectID : IO String := do
  let id ← IO.getEnv "PROJECT_ID"
  match id with
  | none => throw <| IO.userError "PROJECT_ID not set"
  | some id => return id


/--
Extracts the content of the message field from a JSON object,
following the OpenAI API format.
-/
def getMessageContents (json: Json) : CoreM (Array String) := do
  let outArr : Array String ←
    match json.getArr? with
    | Except.ok arr =>
        let parsedArr : Array String ←
          arr.filterMapM <| fun js =>
            match js.getObjVal? "message" with
            | Except.ok jsobj =>
                match jsobj.getObjValAs? String "content" with
                | Except.ok str =>
                  pure (some str)
                | Except.error _ =>
                  throwError m!"no  string content field in {jsobj}"
            | Except.error _ =>
                throwError m!"no message field in {js}"

        pure parsedArr
    | Except.error e => throwError m!"json parsing error: {e}"

structure ChatParams where
  n : Nat := 1
  temp : JsonNumber := 0.8
  stopTokens : Array String :=  #[]
  maxTokens : Nat := 1600

namespace ChatParams
def stopColEq (params: ChatParams) : Bool :=
  params.stopTokens.contains ":="

def splitOutputs (params: ChatParams)
  (outputs : Array String) : Array String :=
  if stopColEq params then
    outputs
  else
    let outs := outputs.toList.bind colEqSegments
    outs.toArray

def noStop (p: ChatParams) : ChatParams :=
  {p with stopTokens := #["\n\n"]}

def withoutStop (p: ChatParams)(stopless: Bool) : ChatParams :=
  if stopless then noStop p else p

end ChatParams


inductive ChatClient where
  | openAI (model: String := "gpt-4o")
  | azure (deployment: String := "GPT4TestDeployment")
      (model: String := "GPT-4")
  | google (model: String := "gemini-1.5-pro-001") (location: String := "asia-south1")
  | generic (model: String) (url: String) (hasSysPropmpt : Bool := false)

namespace ChatClient

def url : ChatClient → IO String
  | openAI _ =>
      return "https://api.openai.com/v1/chat/completions"
  | azure deployment _ =>
      azureURL deployment
  | google _ location => do
      let url ←  pure s!"https://{location}-aiplatform.googleapis.com/v1beta1/projects/{← projectID}/locations/{location}/endpoints/openapi/chat/completions"
      -- IO.eprintln s!"Google URL: {url}"
      return url
  | generic _ url _ =>
      return url++"/v1/chat/completions"

def model : ChatClient → String
  | openAI model => model
  | azure _ model => model
  | generic model _ _ => model
  | google model _ => "google/" ++ model

def hasSysPropmpt : ChatClient → Bool
  | openAI _ => true
  | azure _ _ => true
  | generic _ _ b => b
  | google _ _ => true

def authHeader? : ChatClient → IO (Option String)
  | openAI _ => do
    let key? ← openAIKey
    let key :=
    match key? with
      | some k => k
      | none => panic! "OPENAI_API_KEY not set"
    return some <|"Authorization: Bearer " ++ key
  | azure .. => do
    let key? ← azureKey
    let key :=
    match key? with
      | some k => k
      | none => panic! "AZURE_OPENAI_KEY not set"
    return some <| "api-key: " ++ key
  | generic .. =>
    return none
  | google _ _ => do
    let key ← IO.Process.run {cmd := "gcloud", args := #["auth", "print-access-token"]}
    return some <|"Authorization: Bearer " ++ key.trim

def query (server: ChatClient)(messages : Json)(params : ChatParams) : CoreM Json := do
  let stopJs := Json.mkObj <| if params.stopTokens.isEmpty then [] else
    [("stop", Json.arr <| params.stopTokens |>.map Json.str)]
  let dataJs := Json.mkObj [("model", server.model), ("messages", messages)
  , ("temperature", Json.num params.temp), ("n", params.n), ("max_tokens", params.maxTokens)]
  let dataJs := dataJs.mergeObj stopJs
  let data := dataJs.pretty
  trace[Translate.info] "Model query: {data}"
  let url ← server.url
  let authHeader? ← server.authHeader?
  -- IO.eprintln s!"Querying {url} at {← IO.monoMsNow }"
  -- let start ← IO.monoMsNow
  let baseArgs :=
    #[url, "-X", "POST", "-H", "Content-Type: application/json"]
  let args := match authHeader? with
    | some h => #["-H", h] ++ baseArgs
    | none => baseArgs
  let output ← IO.Process.output
      {cmd := "curl", args:= args ++ #["--data", data]}
  let queryJs := Json.mkObj [
    ("url", Json.str url),
    ("arguments", Json.arr <| baseArgs.map (Json.str)),
    ("data", data)]
  match output.exitCode, Lean.Json.parse output.stdout with
  | 0, Except.ok j =>
    appendLog "chat_queries"
      (Json.mkObj [("query", queryJs), ("success", true), ("response", j)])
    return j
  | 0, Except.error e =>
    appendLog "chat_queries"
      (Json.mkObj [("query", queryJs), ("success", false), ("error", e), ("response", output.stdout)])
    panic! s!"Error parsing JSON: {e}; source: {output.stdout}"
  | j, _ =>
    appendLog "chat_queries"
      (Json.mkObj [("query", queryJs), ("success", false), ("error",output.stderr), ("exit code:", j.toNat), ("response", output.stdout)])
    panic! s!"Error querying model: {output.stderr}; output: {output.stdout}"



end ChatClient

structure ChatExample where
  user : String
  assistant : String
deriving FromJson, ToJson, Repr, DecidableEq, Inhabited

def ChatExample.messages (ex : ChatExample)(responder := "assistant") : List Json :=
  [Json.mkObj [("role", "user"), ("content", ex.user)],
    Json.mkObj [("role", responder), ("content", ex.assistant)]]

abbrev ToChatExample := String × Json → MetaM (Option ChatExample)

def simpleChatExample : ToChatExample
  | (docString, data) =>
    return data.getObjValAs? String "theorem" |>.toOption.map fun thm => {user := docString, assistant:= thm}

def fullTheorem (js: Json) : Option String := do
  let thm ← js.getObjValAs? String "theorem" |>.toOption
  let name ← js.getObjValAs? String "name" |>.toOption
  let isProp ← js.getObjValAs? Bool "isProp" |>.toOption
  return if isProp then
    s!"theorem {name} : {thm} := by sorry"
  else
    s!"def {name} : {thm} := sorry"

def displayedDoc (doc: String)(isProp: Bool)(name?: Option String) : String :=
  let withName : String := match name? with
    | some n => s!" with name **{n}**"
    | none => ""
  if (isProp) then s!"Consider the mathematical theorem.
**Theorem:**
{doc}
---
Translate the above mathematical statement into a Lean 4 `theorem`{withName} with proof `by sorry`. Give the Lean code only"
  else s!"Consider the mathematical definition.
**Definition:**
{doc}
---
Translate the above mathematical definition into a Lean 4 `def`{withName}. Give the Lean code only"


def docChatExample
  (fullThm: Bool := true)(fullDoc : Bool := true) : ToChatExample
  | (docString, data) => do
    let thm? := data.getObjValAs? String "theorem" |>.toOption
    let name? := data.getObjValAs? String "name" |>.toOption
    let isProp?:= data.getObjValAs? Bool "isProp" |>.toOption
    match thm?, name?, isProp? with
    | some thm, some name, some isProp =>
    let user := if fullDoc then displayedDoc docString isProp (some name) else
      docString
    let head := if isProp then "theorem" else "definition"
    let value ←  if isProp then pure "by sorry" else
      let env ← getEnv
      let decl := env.find? name.toName
      let expr? := decl.bind (fun d => d.value?)
      let fmt? ← expr?.mapM (fun e => ppExpr e)
      pure <| fmt?.map (·.pretty) |>.getD "sorry"
    let assistant :=
      if fullThm then s!"{head} {name} : {thm} := {value}" else thm
    return some {user := user, assistant := assistant}
    | _,_,_ => return none



/--
A Json object representing a chat message
-/
def message (role content : String) : Json :=
  Json.mkObj [("role", role), ("content", content)]

/--
JSON object for the messages field in a chat prompt,
assuming that there is a system message at the beginning.
-/
def sysMessages (sys: String) (egs : List <| ChatExample)
  (query : String) : Json :=
  let head := message "system" sys
  let egArr :=
    egs.bind (fun eg  => eg.messages)
  Json.arr <| head :: egArr ++ [message "user" query] |>.toArray

def syslessAnswer := "Sure. I will answer precisely and concisely following instructions"

/--
JSON object for the messages field in a chat prompt,
assuming that there is no system message at the beginning.
-/
def syslessMessages (sys: String)(egs : List <| ChatExample)
    (query : String) : Json :=
  let headEg : ChatExample := ⟨sys, syslessAnswer⟩
  let egArr :=
    (headEg :: egs).bind (fun eg  => eg.messages)
  Json.arr <| egArr ++ [message "user" query] |>.toArray


def sysPrompt' := "You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples. Follow EXACTLY the examples given."

/--
Given a query and a list of examples, build messages for a prompt for OpenAI
-/
def mkMessages(query : String)(examples: Array ChatExample)
  (sysPrompt: String)(sysLess: Bool := false) : IO Json:= do
  if sysLess then
    return syslessMessages sysPrompt examples.toList query
  else
    return sysMessages sysPrompt examples.toList query



def mathPrompt := getTemplate "math_sys_prompt"

def sysPrompt := getTemplate "sys_prompt"

def transPrompt : IO String := do
  let sys ← sysPrompt
  let trans ← getTemplate "translate_sys_prompt"
  return s!"{sys} {trans}"
namespace ChatClient

def completions (server: ChatClient)
  (queryString: String)(sysPrompt: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let messages ←  mkMessages queryString examples sysPrompt !(server.hasSysPropmpt)
  let data ← ChatClient.query server messages params
  match data.getObjValAs? Json "choices" with
  | Except.error _ =>
    throwError m!"no choices field in {data}"
  | Except.ok data =>
    let outputs ← getMessageContents data
    return outputs

def mathCompletions (server: ChatClient)
  (queryString: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let sysPrompt ← mathPrompt
  ChatClient.completions server queryString sysPrompt n params examples

def prove (server: ChatClient)
  (thm: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "prove" [("theorem", thm)]
  ChatClient.mathCompletions server queryString n params examples


def prove_with_outline (server: ChatClient)
  (thm outline: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "prove_with_outline" [("theorem", thm), ("outline", outline)]
  ChatClient.mathCompletions server queryString n params examples

def solve (server: ChatClient)
  (problem: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "solve" [("problem", problem)]
  ChatClient.mathCompletions server queryString n params examples

def solution_to_theory (server: ChatClient)
  (problem solution: String)(n: Nat := 1)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "solution_to_theory" [("problem", problem), ("solution", solution)]
  ChatClient.mathCompletions server queryString n params examples

def structuredProof (server: ChatClient)
  (pf: String)(n: Nat := 1)
  (params: ChatParams := {n := n, stopTokens := #[]})
  : CoreM (Array Json) := do
  let instructions ← jsonProofInstructions
  let init : ChatExample := {
    user := instructions
    assistant := "Please provide the theorem and proof. I will translated this into ProofJSON format."
  }
  let examples := #[init]
  let outs ← ChatClient.mathCompletions server pf n params examples
  outs.mapM extractJsonM

def structuredProofRaw (server: ChatClient)
  (pf: String)(n: Nat := 1)
  (params: ChatParams := {n := n, stopTokens := #[]})
  : CoreM (Array String) := do
  let instructions ← jsonProofInstructions
  let init : ChatExample := {
    user := instructions
    assistant := "Please provide the theorem and proof. I will translated this into ProofJSON format."
  }
  let examples := #[init]
  let outs ← ChatClient.mathCompletions server pf n params examples
  return outs

def structuredProofFromSolution (server: ChatClient)
  (problem solution: String)(n: Nat := 1)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]) : CoreM (Array Json) := do
  let theories ← solution_to_theory server problem solution n params examples
  let results ← theories.mapM (structuredProof server)
  return results.foldl (· ++ ·) #[]

@[deprecated structuredProof]
def structuredProofFull (server: ChatClient)
  (pf: String)(n: Nat := 1)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array Json) := do
  let queryString ← structuredProofQueryFull pf
  let outs ← ChatClient.mathCompletions server queryString n params examples
  return outs.map extractJson

@[deprecated structuredProof]
def make_structured (server: ChatClient)
  (text: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "make_structured" [("text", text)]
  ChatClient.mathCompletions server queryString n params examples

def informalize (server: ChatClient)
  (code: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let text ← fromTemplate "informalize" [("code", code)]
  ChatClient.completions server text (← sysPrompt) n params examples

def add_statements (server: ChatClient)
  (text: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "add_statements" [("json", text)]
  ChatClient.mathCompletions server queryString n params examples

def expand_deductions (server: ChatClient)
  (text: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "expand_deductions" [("json", text)]
  ChatClient.mathCompletions server queryString n params examples

def expand_observations (server: ChatClient)
  (text: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "expand_observations" [("json", text)]
  ChatClient.mathCompletions server queryString n params examples

def expand_justifications (server: ChatClient)
  (text: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "expand_justifications" [("json", text)]
  ChatClient.mathCompletions server queryString n params examples

def summarize (server: ChatClient)
  (text: String)
  (examples: Array ChatExample := #[])(n: Nat := 3)
  : CoreM (Array String) := do
  let queryString ← fromTemplate "summarize" [("text", text)]
  ChatClient.mathCompletions server queryString n {n := n, stopTokens := #[]} examples

end ChatClient
