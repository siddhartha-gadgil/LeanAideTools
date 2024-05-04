import Lean
import Lake.Build.Actions
import Std.Util.Pickle
open Lean Meta Elab Command

def distL2Sq (v₁ : FloatArray) (v₂ : Array Float) : Float :=
  let squaredDiffs : Array Float :=
    (v₁.data.zip v₂).map (fun (x, y) => (x - y) * (x - y))
  squaredDiffs.foldl (Float.add) 0.0

def insertBy (l: Array <| α × Float)(cost : α → Float)(sizeBound: Nat)
    (x : α)  : Array <| α × Float :=
  match sizeBound with
  | 0 => l
  | k + 1 =>
    let cx :=  cost x
    match l.findIdx? (fun (_, cy) => cx < cy) with
    | some idx =>
      l.insertAt! idx (x, cx) |>.shrink (k + 1)
    | none => l.push (x, cx) |>.shrink (k + 1)

def bestWithCost (l: Array <| α)
  (cost : α → Float)(n: Nat)(accum : Array <| α × Float := #[]): Array <| α × Float :=
  l.foldl (fun (acc : Array <| α × Float) (x: α) =>
    insertBy acc cost n x) accum

def nearestDocsToDocEmbedding (data : Array <| (String × String × String) ×  FloatArray)
  (embedding : Array Float) (k : Nat)
  (dist: FloatArray → Array Float → Float := distL2Sq) : List (String × String × String) :=
  let pairs : Array <| ((String × String × String) × FloatArray) × Float :=
    bestWithCost data (fun (_, flArr) ↦ dist flArr embedding) k
  (pairs.map <| fun ((doc, _), _) => doc).toList


def leanToolchain : IO String := do
  let inp ← IO.FS.readFile "lean-toolchain"
  return inp.trim.drop ("leanprover/lean4:".length)

def picklePath  : IO System.FilePath := do
  return ".lake"/ "build" / "lib" /
    s!"mathlib4-concise-description-embeddings-{← leanToolchain}.olean"

def openAIKey : IO (Option String) := IO.getEnv "OPENAI_API_KEY"
def embedQuery? (doc: String) : IO <| Except String Json := do
  let key? ← openAIKey
  match key? with
  | none => return Except.error "OPENAI_API_KEY not set"
  | some key =>
    let dataJs := Json.mkObj
        [("input", doc), ("model", "text-embedding-ada-002")]
    let data := dataJs.pretty
    let out ←
      IO.Process.run {cmd := "curl", args := #["https://api.openai.com/v1/embeddings",
          "-H", "Authorization: Bearer " ++ key,
          "-H", "Content-Type: application/json",
          "--data", data]}
    return Lean.Json.parse out

unsafe def findNearestEmbeddings (doc: String) (n: Nat) :
  CommandElabM <| List (String × String × String) := do
    let picklePath ← picklePath
    withUnpickle  picklePath <|
    fun (data : Array <| (String × String × Bool × String) ×  FloatArray) => do
        let data' := data.map (fun ((doc, thm, _, name), emb) => ((doc, thm, name), emb))
        let queryRes? ← embedQuery? doc
        match queryRes? with
        | Except.ok queryRes =>
          let queryData? := queryRes.getObjVal? "data"
          match queryData? with
          | Except.error error =>
              throwError s!"no data in query result: {error}"
          | Except.ok queryDataArr =>
            let queryData := queryDataArr.getArrVal? 0 |>.toOption.get!
            match queryData.getObjValAs? (Array Float) "embedding" with
            | Except.ok queryEmbedding =>
              return nearestDocsToDocEmbedding data' queryEmbedding n distL2Sq
            | Except.error error =>
              throwError s!"no embedding in query result: {error} in {queryData}"
        | Except.error err =>
          throwError s!"error querying openai: {err}"


elab "#setup_search" : command => do
  let picklePath ← picklePath
  if (← picklePath.pathExists) then
    logWarning m!"Embeddings already present at {picklePath}, use `#setup_search!` to redownload."
  let url := "https://math.iisc.ac.in/~gadgil/data/{picklePath.fileName.get!}"
  let _ ←  IO.Process.run {
    cmd := "curl"
    args := #["-f", "-o", picklePath.toString, "-L", url]
  }
  logInfo "Fetched embeddings for search"

elab "#setup_search!" : command => do
  let picklePath ← picklePath
  let url := "https://math.iisc.ac.in/~gadgil/data/{picklePath.fileName.get!}"
  let _ ←  IO.Process.run {
    cmd := "curl"
    args := #["-f", "-o", picklePath.toString, "-L", url]
  }
  logInfo "Fetched embeddings for search"
