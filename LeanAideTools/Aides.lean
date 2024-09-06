import Lean
import Lean.Meta
import Lean.Elab
import Lean.Parser
import Lean.Parser.Extension
import Batteries.Data.List.Basic

open Lean Meta Elab Parser Tactic

def Lean.Expr.view (expr: Expr) : MetaM String := do
  let expr ← instantiateMVars expr
  let fmt ← PrettyPrinter.ppExpr expr
  return fmt.pretty

def EIO.runToIO' (eio: EIO Exception α) : IO α  := do
  match ←  eio.toIO' with
  | Except.ok x =>
      pure x
  | Except.error e =>
      let msg ← e.toMessageData.toString
      IO.throwServerError msg

def EIO.spawnToIO (eio: EIO Exception α) : IO <| Task <| IO α  := do
  let task ←  eio.asTask (prio := Task.Priority.max)
  return task.map (fun eio =>
    match eio with
    | Except.ok x =>
        pure x
    | Except.error e => do
        let msg ←  e.toMessageData.toString
        IO.throwServerError msg)

def EIO.asyncIO (eio: EIO Exception α) : IO α  := do
  let task ← EIO.spawnToIO eio
  task.get

-- code from Leo de Moura
def getTactics (s : TSyntax ``tacticSeq) : Array (TSyntax `tactic) :=
  match s with
  | `(tacticSeq| { $[$t]* }) => t
  | `(tacticSeq| $[$t]*) => t
  | _ => #[]

def appendTactics (s t : TSyntax ``tacticSeq) :
  MetaM (TSyntax ``tacticSeq) := do
  let ts := getTactics t
  match s with
  | `(tacticSeq| { $[$t]* }) =>
      let ts' := t ++ ts
      `(tacticSeq| { $[$ts']* })
  | `(tacticSeq| $[$t]*) =>
      let ts' := t ++ ts
      `(tacticSeq| $[$ts']*)
  | _ => pure t

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

def consTactics (h: TSyntax `tactic)(s : TSyntax ``tacticSeq):
  MetaM (TSyntax ``tacticSeq) := do
  match s with
  | `(tacticSeq| { $[$t]* }) =>
      let ts' := #[h] ++ t
      `(tacticSeq| { $[$ts']* })
  | `(tacticSeq| $[$t]*) =>
      let ts' := #[h] ++ t
      `(tacticSeq| $[$ts']*)
  | _ => pure s


def threadNum : IO Nat := do
  try
    let info ←  IO.FS.readFile <| System.mkFilePath ["/", "proc", "cpuinfo"]
    return (info.splitOn "processor" |>.length) - 1
  catch _ =>
    return 4

def leanToolchain : IO String := do
  let inp ← IO.FS.readFile "lean-toolchain"
  return inp.trim.drop ("leanprover/lean4:".length)


def jsonLines [ToJson α] (jsl : Array α) : String :=
  let lines := jsl.map (fun j => Json.compress <| toJson j)
  lines.foldl (fun acc l => acc ++ l ++ "\n") ""

partial def List.batchesAux (l: List α)(size: Nat)(accum : List (List α)) : List (List α) :=
  match l with
  | [] => accum
  | _ =>
    let batch := l.take size
    let rest := l.drop size
    batchesAux rest size (batch::accum)

def List.batches (l: List α)(size: Nat) : List (List α) :=
  batchesAux l size []

def Array.batches (l: Array α)(size: Nat) : Array (Array α) :=
  (l.toList.batches size).map (fun l => l.toArray) |>.toArray

def List.batches' (l: List α)(numBatches: Nat) : List (List α) :=
  let size :=
    if l.length % numBatches = 0 then
      l.length / numBatches
    else
      l.length / numBatches + 1
  batchesAux l size []

def Array.batches' (l: Array α)(numBatches: Nat) : Array (Array α) :=
  (l.toList.batches' numBatches).map (fun l => l.toArray) |>.toArray

/-
Obtaining names of constants
-/

def excludePrefixes := [`Lean, `Std, `IO,
          `Char, `String, `ST, `StateT, `Repr, `ReaderT, `EIO, `BaseIO, `UInt8, ``UInt16, ``UInt32, ``UInt64, `Mathlib.Tactic, `Mathlib.Meta, `LeanAide.Meta, `Aesop, `Qq, `SlimCheck]

/-- This is a slight modification of `Parser.runParserCategory` due to Scott Morrison/Kim Liesinger. -/
def parseAsTacticSeq (env : Environment) (input : String) (fileName := "<input>") :
    Except String (TSyntax ``tacticSeq) :=
  let p := andthenFn whitespace Tactic.tacticSeq.fn
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if s.hasError then
    Except.error (s.toErrorMsg ictx)
  else if input.atEnd s.pos then
    Except.ok ⟨s.stxStack.back⟩
  else
    Except.error ((s.mkError "end of input").toErrorMsg ictx)


/-- Parsing with a group, for example to extract context -/
def parseGroup (env : Environment) (input : String) (parsers: List Parser) (fileName := "<input>") :
    Except String Syntax :=
  match parsers with
  | [] => Except.error "no parsers"
  | head :: tail =>
  let p := tail.foldl (fun acc p => acc <|> p) head |>.fn
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if s.hasError then
    Except.error (s.toErrorMsg ictx)
  else if input.atEnd s.pos then
    Except.ok s.stxStack.back
  else
    Except.error ((s.mkError "end of input").toErrorMsg ictx)

def getName? (stx: Syntax) : Option Name :=
  match stx with
  | `($n:ident) => some n.getId
  | _ => none

open System IO.FS
def appendFile (fname : FilePath) (content : String) : IO Unit := do
  let h ← Handle.mk fname Mode.append
  h.putStrLn content
  h.flush

def appendLog (logFile: String) (content : Json) : IO Unit := do
  let fname : FilePath := "rawdata/" / ("log_" ++ logFile ++ ".jsonl")
  appendFile fname content.compress

def gitHash : IO String := do
  let hash ← IO.Process.output { cmd := "git", args := #["rev-parse", "--short", "HEAD"] }
  return hash.stdout.trim

def colEqSegments (s: String) : List String :=
  let pieces := s.splitOn ":="
  match pieces with
  | [] => []
  | head :: tail =>
    tail.scanl (fun acc x => acc ++ ":=" ++ x) head |>.map (String.trim)

def splitColEqSegments (ss: Array String) : Array String :=
  ss.toList.bind colEqSegments |>.toArray

def trivialEquality : Syntax → CoreM Bool
  | `($a = $b) => return a == b
  | _ => return false


def codeBlock (code: String) (s: String) : String :=
  let fullSplit := s.splitOn s!"```{code}"
  let split := if fullSplit.length > 1
    then fullSplit.get! 1 else
    s.splitOn "```" |>.get! 1
  split.splitOn "```" |>.get! 0

def codeBlock? (code: String) (s: String) : Option String := do
  let split ←   s.splitOn s!"```{code}" |>.get? 1 |>.orElse fun _ =>
    s.splitOn "```" |>.get? 1
  split.splitOn "```" |>.get? 0

def extractJson (s: String) : Json :=
  let code := codeBlock? "json" s |>.getD s
  let code := code.trim
  let code' :=
    code.replace "\n" " " |>.replace "\t" " " |>.replace "\\" "\\\\"
  match Json.parse code' with
  | Except.ok j => j
  | Except.error _ => Json.str code

def extractJsonM (s: String) : CoreM Json :=
  let code := codeBlock? "json" s |>.getD s
  let code := code.trim
  match Json.parse code with
  | Except.ok j => do
    logInfo s!"parsed JSON: {j}"
    appendLog "json_parsed" j
    return j
  | Except.error e => do
    logWarning  m!"Error parsing JSON: {e}"
    appendLog "json_error" (Json.str code)
    appendLog "json_error" (Json.str e)
    return Json.str code

def partialParser  (parser : Parser) (input : String) (fileName := "<input>") : MetaM <| Except String (Syntax × String × String) := do
  let env ← getEnv
  -- let c := mkParserContext (mkInputContext input fileName) { env := env, options := {} }
  let p := andthenFn whitespace parser.fn
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  let stack := s.stxStack.toSubarray.array.filter fun s => !s.hasMissing
  if stack.isEmpty &&  s.hasError then
    return Except.error (s.toErrorMsg ictx)
  else
    let head := input.extract 0 s.pos
    let stx := stack.back
    return Except.ok (stx, head, input.drop head.length)

partial def polyParser (parser: Parser) (input: String) (fileName := "<input>") : MetaM <| Option  Syntax := do
  -- logInfo s!"parsing {input}"
  match (← partialParser parser input fileName) with
  | Except.ok (stx, _, _) =>
    -- logInfo s!"parsed {stx}"
    return some stx
  | Except.error _ =>
    let tail := input.dropWhile (fun c => c != '\n') |>.drop 1 |>.trim
    if tail.isEmpty then
      -- logInfo "no more input; tail empty"
      return none
    else
      return (← polyParser parser tail fileName)

partial def lineBlocks (input: String) : List String :=
  let tail := input.dropWhile (fun c => c != '\n') |>.drop 1
    if tail.isEmpty then
      [input]
    else
      let tailBlocks := lineBlocks tail
      let head := input.takeWhile (fun c => c != '\n')
      head :: (tailBlocks.map (fun b => head ++ "\n" ++ b)) ++ tailBlocks



def termKinds : MetaM <| SyntaxNodeKindSet :=  do
    let env ← getEnv
    let categories := (parserExtension.getState env).categories
    let termCat? := getCategory categories `term
    return termCat?.get!.kinds

def termKindList : MetaM <| List SyntaxNodeKind := do
    let s ← termKinds
    pure <| s.toList.map (·.1)

open PrettyPrinter in
def delabCustom (e : Expr) : MetaM Term := do
  -- let myNatDecl : OpenDecl := .simple `MyNat []
  let (stx, _) ←
    delabCore e {} (
    withOptions (fun o₁ =>
                    let o₂ := pp.motives.all.set o₁ true
                    let o₃ := pp.fieldNotation.set o₂ false
                    let o₄ := pp.proofs.set o₃ true
                    let o₅ := pp.deepTerms.set o₄ true
                    let o₆ := pp.instantiateMVars.set o₅ true
                    pp.unicode.fun.set o₆ true) <|
                    -- withReader (fun c => {c with openDecls := [myNatDecl]} )
                    do
                      Delaborator.delab)
  return stx
