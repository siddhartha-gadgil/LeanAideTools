import LeanAideTools.Embeddings
open Lean Json

unsafe def main(args : List String) : IO UInt32 := do
  let picklePath ← picklePath
  IO.eprintln s!"Reading embeddings from {picklePath}"
  withUnpickle  picklePath <|
    fun (data : Array <| (String × String × Bool × String) ×  FloatArray) => do
    IO.eprintln "Embeddings loaded"
    let res ← findNearestEmbeddings data args[0]! 5
    IO.eprintln "Results:"
    let js := Json.arr <| res.toArray.map (fun (doc, thm, name) => Json.mkObj [("description", doc), ("theorem", thm), ("name", name)])
    IO.println js.compress
  return 0
