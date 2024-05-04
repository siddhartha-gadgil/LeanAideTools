import LeanAideTools.Embeddings

unsafe def main(args : List String) : IO UInt32 := do
  let picklePath ← picklePath
  IO.println s!"Reading embeddings from {picklePath}"
  withUnpickle  picklePath <|
    fun (data : Array <| (String × String × Bool × String) ×  FloatArray) => do
    IO.println "Embeddings loaded"
    let res ← findNearestEmbeddings data args[0]! 5
    IO.println "Results:"
    res.forM (fun (doc, thm, name) => IO.println s!"{doc} {thm} {name}")
  return 0
