import LeanAideTools.Embeddings
open Lean Json

unsafe def main(args : List String) : IO UInt32 := do
  let force := args.contains "-f"
  let picklePath ← picklePath
  if (← picklePath.pathExists) && !force then
    IO.eprintln s!"Embeddings already present at {picklePath}, use `#setup_search!` or `lake exe fetch -f` to redownload."
    return 0
  let url := s!"https://math.iisc.ac.in/~gadgil/data/{picklePath.fileName.get!}"
  -- IO.eprintln s!"Downloading embeddings to {url}"

  let _ ←  IO.Process.run {
    cmd := "curl"
    args := #["-f", "-o", picklePath.toString, "-L", url]
  }
  IO.println "Fetched embeddings for search"

  return 0
