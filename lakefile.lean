import Lake
open Lake DSL

package «LeanAideTools» where
  -- add package configuration options here

lean_lib «LeanAideTools» where
  -- add library configuration options here

@[default_target]
lean_exe «leanaidetools» where
  root := `Main

@[default_target]
lean_exe nearest_embeddings where

@[default_target]
lean_exe fetch_embeddings where


require aesop from git "https://github.com/JLimperg/aesop" @ "v4.7.0"

def leanToolchain : IO String := do
  let inp ← IO.FS.readFile "lean-toolchain"
  return inp.trim.drop ("leanprover/lean4:".length)

def picklePath  : IO System.FilePath := do
  return ".lake"/ "build" / "lib" /
    s!"mathlib4-concise-description-embeddings-{← leanToolchain}.olean"

post_update pkg do
  let rootPkg ← getRootPackage
  if rootPkg.name = pkg.name then
    return
  let picklePath ← picklePath
  if (← picklePath.pathExists)  then
    logWarning s!"Embeddings already present at {picklePath}, use `#setup_search!` or `lake exe fetch -f` to redownload."
    return
  let exitCode ←  IO.Process.spawn {
    cmd := "curl"
    args := #["-f", "-o", picklePath.toString, "-L", s!"https://math.iisc.ac.in/~gadgil/data/{picklePath.fileName.get!}"]
  } >>= (·.wait)
  if exitCode ≠ 0 then
    logError s!"{pkg.name}: failed to fetch embeddings"
