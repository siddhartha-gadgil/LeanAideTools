import Lake
open Lake DSL

package «LeanAideTools» where
  -- add package configuration options here

lean_lib «LeanAideTools» where
  -- add library configuration options here

@[default_target]
lean_exe «leanaidetools» where
  root := `Main


require aesop from git "https://github.com/JLimperg/aesop" @ "v4.11.0"
