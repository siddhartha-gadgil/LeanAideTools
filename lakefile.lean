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
