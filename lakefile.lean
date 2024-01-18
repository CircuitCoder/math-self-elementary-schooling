import Lake
open Lake DSL

package «math-self-elementary-schooling» where
  -- add package configuration options here

lean_lib «MathSelfElementarySchooling» where
  -- add library configuration options here

@[default_target]
lean_exe «math-self-elementary-schooling» where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
