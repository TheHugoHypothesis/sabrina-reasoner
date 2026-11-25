import Lake
open Lake DSL

package sabrinaWorkspace where
  version := v!"0.1.0"

require logicCore from "packages/logic-core"
require sabrina from "packages/sabrina"

@[default_target]
lean_lib Verification where
  roots := #[`Verification]

@[default_target]
lean_exe "sabrina-alc-query" where
  root := `WorkspaceCLI.SabrinaAlcQuery

@[default_target]
lean_exe "sabrina-session" where
  root := `WorkspaceCLI.SabrinaSession
