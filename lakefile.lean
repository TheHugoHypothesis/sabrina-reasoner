import Lake
open Lake DSL

package sabrinaWorkspace where
  version := v!"1.2.1"

require logicCore from "packages/logic-core"
require sabrina from "packages/sabrina"

@[default_target]
lean_lib Verification where
  roots := #[`Verification]

@[default_target]
lean_exe "sabrina-query" where
  root := `WorkspaceCLI.SabrinaQuery

@[default_target]
lean_exe "sabrina-session" where
  root := `WorkspaceCLI.SabrinaSession
