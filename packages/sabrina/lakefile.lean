import Lake
open Lake DSL

package sabrina where
  version := v!"1.0.0"

require logicCore from "../logic-core"

@[default_target]
lean_lib Sabrina where
  globs := #[Glob.one `Sabrina, Glob.submodules `Sabrina]

lean_lib SabrinaTests where
  srcDir := "tests"
  globs := #[Glob.one `SabrinaTests, Glob.submodules `SabrinaTests]
