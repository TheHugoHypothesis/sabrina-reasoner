import Lake
open Lake DSL

package logicCore where
  version := v!"1.0.0"


@[default_target]
lean_lib Logic where
  globs := #[Glob.one `Logic, Glob.submodules `Logic]

lean_lib LogicTests where
  srcDir := "tests"
  globs := #[Glob.one `LogicTests, Glob.submodules `LogicTests]

lean_exe "logic-roundtrip" where
  root := `Executables.LogicRoundtrip
