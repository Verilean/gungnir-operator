import Lake
open Lake DSL

package gungnir where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Gungnir where
  globs := #[.submodules `Gungnir]

lean_exe gungnir_operator where
  root := `Gungnir.Main
