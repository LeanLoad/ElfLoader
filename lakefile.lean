import Lake
open Lake DSL System

package ElfLoader

-- ============================================================================
-- Native runtime (FFI shim — `ElfLoader/Runtime.c`, counterpart to the runtime
-- capability modules). Single C file → object file → static lib
-- linked into the AOT `elfloader` binary. No shared library: nothing
-- in this project calls FFI from the Lean interpreter (`#eval` / LSP),
-- so the `.so` would be unused.
-- ============================================================================

def cFlags : Array String := #["-O2", "-fPIC", "-Wall", "-Wextra"]

def runtimeLinkArgs : Array String :=
  #["-L.lake/build/lib", "-Wl,-Bstatic", "-lelfloader_runtime", "-Wl,-Bdynamic"]

target libelfloader_runtime (pkg : NPackage __name__) : FilePath := do
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "ElfLoader" / "Runtime.o"
  let src ← inputFile (pkg.dir / "ElfLoader" / "Runtime.c") false
  let obj ← buildO oFile src (weakArgs := #[s!"-I{lean.includeDir}"])
              (traceArgs := cFlags) (compiler := "cc")
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "elfloader_runtime") #[obj]

-- ============================================================================
-- Lean libraries and executables
-- ============================================================================

@[default_target]
lean_lib ElfLoader where
  extraDepTargets := #[`libelfloader_runtime]

lean_exe elfloader where
  root := `Main
  extraDepTargets := #[`libelfloader_runtime]
  moreLinkArgs := runtimeLinkArgs
