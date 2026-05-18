import Lake
open Lake DSL System

package leanload

-- ============================================================================
-- Native runtime (FFI shim — `LeanLoad/Runtime.c`, sibling of
-- `LeanLoad/Runtime.lean`). Single C file → object file → static lib
-- linked into the AOT `leanload` binary. No shared library: nothing
-- in this project calls FFI from the Lean interpreter (`#eval` / LSP),
-- so the `.so` would be unused.
-- ============================================================================

def cFlags : Array String := #["-O2", "-fPIC", "-Wall", "-Wextra"]

def runtimeLinkArgs : Array String :=
  #["-L.lake/build/lib", "-Wl,-Bstatic", "-lleanload_runtime", "-Wl,-Bdynamic"]

target libleanload_runtime (pkg : NPackage __name__) : FilePath := do
  let lean ← getLeanInstall
  let oFile := pkg.buildDir / "LeanLoad" / "Runtime.o"
  let src ← inputFile (pkg.dir / "LeanLoad" / "Runtime.c") false
  let obj ← buildO oFile src (weakArgs := #[s!"-I{lean.includeDir}"])
              (traceArgs := cFlags) (compiler := "cc")
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leanload_runtime") #[obj]

-- ============================================================================
-- Lean libraries and executables
-- ============================================================================

@[default_target]
lean_lib LeanLoad where
  extraDepTargets := #[`libleanload_runtime]

lean_exe leanload where
  root := `Main
  extraDepTargets := #[`libleanload_runtime]
  moreLinkArgs := runtimeLinkArgs
