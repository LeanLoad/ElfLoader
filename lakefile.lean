import Lake
open Lake DSL System

package leanload where
  testDriver := "test"

-- ============================================================================
-- Native runtime (FFI shims under runtime/).
--
-- Per-source object targets, archived into a static lib that is linked
-- into the AOT binaries (`leanload`, `test`). No shared library: nothing
-- in this project calls FFI from the Lean interpreter (`#eval` / LSP),
-- so the `.so` would be unused.
-- ============================================================================

def cFlags : Array String := #["-O2", "-fPIC", "-Wall", "-Wextra"]

def runtimeLinkArgs : Array String :=
  #["-L.lake/build/lib", "-Wl,-Bstatic", "-lleanload_runtime", "-Wl,-Bdynamic"]

target libleanload_runtime (pkg : NPackage __name__) : FilePath := do
  let lean ← getLeanInstall
  let buildRuntimeObj (name : String) := do
    let oFile := pkg.buildDir / "runtime" / s!"{name}.o"
    let src ← inputFile (pkg.dir / "runtime" / s!"{name}.c") false
    buildO oFile src (weakArgs := #[s!"-I{lean.includeDir}"])
      (traceArgs := cFlags) (compiler := "cc")
  let region ← buildRuntimeObj "region"
  let exec   ← buildRuntimeObj "exec"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leanload_runtime")
    #[region, exec]

-- ============================================================================
-- Lean libraries and executables
-- ============================================================================

@[default_target]
lean_lib LeanLoad where
  extraDepTargets := #[`libleanload_runtime]

lean_exe leanload where
  root := `LeanLoad.Main
  extraDepTargets := #[`libleanload_runtime]
  moreLinkArgs := runtimeLinkArgs

lean_exe test where
  root := `LeanLoad.Test
  extraDepTargets := #[`libleanload_runtime]
  moreLinkArgs := runtimeLinkArgs
