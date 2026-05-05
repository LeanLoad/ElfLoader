import Lake
open Lake DSL System

package leanload where
  testDriver := "test"

-- ============================================================================
-- Native runtime (FFI shims under runtime/).
--
-- Per-source object targets, then a static archive and a shared library.
-- The static archive is linked into AOT binaries; the shared library is
-- loaded by the Lean interpreter so `#eval` / editor sessions can call
-- the FFI primitives.
-- ============================================================================

def cFlags : Array String := #["-O2", "-fPIC", "-Wall", "-Wextra"]

target regionObj (pkg : NPackage __name__) : FilePath := do
  let oFile := pkg.buildDir / "runtime" / "region.o"
  let src ← inputFile (pkg.dir / "runtime" / "region.c") false
  let lean ← getLeanInstall
  buildO oFile src (weakArgs := #[s!"-I{lean.includeDir}"])
    (traceArgs := cFlags) (compiler := "cc")

target execObj (pkg : NPackage __name__) : FilePath := do
  let oFile := pkg.buildDir / "runtime" / "exec.o"
  let src ← inputFile (pkg.dir / "runtime" / "exec.c") false
  let lean ← getLeanInstall
  buildO oFile src (weakArgs := #[s!"-I{lean.includeDir}"])
    (traceArgs := cFlags) (compiler := "cc")

target libleanload_runtime (pkg : NPackage __name__) : FilePath := do
  let region ← regionObj.fetch
  let exec   ← execObj.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leanload_runtime")
    #[region, exec]

target libleanload_runtimedyn (pkg : NPackage __name__) : Dynlib := do
  let region ← regionObj.fetch
  let exec   ← execObj.fetch
  let lean ← getLeanInstall
  let leanLibDir := lean.sysroot / "lib" / "lean"
  buildLeanSharedLib "leanload_runtime"
    (pkg.sharedLibDir / nameToSharedLib "leanload_runtime")
    #[region, exec] #[]
    (weakArgs := #[s!"-Wl,-rpath,{leanLibDir}"])

-- ============================================================================
-- Lean libraries and executables
-- ============================================================================

@[default_target]
lean_lib LeanLoad where
  extraDepTargets := #[`libleanload_runtime, `libleanload_runtimedyn]

lean_lib Tests

lean_exe leanload where
  root := `Main
  extraDepTargets := #[`libleanload_runtime]
  moreLinkArgs := #[
    "-L.lake/build/lib",
    "-Wl,-Bstatic", "-lleanload_runtime", "-Wl,-Bdynamic"
  ]

lean_exe test where
  root := `Tests.Test
  extraDepTargets := #[`libleanload_runtime]
  moreLinkArgs := #[
    "-L.lake/build/lib",
    "-Wl,-Bstatic", "-lleanload_runtime", "-Wl,-Bdynamic"
  ]
