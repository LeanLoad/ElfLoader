/-
Library path resolution.

Spec: gabi 08 § Shared Object Dependencies.

Given a `DT_NEEDED` string and a search context (per-binary
`DT_RUNPATH`, the host's `LD_LIBRARY_PATH`, default paths), enumerate
the candidate filesystem locations to probe, in priority order. The
function is pure; the actual filesystem access happens in `Discover`.

Rules:

1. If the name contains `/`, it is treated as a path directly — no
   search is performed.
2. Otherwise, search in order:
   a. `LD_LIBRARY_PATH` directories.
   b. The owning object's `DT_RUNPATH` directories.
   c. Default system paths (caller-supplied; empty by default for
      hermetic test setups).

`DT_RPATH` is deprecated and intentionally not honoured.
-/

namespace LeanLoad.Link.Search

/-- Split a colon-separated path list. Empty entries are dropped. -/
def parsePathList (s : String) : Array String :=
  s.splitOn ":" |>.filter (! ·.isEmpty) |>.toArray

#guard parsePathList "" = #[]
#guard parsePathList "/a:/b" = #["/a", "/b"]
#guard parsePathList "/a::/b" = #["/a", "/b"]

/-- Search context for one resolution call. -/
structure Context where
  /-- The owning object's `DT_RUNPATH`, if any. Per-binary, not transitive. -/
  runpath  : Option String := none
  /-- Host's `LD_LIBRARY_PATH`, if set. -/
  envPath  : Option String := none
  /-- Caller-supplied default paths (`/lib`, `/usr/lib`, ...). Empty for
      hermetic tests. -/
  defaults : Array String  := #[]

/-- Enumerate candidate paths for `soname` under `ctx`. If `soname`
    contains `/` the result is `#[soname]` (treated as a path). -/
def candidates (soname : String) (ctx : Context) : Array String :=
  if soname.contains '/' then
    #[soname]
  else
    let dirs : Array String := Id.run do
      let mut acc : Array String := #[]
      if let some p := ctx.envPath  then acc := acc ++ parsePathList p
      if let some p := ctx.runpath  then acc := acc ++ parsePathList p
      acc := acc ++ ctx.defaults
      return acc
    dirs.map (fun d => s!"{d}/{soname}")

#guard candidates "/abs/path" {} = #["/abs/path"]
#guard candidates "libfoo.so" { runpath := some "/a:/b" } = #["/a/libfoo.so", "/b/libfoo.so"]

end LeanLoad.Link.Search
