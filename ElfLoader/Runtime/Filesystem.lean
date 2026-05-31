/-
Filesystem boundary used by the runtime executor.

`Runtime.File` opens one path; this module owns the *collection* of
files the loader may need. Plan structures store filesystem paths
(`DiscoveredObject.path`, `Finalize.MmapOp.path`); the executor uses a
`Filesystem` to turn each path back into an open `File` when it needs
to mmap or read.

Two instances:

  · `io`      — production: opens real files with `Runtime.File.openPath`.
  · `virtual` — pure: looks up `(path, ByteArray)` pairs in an array,
    returning the matching bytes as a `File Id`. Used by examples that
    inspect plan structures without ever executing the load ops.

`gabi 08 § Shared Object Dependencies` describes the filesystem search
the dynamic linker performs; this abstraction is the seam through which
that search reaches actual bytes.
-/

import ElfLoader.Runtime.File

namespace ElfLoader

namespace Runtime

/-- A by-path open boundary. The contract matches `Runtime.File.openPath`:
    `none` means "no entry at this path"; parse/policy failures escape
    through `m`. -/
structure Filesystem (m : Type → Type) where
  openPath : String → m (Option (File m))

/-- Path-keyed in-memory file table for pure examples. The list shape
    keeps the value debuggable (a custom `Repr` summarises each entry
    as `(path, <N bytes>)`) and gives a deterministic
    first-match-wins lookup that golden tests can rely on. -/
structure VirtualEntries where
  entries : Array (String × ByteArray)
  deriving Inhabited

namespace VirtualEntries

private def entryStr (entry : String × ByteArray) : String :=
  s!"({repr entry.fst}, <{entry.snd.size} bytes>)"

instance : Repr VirtualEntries where
  reprPrec vs _ :=
    let parts := vs.entries.toList.map entryStr
    "{ entries := #[" ++ String.intercalate ", " parts ++ "] }"

end VirtualEntries

namespace Filesystem

/-- Production filesystem: `open(2)` via `Runtime.File.openPath`. -/
def io : Filesystem IO :=
  { openPath := File.openPath }

/-- Look up a path in a `VirtualEntries`, returning the matching bytes
    as a pure `File Id`. First match wins so the iteration order in
    `entries` is what `gabi 08 § Shared Object Dependencies`-style
    examples can use to model precedence. -/
def virtual (vs : VirtualEntries) : Filesystem Id :=
  { openPath := fun path =>
      (vs.entries.find? (fun e => e.fst == path)).map
        (fun e => File.ofByteArray e.snd) }

end Filesystem

end Runtime

end ElfLoader

namespace ElfLoader.Runtime

/-- Trivial smoke test: the virtual filesystem reports `none` for an
    absent path and returns a file of the right size for a present
    path. -/
private def smokeEntries : VirtualEntries :=
  { entries := #[("/a", (ByteArray.mk #[0x11, 0x22, 0x33]))] }

#guard ((Filesystem.virtual smokeEntries).openPath "/missing").isNone
#guard ((Filesystem.virtual smokeEntries).openPath "/a"
          |>.map (fun f => f.size.toNat)) == some 3

end ElfLoader.Runtime
