/-
Shared Discover data types.

These are the small records that define the boundary between Parse and
Discover: checked ELFs enter as `LoadedObject`s, and dependency traversal
passes explicit `WorkItem`s instead of loose strings.
-/

import LeanLoad.Parse
import LeanLoad.Runtime.Basic

namespace LeanLoad.Discover

open LeanLoad
open LeanLoad.Parse

/-- One loaded object. Production policy:
    NEEDED-loaded deps must have `DT_SONAME` (used as `.name`);
    the main executable's `.name` is `basename mainPath` (executables
    conventionally don't set SONAME). -/
structure LoadedObject where
  /-- Canonical dedup key. For NEEDED deps: `elf.soname.get!` (production
      requires DT_SONAME). For the main executable: `basename mainPath`. -/
  name : String
  /-- Open read-only file, kept for extra parse reads and file-backed mmap.
      Production paths carry C-backed read/mmap closures plus observed size;
      examples use a dummy `Runtime.File`. -/
  handle : Runtime.File
  /-- Checked ELF — output of `Parse.parseFile`. The type is the witness
      that PT_LOAD well-formedness held and every dynamic relocation
      was located against a covering segment. -/
  elf : Elf
  deriving Repr

/-- One dependency request to resolve next. `needed` is the raw `DT_NEEDED`
    string from the referring object; `runpath` is that object's
    `DT_RUNPATH`, if present. This keeps traversal work explicit instead
    of passing loose strings around. -/
structure WorkItem where
  needed  : String
  runpath : Option String
  deriving Repr

namespace WorkItem

/-- Build the work items created by one object's `DT_NEEDED` array. -/
def ofNeededArray (runpath : Option String) (needed : Array String) :
    List WorkItem :=
  needed.toList.map (fun name => { needed := name, runpath })

end WorkItem

end LeanLoad.Discover
