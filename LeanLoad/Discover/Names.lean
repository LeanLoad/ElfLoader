/-
Discover naming policy.

Discover deduplicates by canonical object name. Dependencies use `DT_SONAME`
at the provider boundary; the main executable is path-loaded, so its canonical
name is the path basename.
-/

import LeanLoad.Discover.Basic

namespace LeanLoad.Discover

namespace LoadedObject

/-- Canonical name for the path-loaded main executable. -/
def mainName (mainPath : String) : String :=
  (mainPath.splitOn "/").getLast?.getD mainPath

/-- Construct the main `LoadedObject` from a user-supplied path. The canonical
    name is the path basename — executables don't conventionally set
    `DT_SONAME`, and main is path-loaded (not NEEDED-driven), so we don't
    consult `elf.soname`. -/
def ofMain (mainPath : String) (handle : Runtime.File)
    (elf : Parse.Elf) : LoadedObject :=
  { name := mainName mainPath, handle, elf }

end LoadedObject

end LeanLoad.Discover
