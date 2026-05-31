/-
Discover naming policy.

Discover deduplicates by canonical object name. Dependencies use `DT_SONAME`
at the provider boundary; the main executable is path-discovered, so its canonical
name is the path basename.
-/

import ElfLoader.Discover

namespace ElfLoader.Discover

namespace DiscoveredObject

/-- Canonical name for the path-discovered main executable. -/
def mainName (mainPath : String) : String :=
  (mainPath.splitOn "/").getLast?.getD mainPath

/-- Construct the main `DiscoveredObject` from a user-supplied path. The canonical
    name is the path basename — executables don't conventionally set
    `DT_SONAME`, and main is path-discovered (not NEEDED-driven), so we don't
    consult `elf.soname`. The path is recorded verbatim so downstream stages
    can refer back to it without re-deriving. -/
def ofMain (mainPath : String) (originDir : Option String) (elf : Parse.Elf) :
    DiscoveredObject :=
  { name := mainName mainPath, path := mainPath, originDir, elf }

end DiscoveredObject

end ElfLoader.Discover
