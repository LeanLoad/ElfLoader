/-
Object-finder boundary for Discover.

Production instantiates this with runtime path search, open, and checked parse.
Examples use an in-memory finder over already-built ELFs.
-/

import ElfLoader.Discover.Names

namespace ElfLoader.Discover

/-- Object finder seam used by discovery traversal. -/
structure ObjectFinder (m : Type → Type) where
  /-- Find and parse the main object. This owns the effectful boundary from a user
      path to the checked `DiscoveredObject` that seeds traversal. -/
  findMain : String → m DiscoveredObject
  /-- Find a dependency for this work item. `none` means "not found"; parse failures and
      policy failures escape through the monad's error mechanism. -/
  findDependency : WorkItem → m (Option DiscoveredObject)

end ElfLoader.Discover
