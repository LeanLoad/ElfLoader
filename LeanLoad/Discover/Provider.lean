/-
Object-finder boundary for Discover.

Production instantiates this with runtime path search, open, and checked parse.
Examples use an in-memory finder over already-built ELFs.
-/

import LeanLoad.Discover.Names

namespace LeanLoad.Discover

/-- Object finder seam used by discovery traversal. -/
structure ObjectFinder (m : Type → Type) where
  /-- Find and parse the main object. This owns the effectful boundary from a user
      path to the checked `LoadedObject` that seeds traversal. -/
  findMain : String → m LoadedObject
  /-- Find a dependency for this work item. `none` means "not found"; parse failures and
      policy failures escape through the monad's error mechanism. -/
  findDependency : WorkItem → m (Option LoadedObject)

end LeanLoad.Discover
