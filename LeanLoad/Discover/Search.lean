/-
Dependency search policy for Discover.

Runtime.File owns exact opens and byte reads. This module owns the gABI dynamic
linker policy: `$ORIGIN` substitution, path-list splitting, RPATH/RUNPATH/env
ordering, and default search directories.
-/

import LeanLoad.Discover

namespace LeanLoad.Discover

namespace Search

/-- Search context for one `DT_NEEDED` edge. `originDir` is the canonical
    directory of the object containing the dynamic string; it is required only
    when `$ORIGIN` is used (gABI 08 § Substitution Sequences). -/
structure Context where
  originDir : Option String := none
  /-- `DT_RPATH`, if present. Deprecated by gABI 08, but still specified when
      `DT_RUNPATH` is absent. -/
  rpath     : Option String := none
  /-- `DT_RUNPATH`, if present. gABI 08 § Shared Object Dependencies scopes it
      only to this object's immediate `DT_NEEDED` entries. -/
  runpath   : Option String := none
  /-- Environment value for `LD_LIBRARY_PATH`. `none` means absent; `some ""`
      is a present empty list whose empty entry denotes the current directory
      (gABI 08 § Shared Object Dependencies). -/
  envPath   : Option String := none
  deriving Repr, Inhabited

/-- Default directories after `RPATH`/`LD_LIBRARY_PATH`/`RUNPATH` fail.

    gABI 08 § Shared Object Dependencies names `/usr/lib` "or such other
    directories as may be specified by the psABI supplement". x86-64 psABI
    `kernel.tex` names `/lib`, `/usr/lib`, `/lib64`, and `/usr/lib64`; Linux
    multi-arch directories are a distribution convention, not fully specified by
    gABI/psABI, so LeanLoad records this deterministic Linux-oriented policy here. -/
def defaultDirs : Array String :=
  #["/lib64", "/usr/lib64", "/lib", "/usr/lib",
    "/lib/x86_64-linux-gnu", "/usr/lib/x86_64-linux-gnu"]

private def isAsciiLetter (c : Char) : Bool :=
  decide (('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat) ∨
          ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat))

private def isAsciiDigit (c : Char) : Bool :=
  decide ('0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat)

private def isSubstNameStart (c : Char) : Bool :=
  c == '_' || isAsciiLetter c

private def isSubstNameRest (c : Char) : Bool :=
  isSubstNameStart c || isAsciiDigit c

private def takeSubstNameRest : List Char → List Char → List Char × List Char
  | [], acc => (acc.reverse, [])
  | c :: cs, acc =>
      if isSubstNameRest c then
        takeSubstNameRest cs (c :: acc)
      else
        (acc.reverse, c :: cs)

private def takeUntilRightBrace : List Char → List Char → Option (List Char × List Char)
  | [], _acc => none
  | '}' :: cs, acc => some (acc.reverse, cs)
  | c :: cs, acc => takeUntilRightBrace cs (c :: acc)

private def pushStringRev (s : String) (acc : List Char) : List Char :=
  s.toList.reverse ++ acc

private def substitutionReplacement (originDir : Option String) (name : String) :
    Except String String :=
  if name == "ORIGIN" then
    match originDir with
    | some origin => .ok origin
    | none =>
        .error "discover search: $ORIGIN used but the referring object has no canonical origin"
  else
    -- gABI 08 § Substitution Sequences specifies `$ORIGIN`; behavior for every
    -- other name is unspecified, so LeanLoad rejects it instead of guessing.
    .error s!"discover search: unsupported dynamic-string substitution ${name}"

private def expandDynamicChars (originDir : Option String) :
    Nat → List Char → List Char → Except String String
  | 0, _acc, _chars => .error "discover search: internal substitution fuel exhausted"
  | _fuel + 1, acc, [] => .ok (String.ofList acc.reverse)
  | fuel + 1, acc, '$' :: '{' :: rest =>
      match takeUntilRightBrace rest [] with
      | none => .error "discover search: unterminated ${...} substitution"
      | some (nameChars, after) => do
          let replacement ← substitutionReplacement originDir (String.ofList nameChars)
          expandDynamicChars originDir fuel (pushStringRev replacement acc) after
  | fuel + 1, acc, '$' :: c :: rest =>
      if isSubstNameStart c then do
        let (nameChars, after) := takeSubstNameRest rest [c]
        let replacement ← substitutionReplacement originDir (String.ofList nameChars)
        expandDynamicChars originDir fuel (pushStringRev replacement acc) after
      else
        -- gABI leaves this case unspecified; make malformed inputs explicit.
        .error "discover search: '$' is not followed by a substitution name"
  | _fuel + 1, _acc, ['$'] =>
      .error "discover search: '$' is not followed by a substitution name"
  | fuel + 1, acc, c :: rest =>
      expandDynamicChars originDir fuel (c :: acc) rest

/-- Expand gABI dynamic-string substitutions in a `DT_NEEDED`, `DT_RUNPATH`, or
    compatibility `DT_RPATH` string. Only `$ORIGIN` is specified; unsupported or
    malformed `$...` forms are rejected because gABI marks their behavior
    unspecified. -/
def expandDynamicString (originDir : Option String) (s : String) : Except String String :=
  expandDynamicChars originDir (s.toList.length + 1) [] s.toList

/-- Split `DT_RUNPATH`/`DT_RPATH`: colon-separated, preserving empty entries as
    the current directory (gABI 08 § Shared Object Dependencies). -/
def splitDynamicPathList (s : String) : Array String :=
  (s.splitOn ":").toArray

/-- Split `LD_LIBRARY_PATH`. gABI accepts a semicolon between directory lists and
    says the dynamic linker does not distinguish the two lists, so both `:` and
    `;` are separators. Empty entries are preserved as the current directory. -/
def splitEnvPathList (s : String) : Array String :=
  (((s.splitOn ";").map (fun chunk => chunk.splitOn ":")).flatten).toArray

private def expandDynamicDirs (originDir : Option String) (pathList : String) :
    Except String (Array String) :=
  (splitDynamicPathList pathList).mapM (expandDynamicString originDir)

private def joinSearchDir (dir soname : String) : String :=
  if dir.isEmpty then soname else dir ++ "/" ++ soname

/-- Candidate paths for one dependency search, before exact `open(2)`.

    Implemented gABI 08 § Shared Object Dependencies rules:

    * `DT_NEEDED` with a slash is used directly after dynamic-string expansion.
    * If `DT_RUNPATH` is absent, deprecated `DT_RPATH` is searched before
      `LD_LIBRARY_PATH`; if both appear, gABI says only `DT_RUNPATH` is processed.
    * `LD_LIBRARY_PATH` precedes `DT_RUNPATH` and accepts both `:` and `;`.
    * Empty path-list entries denote the current directory.
    * Default directories are searched last.

    Deliberate policy where gABI is weak or host-specific:

    * The default directory set/order is Linux x86-64 oriented; gABI delegates
      the full set to psABI/system policy.
    * `$ORIGIN` is expanded in `DT_RPATH` too. gABI's substitution text names
      `DT_NEEDED` and `DT_RUNPATH`; Linux loaders also support `$ORIGIN` in the
      deprecated `DT_RPATH`, and rejecting it would make the otherwise-specified
      `DT_RPATH` fallback much less useful.
    * Privileged/setuid restrictions are not modeled: LeanLoad does not perform
      kernel `execve` privilege transitions, so loading such programs through
      this userspace loader would already be outside the supported model. -/
def candidates (needed : String) (ctx : Context) : Except String (Array String) := do
  let soname ← expandDynamicString ctx.originDir needed
  if soname.contains '/' then
    return #[soname]
  let mut dirs : Array String := #[]
  match ctx.runpath, ctx.rpath with
  | none, some rpath => dirs := dirs ++ (← expandDynamicDirs ctx.originDir rpath)
  | _, _ => pure ()
  if let some envPath := ctx.envPath then
    dirs := dirs ++ splitEnvPathList envPath
  if let some runpath := ctx.runpath then
    dirs := dirs ++ (← expandDynamicDirs ctx.originDir runpath)
  dirs := dirs ++ defaultDirs
  return dirs.map (fun dir => joinSearchDir dir soname)

/-- Read `LD_LIBRARY_PATH` and produce the gABI dependency-search candidate list. -/
def candidatesIO (needed : String) (ctx : Context) : ExceptT String IO (Array String) :=
  ExceptT.mk <| do
    let envPath ← IO.getEnv "LD_LIBRARY_PATH"
    pure (candidates needed { ctx with envPath })

@[extern "leanload_canonical_origin_dir"]
private opaque canonicalOriginDirImpl (path : @& String) : IO String

/-- Canonical directory for `$ORIGIN` expansion. gABI 08 § Substitution
    Sequences requires an absolute pathname with no symlinks and no `.`/`..`
    components; the C shim uses `realpath(3)` to provide that fact. -/
def canonicalOriginDir (path : String) : ExceptT String IO String :=
  ExceptT.mk <| (show IO (Except String String) from
    try
      let origin ← canonicalOriginDirImpl path
      pure (.ok origin)
    catch e =>
      pure (.error s!"discover search: cannot canonicalize $ORIGIN directory for '{path}': {e}"))

#guard splitEnvPathList "/a:/b;/c:" == #["/a", "/b", "/c", ""]
#guard splitDynamicPathList "/a:/b:" == #["/a", "/b", ""]

#guard
  match candidates "/tmp/libx.so" {} with
  | .ok xs => xs == #["/tmp/libx.so"]
  | .error _ => false

#guard
  match candidates "libx.so" { originDir := some "/app/bin", runpath := some "$ORIGIN/lib" } with
  | .ok xs => xs[0]? == some "/app/bin/lib/libx.so"
  | .error _ => false

#guard
  match candidates "libx.so" { originDir := none, rpath := some "/old", envPath := some "/env" } with
  | .ok xs => xs[0]? == some "/old/libx.so" && xs[1]? == some "/env/libx.so"
  | .error _ => false

#guard
  match candidates "libx.so"
      { originDir := none, rpath := some "/old", runpath := some "/run", envPath := some "" } with
  | .ok xs =>
      xs[0]? == some "libx.so" && xs[1]? == some "/run/libx.so" &&
        !xs.contains "/old/libx.so"
  | .error _ => false

end Search

end LeanLoad.Discover
