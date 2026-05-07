/-
`deriving BytesDecode` handler.

For any structure type all of whose fields have a `BytesDecode`
instance, generates:

    instance : BytesDecode T where
      decode := do return { f₁ := ← BytesDecode.decode,
                            f₂ := ← BytesDecode.decode, … }

Each `← BytesDecode.decode` is dispatched by the field's declared
type. For primitive widths we provide instances in `Parse.Bytes`
(`UInt8/16/32/64`); composite fields work as long as their type
has its own `BytesDecode` instance (typically also derived).

Used by every struct under `LeanLoad/Parse/` whose parser is a
left-to-right sequence of fixed-width field decodes. Structs that
need pre/post checks (e.g. `RawIdent`'s magic-byte prefix) write
their instance manually.
-/

import LeanLoad.Parse.Bytes
import Lean

open Lean Elab Command

namespace LeanLoad.Parse.BytesDecode

/-- Generate `instance : BytesDecode T` whose `decode` is an
    applicative chain `T.mk <$> decode <*> decode <*> …` — one
    `<*> decode` per declared field, threading the typeclass dispatch
    on each field's declared type. -/
private def mkInstance (typeName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some sInfo := getStructureInfo? env typeName
    | throwError "deriving BytesDecode: {typeName} is not a structure"
  let nFields := sInfo.fieldNames.size
  if nFields == 0 then
    throwError "deriving BytesDecode: {typeName} has no fields"
  let typeId := mkIdent typeName
  let ctorId := mkIdent (typeName ++ `mk)
  let decodeStx ← `(LeanLoad.Parse.BytesDecode.decode)
  -- ctor <$> decode <*> decode <*> … (nFields total decodes)
  let mut body ← `($ctorId <$> $decodeStx)
  for _ in [1:nFields] do
    body ← `($body <*> $decodeStx)
  let cmd ← `(instance : LeanLoad.Parse.BytesDecode $typeId where decode := $body)
  elabCommand cmd

/-- Deriving handler: dispatches each requested type to `mkInstance`. -/
private def handler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.isEmpty then return false
  for declName in declNames do
    mkInstance declName
  return true

initialize
  registerDerivingHandler ``LeanLoad.Parse.BytesDecode handler

end LeanLoad.Parse.BytesDecode
