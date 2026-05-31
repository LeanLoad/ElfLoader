/-
`deriving Decodable` handler.

For any raw fixed-width structure type whose fields all have a `Decodable`
instance, generates:

    instance : Decodable T where
      byteSize := ByteSize.ofNat (Decodable.byteSize (α := F₁)).toNat + …
      decoder := do
        let f₁ ← Decodable.decoder
        …
        return { f₁, … }

`Prop` fields are rejected with a direct error. Checked types should decode a
raw structure first, then hand-roll validation that attaches proof witnesses.
-/

import ElfLoader.Parse.Decode.Decodable
import Lean

open Lean Elab Command Meta Parser

namespace ElfLoader.Parse.Decodable

/-- Return the last component of a structure field name as source text. -/
private def fieldIdent (fieldName : Name) : String :=
  fieldName.getString!

/-- Run `k` over a structure projection's result type. -/
private def withFieldResultType (typeName : Name) (fieldName : Name) (k : Expr → MetaM α) :
    CommandElabM α := do
  liftTermElabM do
    let projInfo ← getConstInfo (typeName ++ fieldName)
    forallTelescope projInfo.type fun _ body => k body

/-- Generate `instance : Decodable T`. Every field contributes its fixed byte
    size and is decoded from bytes. Proof fields are intentionally rejected:
    split the structure into a raw decodable type and a checked type with a
    hand-rolled decoder/smart constructor. -/
private def mkInstance (typeName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some sInfo := getStructureInfo? env typeName
    | throwError "deriving Decodable: {typeName} is not a structure"
  let fieldNames := sInfo.fieldNames
  if fieldNames.isEmpty then
    throwError "deriving Decodable: {typeName} has no fields"
  let mut sizes : Array String := #[]
  let mut lets : Array String := #[]
  for fieldName in fieldNames do
    let field := fieldIdent fieldName
    let (fieldType, isFieldProp) ← withFieldResultType typeName fieldName fun body => do
      return ((← ppExpr body).pretty, ← isProp body)
    if isFieldProp then
      throwError "deriving Decodable: {typeName}.{field} is a Prop field; \
        split into a raw Decodable type and a checked type with a hand-rolled decoder"
    else
      sizes := sizes.push s!"(ElfLoader.Parse.Decodable.byteSize (α := {fieldType})).toNat"
      lets := lets.push s!"    let {field} : {fieldType} ← ElfLoader.Parse.Decodable.decoder"
  let fields := String.intercalate ",\n" (fieldNames.toList.map (fun f => s!"      {fieldIdent f}"))
  let byteSize := if sizes.isEmpty then "0" else String.intercalate " + " sizes.toList
  let cmdString :=
    s!"instance : ElfLoader.Parse.Decodable {typeName} where\n" ++
    s!"  byteSize := ElfLoader.ByteSize.ofNat ({byteSize})\n" ++
    "  decoder := do\n" ++
    String.intercalate "\n" lets.toList ++
    "\n    return {\n" ++ fields ++ "\n    }"
  match runParserCategory env `command cmdString with
  | .ok stx   => elabCommand stx
  | .error e  =>
      throwError "deriving Decodable: failed to parse generated instance for {typeName}: {e}\n\
        {cmdString}"

/-- Deriving handler: dispatches each requested type to `mkInstance`. -/
private def handler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.isEmpty then return false
  for declName in declNames do
    mkInstance declName
  return true

initialize
  registerDerivingHandler ``ElfLoader.Parse.Decodable handler

end ElfLoader.Parse.Decodable
