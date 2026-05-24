/-
`deriving Decodable` handler.

For any structure type whose data fields have a `Decodable` instance and whose
proof fields are decidable, generates:

    instance : Decodable T where
      byteSize := Decodable.byteSize (α := F₁) + …
      decode := do
        let f₁ ← Decodable.decode
        …
        let ⟨h⟩ ← Decodable.require "T.h" (predicate over decoded fields)
        return { f₁, …, h }
-/

import LeanLoad.Parse.Decode.Decodable
import Lean

open Lean Elab Command Meta Parser

namespace LeanLoad.Parse.Decodable

/-- Return the last component of a structure field name as source text. -/
private def fieldIdent (fieldName : Name) : String :=
  fieldName.getString!

/-- Run `k` over a structure projection's result type. -/
private def withFieldResultType (typeName : Name) (fieldName : Name) (k : Expr → MetaM α) :
    CommandElabM α := do
  liftTermElabM do
    let projInfo ← getConstInfo (typeName ++ fieldName)
    forallTelescope projInfo.type fun _ body => k body

/-- Pretty-print a field projection result type and rewrite `self.field`
    projections to the local variables generated for previously decoded fields. -/
private def fieldTypeTerm (typeName : Name) (fieldNames : Array Name) (fieldName : Name) :
    CommandElabM String :=
  withFieldResultType typeName fieldName fun body => do
    let mut prop := (← ppExpr body).pretty
    for f in fieldNames do
      let f := fieldIdent f
      prop := prop.replace s!"self.{f}" f
    return prop

/-- True iff the projection's result type is a proposition. -/
private def isProofField (typeName : Name) (fieldName : Name) : CommandElabM Bool :=
  withFieldResultType typeName fieldName isProp

/-- Generate `instance : Decodable T`. Data fields contribute their fixed byte
    size and are decoded from bytes; proof fields contribute no bytes and are
    checked with `Decodable.require` after the fields they mention have been
    decoded. -/
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
    if ← isProofField typeName fieldName then
      let prop ← fieldTypeTerm typeName fieldNames fieldName
      lets := lets.push
        s!"    let ⟨{field}⟩ ← LeanLoad.Parse.Decodable.require \"{typeName}.{field}\" ({prop})"
    else
      let fieldType ← fieldTypeTerm typeName fieldNames fieldName
      sizes := sizes.push s!"LeanLoad.Parse.Decodable.byteSize (α := {fieldType})"
      lets := lets.push s!"    let {field} : {fieldType} ← LeanLoad.Parse.Decodable.decode"
  let fields := String.intercalate ",\n" (fieldNames.toList.map (fun f => s!"      {fieldIdent f}"))
  let byteSize := if sizes.isEmpty then "0" else String.intercalate " + " sizes.toList
  let cmdString :=
    s!"instance : LeanLoad.Parse.Decodable {typeName} where\n" ++
    s!"  byteSize := {byteSize}\n" ++
    "  decode := do\n" ++
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
  registerDerivingHandler ``LeanLoad.Parse.Decodable handler

end LeanLoad.Parse.Decodable
