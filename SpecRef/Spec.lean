import Lean

/-!
# Spec

Definitions for declaring language specifications and sections within a specification.
-/

namespace SpecRef
open Lean

/-- A specification section.

    The `id` is a numeric section heading such as `9.7.9.6`.
    The `anchor` is the string used to represent the section in a url,
    for specifications whose links are not section numbers; it
    defaults to the `id`. -/
structure Section where
  id : String
  title : String := ""
  anchor : Option String := none
deriving Repr, BEq, Inhabited

/-- The information needed to reference a specification. -/
structure Spec where
  title : String
  version : String := ""
  /-- A template for the link to each section, in which `{id}` and `{anchor}` are
      replaced by those of the section. Leave it empty if there are no links. -/
  url : String := ""
  /-- Optionally, all of the sections in the specification. -/
  sections : Array Section := #[]
deriving Repr, BEq, Inhabited

/-- The listed section with the given `id`, if there is one. -/
def Spec.find? (s : Spec) (id : String) : Option Section :=
  s.sections.find? (·.id == id)

/-- Whether the section `id` can be referenced, returning true
    if no `sections` are provided or `sections` includes a section
    with the provided id. -/
def Spec.accepts (s : Spec) (id : String) : Bool :=
  s.sections.isEmpty || (s.find? id).isSome

/-- Encode a string so that it can be used as part of a url. -/
def encodeComponent (s : String) : String :=
  s.toUTF8.foldl (init := "") fun acc b =>
    let c := Char.ofNat b.toNat
    if b < 128 && (c.isAlphanum || "-._~".contains c) then acc.push c
    else
      let digits := (Nat.toDigits 16 b.toNat).map Char.toUpper
      acc ++ "%" ++ String.ofList (if digits.length == 1 then '0' :: digits else digits)

/-- Build a link to section `id` from the `url` template. The template is split
    on its placeholders before the values are inserted, so that an inserted value
    is never itself substituted. -/
def Spec.link (s : Spec) (id : String) : Option String :=
  if s.url.isEmpty then none else
  let anchor := ((s.find? id).bind (·.anchor)).getD id
  let pieces := (s.url.splitOn "{anchor}").map fun p =>
    String.intercalate (encodeComponent id) (p.splitOn "{id}")
  some (String.intercalate (encodeComponent anchor) pieces)

/-- The heading of a section as it appears in reports, such as `§2.1 add`, or
    just the number if the `Spec` does not list its sections. -/
def Spec.heading (s : Spec) (id : String) : String :=
  match s.find? id with
  | some x => if x.title.isEmpty then s!"§{id}" else s!"§{id} {x.title}"
  | none => s!"§{id}"

unsafe def evalSpecUnsafe (n : Name) : CoreM Spec := evalConst Spec n

/-- Evaluate the `Spec` definition with the given name. -/
@[implemented_by evalSpecUnsafe] opaque evalSpec (n : Name) : CoreM Spec

open Elab in
/-- Find the `Spec` definition named by an identifier and evaluate it. The
    definition must have type `Spec`, possibly through an `abbrev`, and must be
    computable. -/
def resolveSpec (id : Ident) : CoreM (Name × Spec) := do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let isSpec ← (do return (← Meta.whnfR (← getConstInfo n).type).isConstOf ``Spec : MetaM Bool).run'
  unless isSpec do throwErrorAt id "{.ofConstName n} is not a Spec"
  if isNoncomputable (← getEnv) n then
    throwErrorAt id "{.ofConstName n} is noncomputable, so it cannot be evaluated"
  try return (n, ← evalSpec n)
  catch e => throwErrorAt id "{.ofConstName n} could not be evaluated: {e.toMessageData}"

end SpecRef
