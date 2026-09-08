import SpecRef.Cite

/-!
# Queries and reports

`SpecRef` includes a number of commands for getting and checking information
about spec references:

- `#spec_refs sourceLane` lists the sections referenced by a definition.
- `#spec_cited ptx "9.7.9.6"` lists the definitions that reference a section.
- `#spec_report ptx` generates a Markdown report showing the definitions
  relevant to each section, followed by the sections that are not referenced.
- `#spec_check ptx` checks that every section listed by the `Spec` has been
  referenced, and fails otherwise. To allow some sections to go unreferenced,
  add `allowing ["<id>", ...]`; allowing a section that does not exist is an
  error.

The same information is available to programs through `citations`, `citing`,
`uncitedSections` and `markdownReport`.
-/

namespace SpecRef
open Lean Elab Command

/-- A citation as plain text, for messages. Messages do not render Markdown, so
    the heading, quoted text and reason are given on one line with the url
    below. -/
def Citation.describe (spec : Spec) (c : Citation) : String :=
  let url := match c.link spec with | some u => s!"\n    {u}" | none => ""
  s!"{spec.title} {spec.heading c.sectionId}{c.annotation}{url}"

/-- Order section ids by their numeric parts, so that `1.9` comes before `1.10`. -/
def sectionLt (a b : String) : Bool :=
  let parts (s : String) : List (Nat × String) := (s.splitOn ".").map fun p => (p.toNat?.getD 0, p)
  let rec lt : List (Nat × String) → List (Nat × String) → Bool
    | [], [] => false
    | [], _ => true
    | _, [] => false
    | x :: xs, y :: ys => if x.1 != y.1 then x.1 < y.1 else if x.2 != y.2 then x.2 < y.2 else lt xs ys
  lt (parts a) (parts b)

/-- A Markdown report for a specification: a heading for each referenced section
    with its citations, in the order of the `Spec` if it lists its sections,
    followed by the sections that are not referenced. -/
def markdownReport (env : Environment) (name : Name) (spec : Spec) : String := Id.run do
  let cited := citedSections env name
  let ordered := if spec.sections.isEmpty then cited.qsort sectionLt else
    (spec.sections.filterMap fun s => if cited.contains s.id then some s.id else none) ++
      (cited.filter fun id => (spec.find? id).isNone)
  let mut out := #[s!"# {spec.title} {spec.version}".trimAscii.toString, ""]
  for id in ordered do
    let heading := spec.heading id
    out := out.push (match spec.link id with
      | some url => s!"## [{heading}]({url})"
      | none => s!"## {heading}")
    out := out.push ""
    for c in citing env name id do
      out := out.push s!"- `{c.decl}`{c.annotation}"
    out := out.push ""
  let uncited := uncitedSections env name spec
  unless uncited.isEmpty do
    out := out.push "## Not cited" |>.push ""
    for s in uncited do out := out.push s!"- §{s.id} {s.title}".trimAscii.toString
    out := out.push ""
  return String.intercalate "\n" out.toList

elab "#spec_refs " id:ident : command => do
  let env ← getEnv
  let decl ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
  let cs := citations env decl
  if cs.isEmpty then
    logInfo m!"{decl} cites nothing"
  else
    let lines ← cs.toList.mapM fun c => do return c.describe (← liftCoreM (evalSpec c.spec))
    logInfo m!"{.ofConstName decl} cites:\n{String.intercalate "\n" lines}\n(hover over {.ofConstName decl} for these as links; for a theorem, from a file that imports it)"

elab "#spec_cited " spec:ident sec:str : command => do
  let env ← getEnv
  let (name, s) ← liftCoreM (resolveSpec spec)
  unless s.accepts sec.getString do throwErrorAt sec "{.ofConstName name} has no section '{sec.getString}'"
  let cs := citing env name sec.getString
  let heading := m!"{.ofConstName name} {s.heading sec.getString}"
  if cs.isEmpty then logInfo m!"nothing cites {heading}"
  else logInfo m!"{heading} is cited by:\n{String.intercalate "\n" (cs.toList.map fun c =>
    if c.reason.isEmpty then s!"{c.decl}" else s!"{c.decl}: {c.reason}")}"

elab "#spec_report " spec:ident : command => do
  let env ← getEnv
  let (name, s) ← liftCoreM (resolveSpec spec)
  logInfo (markdownReport env name s)

unsafe def evalStringsUnsafe (t : Term) : TermElabM (List String) :=
  Term.evalTerm (List String) (toTypeExpr (List String)) t

/-- Evaluate a term of type `List String`, such as the sections given to `allowing`. -/
@[implemented_by evalStringsUnsafe] opaque evalStrings (t : Term) : TermElabM (List String)

syntax (name := specCheck) "#spec_check " ident (ppSpace &"allowing" ppSpace term)? : command

/-- Check that every section listed by a `Spec` is referenced, other than those
    that have been explicitly allowed. -/
def runSpecCheck (spec : Ident) (exempt : Option Term) : CommandElabM Unit := do
  let env ← getEnv
  let (name, s) ← liftCoreM (resolveSpec spec)
  let exempt : List String ← match exempt with
    | some t => liftTermElabM (evalStrings t)
    | none => pure []
  for id in exempt do
    unless s.accepts id do throwError "{.ofConstName name} has no section '{id}' to allow"
  let missing := (uncitedSections env name s).filter fun x => !exempt.contains x.id
  if s.sections.isEmpty then logWarning m!"{.ofConstName name} does not list its sections, so there is nothing to check"
  unless missing.isEmpty do
    throwError "{.ofConstName name}: {missing.size} section(s) are not cited:\n{String.intercalate "\n" (missing.toList.map fun x => s!"§{x.id} {x.title}".trimAscii.toString)}"

elab_rules : command
  | `(#spec_check $spec:ident) => runSpecCheck spec none
  | `(#spec_check $spec:ident allowing $t:term) => runSpecCheck spec (some t)

end SpecRef
