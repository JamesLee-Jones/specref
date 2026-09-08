import SpecRef.Spec

/-!
# Citations

The `spec` attribute associates a definition with a section of a specification.
A citation is written as
`spec <spec-def> "<section>" [quoting "<passage>" [after "<preceding text>"]] [because "<reason>"]`,
where `<spec-def>` is a defined `Spec` and `<section>` is the section referenced.
`quoting` allows the reference to provide a verbatim quote from the
specification, `after` says what text immediately precedes the quote when the
same words occur more than once on the page, and `because` gives a reason for
the reference. The attribute can be repeated, so a definition can reference
several sections of several specifications:

```lean
@[spec ptx "9.7.9.6" quoting "otherwise, the thread will simply copy its own input a to destination d",
  spec ptx "5.1.1" because "registers are private to a thread"]
def sourceLane ...
```

Each citation is added to the docstring of the definition as a link, so that
hovering over the definition shows the references and opens the relevant
section of the specification. If a passage was quoted, the link opens the
specification with the quoted text highlighted. Browsers look for the quoted
text from the top of the page and only fall back to the section anchor if it
is not found, so a quote that also occurs earlier on the page highlights the
earlier occurrence; choose a sentence unique to the section, or give the words
that precede it with `after`. Citations are also stored in the environment, so
that the definitions referencing a section can be found from any file that
imports them.

One limitation: with asynchronous elaboration, which is the default, a
`theorem` is elaborated on a separate branch of the environment, and its
docstring is looked up there when hovering over it in the file that proves it.
The link this attribute adds lives on the main branch, so it is not shown
there, even when the attribute is given afterwards with `attribute [spec ...]`.
It is shown from any file that imports the theorem, and in the same file if the
theorem is elaborated with `set_option Elab.async false in`. The citation
itself is recorded either way.
-/

namespace SpecRef
open Lean

/-- A reference from a definition to a section of a specification. -/
structure Citation where
  decl : Name
  /-- The name of the `Spec` definition. -/
  spec : Name
  sectionId : String
  /-- The text quoted from the specification, if any. -/
  passage : String := ""
  /-- The text immediately preceding the quoted passage, if given. -/
  context : String := ""
  /-- The reason given for the reference, if any. -/
  reason : String := ""
deriving Repr, BEq, Inhabited

/-- Encode a quoted passage so that it can be used in a url for highlighting
    text on a page. Text fragments give `-`, `&` and `,` a meaning, so those
    are encoded as well. -/
def encodeFragment (s : String) : String :=
  s.toUTF8.foldl (init := "") fun acc b =>
    let c := Char.ofNat b.toNat
    if b < 128 && (c.isAlphanum || "._~".contains c) then acc.push c
    else
      let digits := (Nat.toDigits 16 b.toNat).map Char.toUpper
      acc ++ "%" ++ String.ofList (if digits.length == 1 then '0' :: digits else digits)

/-- The link for a citation. This is the link to the section, and if a passage
    was quoted, a text fragment (`:~:text=...`) is added so that the page opens
    with the quoted text highlighted. The text is matched from the top of the
    page, so a `context` prefix is included when one was given (`prefix-,text`).
    The section anchor is kept as the fallback for when the text is not found. -/
def Citation.link (spec : Spec) (c : Citation) : Option String := do
  let url ← spec.link c.sectionId
  if c.passage.isEmpty then return url
  let before := if c.context.isEmpty then "" else encodeFragment c.context ++ "-,"
  return url ++ (if url.contains '#' then ":~:text=" else "#:~:text=") ++ before ++ encodeFragment c.passage

/-- The quoted passage and the reason, formatted for a docstring or report. -/
def Citation.annotation (c : Citation) : String :=
  (if c.passage.isEmpty then "" else s!" “{c.passage}”") ++
    (if c.reason.isEmpty then "" else s!" — {c.reason}")

/-- A citation as a line of Markdown, for docstrings and reports. -/
def Citation.markdown (spec : Spec) (c : Citation) : String :=
  let heading := s!"{spec.title} {spec.heading c.sectionId}"
  let target := match c.link spec with | some url => s!"[{heading}]({url})" | none => heading
  target ++ c.annotation

/-- Every citation in the environment, stored by the definition that made it. -/
initialize citeExt : SimplePersistentEnvExtension Citation (NameMap (Array Citation)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m c => m.insert c.decl ((m.getD c.decl #[]).push c)
    addImportedFn := fun arrays => arrays.foldl (fun m a => a.foldl
      (fun m c => m.insert c.decl ((m.getD c.decl #[]).push c)) m) {} }

/-- The citations made by a definition. -/
def citations (env : Environment) (decl : Name) : Array Citation :=
  (citeExt.getState env).getD decl #[]

/-- Every citation in the environment. -/
def allCitations (env : Environment) : Array Citation :=
  (citeExt.getState env).foldl (fun acc _ cs => acc ++ cs) #[]

/-- The citations of a particular section of a specification. -/
def citing (env : Environment) (spec : Name) (sectionId : String) : Array Citation :=
  (allCitations env).filter fun c => c.spec == spec && c.sectionId == sectionId

/-- The sections of a specification that are referenced at least once. -/
def citedSections (env : Environment) (spec : Name) : Array String :=
  ((allCitations env).filterMap fun c => if c.spec == spec then some c.sectionId else none)
    |>.toList.eraseDups.toArray

/-- The sections listed by a `Spec` that are not referenced by any definition. -/
def uncitedSections (env : Environment) (name : Name) (spec : Spec) : Array Section :=
  let cited := citedSections env name
  spec.sections.filter fun s => !cited.contains s.id

syntax (name := specAttr) &"spec" ppSpace ident ppSpace str
  (ppSpace &"quoting" ppSpace str (ppSpace &"after" ppSpace str)?)? (ppSpace &"because" ppSpace str)? : attr

initialize registerBuiltinAttribute {
  name := `specAttr
  descr := "associates a definition with a section of a specification; can be repeated"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    let `(attr| spec $specId:ident $sec:str $[quoting $passage:str $[after $context:str]?]? $[because $reason:str]?) := stx
      | throwError "expected `spec <spec-def> \"<section>\" [quoting \"<passage>\" [after \"<text>\"]] [because \"<reason>\"]`"
    unless kind == .global do throwErrorAt stx "spec citations cannot be local or scoped"
    let env ← getEnv
    unless (env.getModuleIdxFor? decl).isNone do
      throwErrorAt stx "{.ofConstName decl} is defined in another file, so it cannot be cited here"
    let (name, spec) ← resolveSpec specId
    unless spec.accepts sec.getString do
      throwErrorAt sec "{.ofConstName name} has no section '{sec.getString}'"
    let passage := (passage.map (·.getString)).getD ""
    let context := ((context.bind id).map (·.getString)).getD ""
    let reason := (reason.map (·.getString)).getD ""
    let c : Citation := { decl, spec := name, sectionId := sec.getString, passage, context, reason }
    if (citations env decl).contains c then throwErrorAt stx "duplicate citation"
    let doc := ((← findDocString? env decl).map (· ++ "\n\n")).getD ""
    addDocStringCore decl (doc ++ "Spec: " ++ c.markdown spec)
    modifyEnv (citeExt.addEntry · c)
}

end SpecRef
