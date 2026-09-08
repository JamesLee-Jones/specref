import SpecRefTests.Toy

/-!
Tests for `SpecRef`, run by `lake test`. The specification and the definitions
that reference it are in `SpecRefTests/Toy.lean`, so everything checked here is
seen across files.
-/

open SpecRef

#guard (toy.find? "2.1").map (·.title) = some "add"
#guard toy.heading "2.1" = "§2.1 add"
#guard free.heading "E-17" = "§E-17"
#guard toy.link "2.1" = some "https://example.org/toy/instructions-add"
#guard toy.link "2.2" = some "https://example.org/toy/2.2"
#guard free.link "E-17" = some "https://example.org/errata#E-17"
#guard toy.accepts "9" = false
#guard free.accepts "anything" = true
/- Ids and anchors are encoded, and an inserted value is never substituted again. -/
#guard ({ title := "T", url := "https://x/{id}/{anchor}" } : Spec).link "a b" = some "https://x/a%20b/a%20b"
#guard ({ title := "T", url := "https://x/{anchor}", sections := #[{ id := "{anchor}", anchor := some "{id}" }] } : Spec).link "{anchor}"
  = some "https://x/%7Bid%7D"
/- Text fragments give `-`, `&` and `,` a meaning; non-ASCII is UTF-8 encoded. -/
#guard encodeFragment "out-of-range, a & b + c" = "out%2Dof%2Drange%2C%20a%20%26%20b%20%2B%20c"
#guard encodeFragment "naïve" = "na%C3%AFve"
/- Sections without a table of contents are ordered numerically. -/
#guard #["1.10", "2", "1.9", "10"].qsort sectionLt = #["1.9", "1.10", "2", "10"]

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let cs := citations env ``add
  unless cs.size == 3 do throwError "add should have 3 citations, has {cs.size}"
  let cited := ((citing env ``toy "2.1").map (·.decl)).qsort Name.lt
  unless cited == #[``add, ``add_comm', ``contextual] do throwError "§2.1 citations: {cited}"
  unless (citing env ``toy "1").size == 2 do throwError "§1 should be cited twice"
  unless (citing env ``toy "2.2").map (·.decl) == #[``later] do throwError "attribute command form"
  unless (uncitedSections env ``toy toy).map (·.id) == #["2"] do
    throwError "uncited: {(uncitedSections env ``toy toy).map (·.id)}"
  unless (citedSections env ``free) == #["E-17"] do throwError "free citations"
  unless (citations env ``contextual).map (·.link toy) ==
      #[some "https://example.org/toy/instructions-add#:~:text=instruction-,add"] do
    throwError "context prefix: {(citations env ``contextual).map (·.link toy)}"
  let quoted := (citations env ``add).filter (·.passage != "")
  unless quoted.map (·.link toy) == #[some "https://example.org/toy/instructions-add#:~:text=adds%20its%20operands"] do
    throwError "text fragment: {quoted.map (·.link toy)}"
  -- Docstrings: the citation follows the doc comment of a definition exactly.
  unless (← findDocString? env ``RegFile) ==
      some "A register file. \n\nSpec: [Toy Machine Manual §1 Registers](https://example.org/toy/registers) — the register file" do
    throwError "docstring of RegFile: {← findDocString? env ``RegFile}"
  unless (← findDocString? env ``add).any (·.startsWith "Spec: [Toy Machine Manual §2.1 add](") do
    throwError "docstring of add: {← findDocString? env ``add}"
  -- From an importing file a theorem's docstring has its citation too.
  unless (← findDocString? env ``add_comm') == some "Commutativity. \n\nSpec: [Toy Machine Manual §2.1 add](https://example.org/toy/instructions-add)" do
    throwError "docstring of add_comm': {← findDocString? env ``add_comm'}"
  let report := markdownReport env ``toy toy
  unless report.startsWith "# Toy Machine Manual 1.2\n" do throwError "report heading:\n{report}"
  unless (report.splitOn "## [§2.1 add](https://example.org/toy/instructions-add)").length == 2 do
    throwError "report link:\n{report}"
  unless (report.splitOn "- §2 Instructions").length == 2 do throwError "report uncited:\n{report}"
  logInfo "citations are recorded, queried and reported as documented"

#spec_refs add
#spec_cited toy "2.1"
#spec_report toy
#spec_check toy allowing ["2"]

/- In the file that proves it, a theorem's docstring does not carry the
   citation, whether the attribute is given with the theorem or afterwards,
   unless the theorem is elaborated synchronously (see the note in
   `SpecRef/Cite.lean`). This pins the behaviour so that a toolchain which
   changes it is noticed. -/
/-- Local theorem. -/
@[spec toy "2"]
theorem local_thm : add_comm' = add_comm' := rfl
/-- Cited afterwards. -/
theorem local_thm2 : add_comm' = add_comm' := rfl
attribute [spec toy "2"] local_thm2
set_option Elab.async false in
/-- Synchronous. -/
@[spec toy "2"]
theorem local_thm3 : add_comm' = add_comm' := rfl
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  unless (← findDocString? env ``local_thm) == some "Local theorem. " do
    throwError "theorem docstrings now carry citations in-file; update the note in Cite.lean: {← findDocString? env ``local_thm}"
  unless (← findDocString? env ``local_thm2) == some "Cited afterwards. " do
    throwError "attribute after a theorem now shows in-file; update the note in Cite.lean: {← findDocString? env ``local_thm2}"
  unless (← findDocString? env ``local_thm3).any (·.startsWith "Synchronous. \n\nSpec: ") do
    throwError "synchronous theorem lost its citation: {← findDocString? env ``local_thm3}"

-- Errors: an unknown spec, a constant that is not a Spec, a noncomputable Spec,
-- an unknown section, a duplicate, a local citation, a citation of an imported
-- definition, an incomplete check, an unknown allowed section.
noncomputable def ncSpec : Spec := toy
@[extern "no_such_symbol"] opaque extSpec : Spec
abbrev Alias := Spec
def aliasSpec : Alias := free
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let rejects (stx : TSyntax `command) (why : String) (expected : String) : CommandElabM Unit := do
    let before := (← get).messages
    let env ← getEnv
    elabCommand stx
    let errors := (← get).messages.toList.filter (·.severity == .error)
    let texts ← errors.mapM (·.data.toString)
    modify fun s => { s with messages := before }
    setEnv env
    if errors.isEmpty then throwError "accepted {why}"
    unless texts.any (·.startsWith expected) do throwError "wrong message for {why}: {texts}"
  rejects (← `(@[spec nope "1"] def bad1 := 1)) "an unknown spec" "Unknown constant"
  rejects (← `(@[spec add "1"] def bad0 := 1)) "a constant that is not a Spec" "add is not a Spec"
  rejects (← `(@[spec ncSpec "1"] def badNc := 1)) "a noncomputable Spec" "ncSpec is noncomputable"
  rejects (← `(@[spec extSpec "1"] def badExt := 1)) "an uncompilable Spec" "extSpec could not be evaluated: "
  rejects (← `(@[spec toy "9"] def bad2 := 1)) "an unknown section" "toy has no section '9'"
  rejects (← `(@[spec toy "1", spec toy "1"] def bad3 := 1)) "a duplicate citation" "duplicate"
  rejects (← `(attribute [local spec toy "1"] later)) "a local citation" "spec citations cannot be local"
  rejects (← `(attribute [spec toy "1"] add)) "citing an imported definition" "add is defined in another file"
  rejects (← `(#spec_check strict)) "uncited sections in a check" "strict: 1 section(s)"
  rejects (← `(#spec_check strict allowing ["9"])) "allowing an unknown section" "strict has no section '9' to allow"
  rejects (← `(#spec_cited toy "9")) "citing an unknown section" "toy has no section '9'"
  -- A rejected citation leaves nothing behind.
  unless (citing (← getEnv) ``toy "1").size == 2 do throwError "a rejected citation was recorded"
  -- A spec through an abbrev is accepted, and a spec without sections only warns.
  elabCommand (← `(@[spec aliasSpec "X"] def viaAlias := 1))
  unless (citing (← getEnv) ``aliasSpec "X").size == 1 do throwError "abbrev spec"
  let before := (← get).messages
  elabCommand (← `(#spec_check aliasSpec))
  unless (← get).messages.toList.any (·.severity == .warning) do throwError "no warning for a spec without sections"
  modify fun s => { s with messages := before }
  logInfo "bad citations are rejected"
