import SpecRef

/-!
A small made-up specification and some definitions that reference it. The
checks are in `SpecRefTests.lean`, which imports this file, so that what is seen
from another file is tested too.
-/

open SpecRef

def toy : Spec := {
  title := "Toy Machine Manual"
  version := "1.2"
  url := "https://example.org/toy/{anchor}"
  sections := #[
    { id := "1", title := "Registers", anchor := some "registers" },
    { id := "2", title := "Instructions" },
    { id := "2.1", title := "add", anchor := some "instructions-add" },
    { id := "2.2", title := "bar" }] }

/-- A spec whose only section is never referenced. -/
def strict : Spec := { title := "Strict", sections := #[{ id := "1" }] }

/-- A spec with no table of contents accepts any section. -/
def free : Spec := { title := "Errata", url := "https://example.org/errata#{id}" }

/-- A register file. -/
@[spec toy "1" because "the register file"]
def RegFile := String → Option Int

@[spec toy "2.1" quoting "adds its operands" because "the add instruction", spec toy "1", spec free "E-17"]
def add (r : RegFile) (a b : String) : Option Int := do return (← r a) + (← r b)

/-- Commutativity. -/
@[spec toy "2.1"]
theorem add_comm' (r : RegFile) (a b : String) : add r a b = add r b a := by
  unfold add; cases r a <;> cases r b <;> simp [Int.add_comm]

def later := 3
attribute [spec toy "2.2" because "cited after the definition"] later

/-- `add` occurs twice on the page; the context says which occurrence. -/
@[spec toy "2.1" quoting "add" after "instruction"]
def contextual := 4
