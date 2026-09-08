import SpecRef

/-!
# Citing the PTX ISA

To demonstrate how to use SpecRef, we take the NVIDIA PTX ISA as an example.
The specification itself is not important here; it is only an illustration.
-/

namespace SpecRef.Examples
open SpecRef

/-- Declare the PTX spec to be referenced. -/
def ptx : Spec := {
  title := "PTX ISA", version := "9.3"
  url := "https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#{anchor}"
  /- `sections` declares all of the sections in the specification, so that
     referencing a section that does not exist is an error. For the sake of this
     example, we will pretend that the PTX ISA only contains the sections
     referenced here. -/
  sections := #[
    { id := "5.1", title := "State Spaces", anchor := some "state-spaces" },
    { id := "5.1.1", title := "Register State Space", anchor := some "register-state-space" },
    { id := "9.7.9.6", title := "Data Movement and Conversion Instructions: shfl.sync",
      anchor := some "data-movement-and-conversion-instructions-shfl-sync" },
    { id := "9.7.14.1", title := "Parallel Synchronization and Communication Instructions: bar, barrier",
      anchor := some "parallel-synchronization-and-communication-instructions-bar" },
    { id := "10", title := "Special Registers", anchor := some "special-registers" }] }

inductive ShflMode where | idx | up | down | bfly

/-- The meaning of the following function isn't important. What is important is
    that hovering over the definition of `sourceLane` now provides links to the
    PTX specification. Try opening one of the links to see the relevant text in
    the specification highlighted. -/
@[spec ptx "9.7.9.6"
    quoting "shfl.sync exchanges register data between threads in membermask"
    because "the four modes select the source lane",
  spec ptx "9.7.9.6"
    quoting "results are undefined if a thread sources a register from an inactive thread"
    because "the source lane must be active"]
def sourceLane (mode : ShflMode) (lane delta width : Nat) : Nat :=
  match mode with
  | .idx => if delta < width then delta else lane
  | .up => if delta ≤ lane then lane - delta else lane
  | .down => if lane + delta < width then lane + delta else lane
  | .bfly => if lane ^^^ delta < width then lane ^^^ delta else lane

/-- Hovering over usages of `sourceLane` will also display references to the specification. -/
def sourceLaneUsage := sourceLane

/- List specification sections referenced by a definition. -/
#spec_refs sourceLane
/- List the definitions that cite a particular section of the specification. -/
#spec_cited ptx "9.7.9.6"
/- Generate a markdown report showing the definitions relevant to each section
   and the uncited sections. -/
#spec_report ptx
/- Check that every section declared in the ptx spec has been referenced.
   This will fail in the following case. -/
-- #spec_check ptx
/- To allow unreferenced sections, add `allowing [<ids>]`. -/
#spec_check ptx allowing ["5.1", "5.1.1", "9.7.14.1", "10"]


end SpecRef.Examples
