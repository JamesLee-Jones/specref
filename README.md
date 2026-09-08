# SpecRef

A library for maintaining an association between Lean definitions and specification documents.

## Using SpecRef

### Add SpecRef to a project

Add the following to the `lakefile.toml` of your project:

```toml
[[require]]
name = "specref"
git = "https://github.com/JamesLee-Jones/specref"
rev = "v0.1.0"
```

Then run `lake update specref` and `import SpecRef` where it is needed.
Your project must use the Lean toolchain named in this repository's `lean-toolchain`.

### Declare a specification

In order to associate Lean definitions with a specification, it is necessary to first provide information about the specification to be referenced.
`SpecRef` allows you to do this in the following way:

```lean
import SpecRef
open SpecRef

def ptx : Spec := {
  title := "PTX ISA", version := "9.3"
  url := "https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#{anchor}" }
```

The `url` field is a template that specifies how the link to each section depends on the `{id}` and `{anchor}` of that section.
The `id` of a section is its numeric heading, such as `9.7.3.0`, its `title` is shown in reports, and an `anchor` optionally specifies the string used to represent a section in the url.

It is possible to specify completely, all of the `Section`s that are present in the specification.
If provided, any references to non-existent sections will lead to an error.
This can also be used to check which specification sections are not referenced.

### Citing a specification

`SpecRef` defines a `spec` attribute to associate a definition with a section of a language specification.

A citation is written as `spec <spec-def> "<section>" [quoting "<passage>" [after "<text>"]] [because "<reason>"]`, where `<spec-def>` is the defined `Spec`, `<section>` is the section of the language specification referenced.
`quoting` allows the reference to provide a verbatim quote from the language specification; we will see why this is useful shortly.
`after` gives the text that immediately precedes the quote, for when the same words occur more than once on the page.
`because` allows a reason for the reference to be given.

For the `ptx` spec defined above, `spec` can be used as follows:

```lean
@[spec ptx "9.7.9.6"
    quoting "shfl.sync exchanges register data between threads in membermask"
    because "the four modes select the source lane",
  spec ptx "5.1.1"]
def sourceLane ...
```

This includes a link to the relevant section of the referenced specification, and will highlight the quoted text if provided.
Browsers look for the quoted text from the top of the page, so choose a sentence unique to the section, or say what precedes it with `after`.
For a theorem, the link is shown from files that import it but not, with Lean's default asynchronous elaboration, in the file that proves it.

### Ask

`SpecRef` includes a number of utility functions for getting and checking information about spec references:

```lean
#spec_refs sourceLane                 -- what sourceLane cites
#spec_cited ptx "9.7.9.6"             -- every declaration citing the section
#spec_report ptx                      -- Markdown, grouped by section, then the uncited sections
#spec_check ptx allowing ["1", "2"]   -- error unless every enumerated section is cited
```

The full example can be found at `SpecRefExamples/PtxIsa.lean`.
