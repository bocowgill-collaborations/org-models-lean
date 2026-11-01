import OrgLibExamples.Walkthrough

/-!
# Short newcomer demonstration

The executable displays exact rational examples. Building the library and its tests
checks the universal proofs; printing particular numbers is a separate operation.
-/

def main : IO Unit := do
  let labels := ["Three-component NK example (001)", "Ordered-neighbor NK example",
    "Shared cyclic example", "Locus-specific witness (01)", "Locus-specific witness (10)"]
  for (label, value) in labels.zip OrgLibExamples.Walkthrough.values do
    IO.println s!"{label}: {value}"
  IO.println "Checked proofs: canonical reuse, rotation symmetry, and landscape-law separation."
  IO.println "Scope: quality landscapes at fixed labels; organizational dynamics are separate."
