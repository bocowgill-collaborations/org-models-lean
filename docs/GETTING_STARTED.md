# Build and inspect the prototype

Lean checks mathematical proofs; Lake builds projects; elan installs the Lean
version requested by a project. No prior Lean knowledge is needed to run these checks.

## Install

Follow the [official Lean setup guide](https://lean-lang.org/install/), which walks
through VS Code, its Lean extension and tool installation. Install Git if needed.
On Windows, use the terminal/environment selected by the guide. A native demo build
also needs ordinary platform build tools: Xcode Command Line Tools on macOS or
the platform's C build toolchain.

Open a new terminal and check `git --version`, `elan --version`, and `lake --version`.
If a command is missing, restart the terminal and finish the setup guide's PATH step.

## Obtain and verify

```sh
git clone https://github.com/bocowgill-collaborations/org-models-lean.git
cd org-models-lean
lake exe cache get
lake build
lake exe nk_demo
```

For a source archive, extract it and start at the cache command inside its directory.
Keep `lean-toolchain` and `lake-manifest.json` unchanged. They pin Lean `v4.28.0`
and all nine dependency revisions, including mathlib
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The first downloads require network
access and can take time. The dependency cache does not replace checking this project.
Do not run bare `lake update` for reproduction: it can upgrade transitive dependencies.

A successful build ends with `Build completed successfully`. It compiles the core,
all retained theorem applications, example anchors, and axiom guards. `#print axioms`
messages are informational; guards allow only `propext`, `Classical.choice` and
`Quot.sound`. The normal build/demo need neither R nor Python. Python 3.11+ is only
needed for supplementary source/archive checks and the optional validation harness.

Expected demo output:

```text
Three-component NK example (001): 1/2
Ordered-neighbor NK example: 13/63
Shared cyclic example: 5/27
Locus-specific witness (01): 1
Locus-specific witness (10): 0
Checked proofs: canonical reuse, rotation symmetry, and landscape-law separation.
Scope: quality landscapes at fixed labels; organizational dynamics are separate.
```

The witness has different values at rotated states. Shared cyclic landscapes force
those values equal, excluding this witness at the same labels. Unequal continuous
landscape laws require a separate probability proof. Read
[Walkthrough.lean](../OrgLibExamples/Walkthrough.lean) and the [theorem guide](THEOREMS.md).

## More checks and troubleshooting

`python3 scripts/check.py` checks naming, root imports, source correspondence and
local links; Lean checks proofs. [CHECKS.json](CHECKS.json) describes the exact tested
snapshot and whether dependencies came from an existing cache or a network install.

For download failures, resolve network/proxy access and retry the cache command.
For native linking failures, install the platform build tools and retry. To rebuild
only this package while retaining dependencies, run `lake clean orglib` then
`lake build`. Rerun the build after edits; a partially successful build is not a pass.

The [external client](../examples/external-client/README.md) constructs its own data.
The [separate supplement](../supplements/README.md) compares the original R evaluators
when supplied matching source files.
