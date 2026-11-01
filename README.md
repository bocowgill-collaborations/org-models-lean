# Organizational Models in Lean

A proof of concept for a community-developed library that specifies organizational
models, proves their properties, and makes their relationships explicit—in the
spirit of mathlib, cslib, physicslib, and MathEconLib.

The prototype studies **NK quality landscapes**. Its canonical representation is
a proposal following [Felipe A. Csaszar's exposition of NK](https://doi.org/10.1186/s41469-018-0039-0).
The two applications use extensions of the NK models
[Sources and exact correspondence](https://github.com/bocowgill-collaborations/org-models-lean/blob/main/docs/SOURCES.md).

## Three demonstrations

| Demonstration | Checked definitions and proofs |
|---|---|
| **1. A proposed canonical NK representation.** Each component reads itself and K neighbors; a table gives its contribution; fitness is the mean. Bounds and sampling laws are separate. | [`Topology`](OrgLib/NK/Basic.lean#L34), [`fitness`](OrgLib/NK/Basic.lean#L57), and reusable [bounds and K=0 maximality](OrgLib/NK/Properties.lean). |
| **2. Direct inheritance.** The quality landscape in *Conflict, Chaos, and the Art of Institutional Design* constructs canonical NK data. Its exact indexed evaluator equals canonical fitness and inherits canonical theorems. | [`Topology.ofNeighbors`](OrgLib/NK/Indexed.lean#L25), [`fitness_eq_indexedAverage`](OrgLib/NK/Indexed.lean#L58), and [`indexed_fitness_mem_Icc`](OrgLib/NK/Indexed.lean#L66). |
| **3. Inheritance with an extra restriction and a different law.** The landscape in *Adaptive Rationality, Garbage Cans, and the Policy Process* is also deterministic NK. Sharing a table around a cycle forces rotation symmetry, excludes some canonical landscapes at fixed labels, and gives a different continuous law from independent tables at the same cyclic topology. | [`sharedCyclic`](OrgLib/NK/SharedCyclic/Basic.lean#L28), [rotation symmetry](OrgLib/NK/SharedCyclic/Basic.lean#L65), [nonrepresentation witness](OrgLib/NK/SharedCyclic/Separation.lean#L63), and [law separation at N=12](OrgLib/NK/SharedCyclic/SizeTwelve.lean#L57). |

[Walkthrough.lean](OrgLibExamples/Walkthrough.lean) applies these results together.
[ThreeComponent.lean](OrgLibExamples/ThreeComponent.lean) proves all eight values
of the small printed NK example. Names describe mathematical objects; source
attribution belongs in documentation and comments.

## Start from zero

Install Git and Lean using the [official setup guide](https://lean-lang.org/install/).
It installs the `elan` version manager and `lake` build command. Then run:

```sh
git clone https://github.com/bocowgill-collaborations/org-models-lean.git
cd org-models-lean
lake exe cache get
lake build
lake exe nk_demo
```

The first run downloads the pinned toolchain and mathlib dependencies. A successful
build ends with `Build completed successfully`: it checks the library, theorem
applications, example equalities and axiom guards. The labelled demo displays exact
values `1/2`, `13/63`, `5/27`, `1`, `0`; the last two exhibit the separating witness.
Printing examples illustrates the results; the build checks their general proofs.

No R or original paper files are needed. Lean `v4.28.0` and dependency revisions
are pinned. [Full newcomer instructions](docs/GETTING_STARTED.md) include expected
output and troubleshooting. To use the API:

```lean
import OrgLib
open OrgLib.NK
```

See the [external client](examples/external-client/README.md) and
[theorem guide](docs/THEOREMS.md). Optional source/link checks use Python 3.11+:
`python3 scripts/check.py`.

## Evidence and limits

The proofs concern raw quality, not the papers' full organizational dynamics.
Comparisons preserve labels and fix topology. Probability bounds are lower bounds,
not exact event probabilities or estimates of organizational outcomes. Sources
identify supplied proof versions; no error in an uninspected final publication
is asserted. The canonical interface is a proposal for community discussion.

The separate [R validation supplement](supplements/README.md) compares fixed inputs
with isolated original evaluators; it does not run the full simulations.
[Current checks](docs/CHECKS.json) · [AI workflow and pending human reviews](docs/WORKFLOW.md).

Original software/documentation use [Apache-2.0](LICENSE).
[Contributing](CONTRIBUTING.md) · [Design](DESIGN.md) · [Rights](docs/RIGHTS.md).
