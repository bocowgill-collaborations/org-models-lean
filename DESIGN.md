# Design principles

This prototype adapts the inspected MathEconLib P1–P8 and M1–M5 guidance;
its pinned source identities are in [SOURCE_CORRESPONDENCE.json](docs/SOURCE_CORRESPONDENCE.json).
It depends on mathlib directly and does not require another model library.

* Keep constitutive data small: topology, tables, bounds and laws are separate.
* Prove at the useful shared level, then construct applications explicitly.
* Compose existing mathematical primitives: embeddings, finite sums, `IsMaxOn`,
  finite products and measures.
* Use data structures for data and propositions for assumptions/properties.
* Prove representation changes: encoding, inverse table interpretation, slot
  reindexing and rational-to-real evaluation.
* State validity where it matters: `K < N`, ordered scopes and required arithmetic
  or measurability assumptions.
* Offer an usable public API and test representative/boundary instances.
* Separate model families from instances, make the scientific framework explicit,
  and distinguish optimality from selection or search algorithms.

Core mathematics lives in `OrgLib/NK`; examples/tests depend on it, never the
reverse. `Indexed` constructs canonical data from ordered nonfocal neighbors.
`SharedCyclic` studies a shared-table restriction of cyclic NK. The deterministic
locus-specific alternative asserts no stochastic independence by itself.

Comparison claims preserve configuration labels and topology. Adapters prove
source-shaped specifications equal canonical fitness; finite R comparisons are
separate evidence. Full organizational behavior remains outside this prototype.

Names describe mathematical content. Source authors/titles belong in documentation,
comments and provenance. Changes to foundational meanings/hypotheses require a
recorded design decision and complementary human review; see [WORKFLOW.md](docs/WORKFLOW.md).
