# Contributing

Start with the [README](README.md), [design principles](DESIGN.md),
[walkthrough](OrgLibExamples/Walkthrough.lean), and [source map](docs/SOURCES.md).
The canonical interface is proposed for community discussion.

1. State the mathematical claim, source interpretation and comparison domain.
2. Reuse the smallest suitable layer; construct canonical data and prove a
   correspondence before adding source-specific conclusions.
3. Use descriptive mathematical names, with attribution in comments and docs.
4. Add an actual public theorem application and a meaningful example/boundary case.
5. Update source correspondence and claim pointers, then run:

```sh
python3 scripts/check.py
lake build
lake exe nk_demo
```

Python 3.11+ is needed only for source/archive tooling. `scripts/check.py --write-imports`
regenerates the three root imports. Keep examples/tests out of the library graph.
Accepted proofs have no placeholders, unsafe shortcuts or new project axioms;
build-time guards allow only `propext`, `Classical.choice`, and `Quot.sound`.

Record source interpretation, kernel checking, numerical comparisons, agent review
and human decisions separately. New foundational definitions need complementary
model/domain and Lean/library review plus a maintainer decision. [Current human
reviews are pending](docs/WORKFLOW.md).

Use `leanck` for focused diagnostics when useful. Normalization remains dry-run
only; no shared configuration or CI integration without separate authorization.

Original contributions use Apache-2.0. Identify third-party rights before packaging;
see [RIGHTS.md](docs/RIGHTS.md). Keep build caches, private history, original sources
and generated validation outputs out of public commits. The full R harness is
an [optional separate supplement](supplements/README.md).
