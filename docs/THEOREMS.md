# Theorem coverage

This table maps the fifteen original mathematical targets to their current,
author-neutral interface. `import OrgLib` exposes the library; examples and tests
are separate clients. The source basis and exact R-to-Lean operation map are in
[SOURCES.md](SOURCES.md) and [SOURCE_CORRESPONDENCE.json](SOURCE_CORRESPONDENCE.json).
Current compile/audit evidence is recorded in [CHECKS.json](CHECKS.json), tied to
the actual source fingerprint. Human semantic and library release reviews remain
pending; they are not implied by a successful build.

All landscape topologies supply `K<N`. Ordered results use
`[Field R] [LinearOrder R] [IsStrictOrderedRing R]`; exact mean identities use
`[Field R] [CharZero R]`. Local word extraction needs no arithmetic assumptions.
Bounds are hypotheses only where the result needs them.

| Target | Public declarations and exact scope |
|---|---|
| T01: Locality | `contribution_eq_of_agree_on_scope` in [Basic.lean](../OrgLib/NK/Basic.lean): agreeing on a locus's allowed inputs gives the same local contribution, for any coefficient type. |
| T02: Bounds | `fitness_mem_Icc` in [Properties.lean](../OrgLib/NK/Properties.lean): tables in `[0,1]` give fitness in `[0,1]`. |
| T03: Separable evaluation | `fitness_K_zero` in [Basic.lean](../OrgLib/NK/Basic.lean): at K=0 each contribution reads only its focal bit. |
| T04: Local/global maxima | `isOneBitLocalMax_iff_isMaxOn_K_zero` in [Properties.lean](../OrgLib/NK/Properties.lean): weak one-bit maximality equals global maximality at K=0, with arbitrary table values and ties. No search convergence follows. |
| T05: Representation transport | `fitness_reindex_slots`, `Topology.reindex_refl`, `Topology.reindex_reindex`, `reindexTables_refl`, `reindexTables_reindex` in [Basic.lean](../OrgLib/NK/Basic.lean): slot permutations fix zero, with inverse table reindexing. No preservation of the shared-table restriction is claimed. |
| T06: Ordered indexed application | Codec inverses and lookup identities in [Encoding.lean](../OrgLib/NK/Encoding.lean); `Topology.ofNeighbors`, `fitness_eq_indexedAverage`, `indexed_fitness_mem_Icc`, and `indexed_isOneBitLocalMax_iff_isMaxOn_K_zero` in [Indexed.lean](../OrgLib/NK/Indexed.lean). Valid supplied neighbor order and raw quality are preserved. |
| T07: Shared cyclic specialization | `sharedCyclic_fitness_eq`, `sharedCyclic_entries_fitness_eq`, `locusSpecificCyclic_sharedTables` in [SharedCyclic/Basic.lean](../OrgLib/NK/SharedCyclic/Basic.lean). Both deterministic families reuse canonical fitness; arbitrary locus tables include the shared case. |
| T08: Extra symmetry | `sharedCyclic_fitness_rotate` in [SharedCyclic/Basic.lean](../OrgLib/NK/SharedCyclic/Basic.lean), reusing `fitness_shared_rotate`: every rotation preserves shared cyclic fitness for every valid N,K. |
| T09: Hamming reduction | `sharedCyclic_K_zero_hamming` in [SharedCyclic/Properties.lean](../OrgLib/NK/SharedCyclic/Properties.lean): at K=0 quality depends only on the count of true bits. Natural subtraction and casts are explicit. |
| T10: Shared K=0 maxima | `sharedCyclic_isMaxOn_iff_all_true`, `sharedCyclic_isMaxOn_iff_all_false`, `sharedCyclic_isMaxOn_of_eq` in [SharedCyclic/Properties.lean](../OrgLib/NK/SharedCyclic/Properties.lean): strict true/false preference or ties characterize raw-quality maxima. |
| T11: Strict restriction | `witnessTables_bounded`, `witness_fitness_state01`, `witness_fitness_state10`, `witness_no_shared_representation` in [Separation.lean](../OrgLib/NK/SharedCyclic/Separation.lean): a bounded rational N=2,K=0 landscape has values 1 and 0 at `01` and `10`, while any shared rational table gives equal values there. |
| T12: Exact cast | `contribution_ratCast`, `fitness_ratCast` in [Cast.lean](../OrgLib/NK/Cast.lean): casting arbitrary rational tables to real tables commutes with evaluation; no bounds are needed. |
| T13: Continuous laws | Measurable realization maps, probability instances and mass-one identities in [Ensembles.lean](../OrgLib/NK/Ensembles.lean). Products specify the complete idealized joint laws at fixed topology. |
| T14: Law separation at N=2 | `shared_event_state01_state10`, `independent_event_state01_state10`, `shared_independent_laws_ne` in [EnsembleSeparation.lean](../OrgLib/NK/SharedCyclic/EnsembleSeparation.lean): a measurable evaluated-landscape event has shared mass zero and independent mass at least `1/16` at N=2,K=0. |
| T15: Law separation at N=12 | `shared_event_zero_N12`, `independent_event_lower_bound_N12`, `landscape_laws_ne_N12` in [SizeTwelve.lean](../OrgLib/NK/SharedCyclic/SizeTwelve.lean): alternating labeled states separate the laws for every K<12, with independent event mass at least `2^-24`. |

## Concrete checks and probability argument

[ThreeComponent.lean](../OrgLibExamples/ThreeComponent.lean) preserves the printed
three-component example's local coordinate order and rational table values.
`expected_code_0` through `expected_code_7` are kernel proofs for all eight states;
the displayed `001` value is exactly `1/2`. This instance has bibliographic
attribution in its documentation rather than an author-named Lean object.

[Walkthrough.lean](../OrgLibExamples/Walkthrough.lean) applies the definitions and
headline results in one reading path. Public API tests apply generic results under
their stated hypotheses; axiom guards reject unexpected dependencies. The allowed
foundations are `propext`, `Classical.choice`, and `Quot.sound`. Printed dependency
reports supplement the rejecting guards. Actual audit counts belong to CHECKS,
rather than being copied from an earlier differently named snapshot.

For the continuous-law result, let `E(x,y)={F | 1/2<F(x) ∧ F(y)≤1/2}`.
Shared rotation symmetry makes E impossible when y is the specified rotation of x.
The independent law reaches E through a sufficient selected-entry rectangle.
[EnsembleRectangles.lean](../OrgLib/NK/EnsembleRectangles.lean) proves exact half
masses and rectangle mass `(1/4)^N` when the two selected local words differ at
each locus. The generic event theorem explicitly assumes this distinctness.
The N=2 and N=12 applications discharge it at their fixed labeled states.

The rectangle masses are exact; `1/16` and `2^-24` are **lower bounds** on the
larger observable event, not exact event probabilities. These are actual continuous
Lebesgue/product calculations, not finite sampling or Bernoulli approximations.

## Interpretation limits

The chapter's landscape **does instantiate deterministic NK**. The bounded witness
proves that the shared family excludes some locus-specific landscapes at fixed
labels. It does not rule out equivalence after arbitrary state recodings. The law
theorems compare evaluated fitness functions at the same cyclic topology; they
do not compare the article's original random-topology generator to the chapter.

The explicit locus-specific cyclic alternative retains topology, labels and
averaging. Its constructor alone asserts neither unequal tables nor independence;
the independent product law supplies the latter assumption separately.

R fixed-input comparisons in the separate supplement support translation fidelity.
They are not the universal cast theorem, not proof of R PRNG behavior, and not an
assessment of changes to organizational outcomes. Political utility, participation,
voting, agendas, trajectories and substantive impact remain outside this scope.
