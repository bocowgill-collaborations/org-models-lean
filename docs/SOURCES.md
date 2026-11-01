# Sources and translation correspondence

The canonical core is a **proposed representation of NK landscapes** following
Felipe A. Csaszar's exposition. It does not attribute ownership of NK to that paper.
The two applications formalize raw quality landscapes, rather than the complete
organizational models in their sources. Author and paper attribution is documentary;
the Lean definitions have descriptive mathematical names.

## Identified source versions

| Source | Role and inspected version |
|---|---|
| Felipe A. Csaszar, *A note on how NK landscapes work* (2018), [DOI](https://doi.org/10.1186/s41469-018-0039-0) | Supplied six-page PDF; pp.2–3 guide the core, and p.3 supplies the three-component example. |
| Scott C. Ganz, *Conflict, Chaos, and the Art of Institutional Design*, [DOI](https://doi.org/10.1287/orsc.2023.1662) | Supplied `ORSC20231662_AU.pdf`, an author proof with queries. Quality landscape: §3.1, PDF/printed p.8. |
| Scott C. Ganz, *Adaptive Rationality, Garbage Cans, and the Policy Process* (2021), [DOI](https://doi.org/10.1108/S0733-558X20210000076004) | Supplied marked-up chapter proof. Quality landscape: §2.2, PDF pp.7–8 / printed pp.85–86. |
| `gcm_model.R` | Supplied active article replication program. Its commented alternative at lines 108–130 is excluded. |
| `RSO_replication.R` | Supplied assembled chapter replication program. Its header reports predecessor files that were not supplied. |

[SOURCE_CORRESPONDENCE.json](SOURCE_CORRESPONDENCE.json) records exact filenames,
byte counts, SHA-256 identities, source locations, current Lean declarations,
hypotheses, evidence classifications and claim limits. It also identifies the
pinned MathEconLib design/contribution guidance used during development.
References concern these supplied versions; a discrepancy in a final version of
record has not been established. The source documents/programs are not bundled.

## From source operations to standalone mathematics

Let `G` denote `gcm_model.R` and `R` denote `RSO_replication.R`. Line ranges refer
to the fingerprinted files, not to a later downloaded revision. The source papers
specify binary configurations and mean quality; array addresses, MSB order and
sorting are additional code conventions, not details attributed to their prose.

| Operation and exact source anchor | Current mathematical representation |
|---|---|
| Binary configuration and allowed interactions: Csaszar pp.2–3 | `Config`, `Tables`, `Topology`, `extract`, `fitness` in [Basic.lean](../OrgLib/NK/Basic.lean). `K` excludes the focal locus; scopes have `K+1` slots. |
| Fixed-width bits/leading zeros: G58–68,83–88; R77–87,101 | `encode`, `decode`, both inverse laws and `encode_val` in [Encoding.lean](../OrgLib/NK/Encoding.lean). |
| Distinct nonfocal neighbors and sorted supplied order: G90–94, especially93 | `Topology.ofNeighbors` in [Indexed.lean](../OrgLib/NK/Indexed.lean). Sorting is not a canonical NK assumption; the constructor preserves its supplied order. |
| Prepend focal bit before neighbors: G75 | `extract_ofNeighbors` in [Indexed.lean](../OrgLib/NK/Indexed.lean). |
| Base-two address and R position `address+1`: G75; R94 | `encode`, `rIndex`, `lookup_rIndex` and their range laws in [Encoding.lean](../OrgLib/NK/Encoding.lean). |
| One indexed table per locus: G97–99, selected at76 | `TableEntries` and `tablesFromEntries`; table indexing alone asserts no independence. |
| Sum contributions divided by N: G72–78,103–104 | `fitness_eq_indexedAverage` proves exact equality with canonical evaluation in [Indexed.lean](../OrgLib/NK/Indexed.lean). |
| Forward cyclic windows: R102–104,94; chapter printed p.85 | `cyclicTopology`, `cyclicTopology_scope_val`, `extract_cyclic` in [Cyclic.lean](../OrgLib/NK/Cyclic.lean): local slot j reads `(i+j) mod N`. |
| A single table sampled at R105, reused at94,106; unindexed φ on printed pp.85–86 | `sharedTables` and `sharedCyclic` in [SharedCyclic/Basic.lean](../OrgLib/NK/SharedCyclic/Basic.lean). Literal equation and active code agree on sharing. |
| Shared indexed lookup/average: R91–96, especially94 | `sharedCyclicFromEntries`, `sharedCyclic_entries_fitness_eq`, `sharedCyclic_fitness_eq` in [SharedCyclic/Basic.lean](../OrgLib/NK/SharedCyclic/Basic.lean). |
| Raw quality before resource weighting and spatial utility: G198–204; R175–181 | A documented scope boundary. Weighted utilities, decisions and trajectories are not formalized here. |

The bounds and maximality results are consequences of the translated mathematics,
not theorems claimed to appear in the papers. The first application demonstrates
reuse through `indexed_fitness_mem_Icc` and the indexed K=0 maximality theorem.
The shared cyclic construction also instantiates canonical NK; its extra symmetry
and separation results are documented in [THEOREMS.md](THEOREMS.md).

## Domain and interpretation boundaries

The mathematical domain allows every natural `N,K` with `K<N`. A table may ignore
some permitted inputs. `K<N` gives positive N and valid nonrepeating scopes; bounds
and probability laws are separate assumptions. The elementary codec also handles
word length zero independently of the positive-N landscape domain.

The literal source-codec correspondence domain is integer `1≤N≤31`, `0≤K<N`,
valid integer state codes and binary words, and correctly sized finite numeric
tables without missing/NaN values. Fixed-input evaluation assumes valid supplied
scopes. This does not promise practical enumeration of `2^31` states. At N=32 the
source helper drops a bit and integer conversion can overflow.

The original G93 sampler has a separate N=2,K=1 exception: R treats a numeric
singleton as a sampling range, so it can select the focal index. The paper's N=12
setting avoids that case. The Lean constructor proves validity of supplied scopes;
it does not verify the original sampler across the full mathematical domain.

## Sampling laws and what was checked

The real laws in [Ensembles.lean](../OrgLib/NK/Ensembles.lean) use Lebesgue measure
restricted to `[0,1]`, finite entry/locus products and measurable fitness
pushforwards. A full independent product is an explicit idealized joint law.
Uniform descriptions and `runif` calls do not by themselves certify an R PRNG or
establish every joint-law assumption. Both sides of the proved law comparison use
the same fixed cyclic topology and labeled configurations.

The [optional validation supplement](../supplements/README.md) compares explicit
fixed inputs with isolated original R evaluators and an independent rational
oracle. Exact/tolerance policies and corruption controls belong to that execution
evidence. The library never calls R. Rational-to-real casting is a separate
universal theorem; finite comparisons do not prove unrestricted R correctness.

[CHECKS.json](CHECKS.json) records the actual current build, source fingerprints
and execution results. Source interpretation, kernel compilation, numerical
comparison and human approval remain separate statuses. Human model/domain and
Lean/library release reviews are pending. No PRNG, random-topology mixture,
behavioral-dynamics or substantive correction-impact result is asserted.
