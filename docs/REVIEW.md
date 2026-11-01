# Independent public-prototype review

**Technical review approved; no open findings. Human release reviews pending.**
Date: 2026-11-01. This is agent review, not human model/domain, Lean/library or
foundational-definition approval.

## Scope and scientific interpretation

The review inspected the README, exact claim pointers, source/theorem correspondence,
renamed core and clients, compact example/walkthrough, newcomer instructions, source
checker, archive tool and separately maintained validation supplement. It reused the
independent comparison of the thirteen mathematical modules and their public tests
against the preserved historical snapshot, and directly checked the new examples.

The public title/prose describe a proof of concept without branding a future library.
The technical namespace remains in code and paths. Authors/titles receive bibliographic
credit in comments/documentation; mathematical identifiers and module paths are neutral.

The three demonstrations are stated accurately: a proposed canonical deterministic NK
interface; exact ordered-neighborhood correspondence with inherited bounds; and a shared
cyclic NK restriction with extra symmetry, fixed-label nonrepresentation and different
continuous landscape laws at the same topology in the proved parameter settings.
Both application landscapes remain deterministic NK. Full organizational dynamics,
PRNG verification and substantive simulation effects are outside the proved scope.
Lower bounds are distinguished from exact probabilities and supplied proofs from
uninspected versions of record. All eight three-component values are kernel proofs.

## Tooling findings resolved

The source checker originally accepted a wrong-but-existing README line anchor. It now
binds each advertised labelled link to its exact claim row and declaration line.
The archive verifier originally accepted removal of a required script together with its
manifest entry. It now requires every source role and the imported fixture-axiom module
independently of that manifest. Source-directory links and cross-platform personal
paths are rejected too. All reported controls were rerun successfully after fixes.

Independent fixtures reject project-axiom injection, author-named Lean declarations,
public imports across the core/client boundary, README branding, broken links and
incorrect existing line anchors; citation comments remain allowed. Archive controls
reject byte corruption, duplicate/traversal/link entries, excluded R/results/config
roles, schema changes, rewritten-manifest omissions and personal home/temp paths.
The default source archive verifies, extracts and repackages byte-identically.

## Execution evidence

The reviewed independent source checkout began without project build products and used
nine exact clean pinned dependency checkouts with independent dependency-cache copies.
The raw reproduction report/logs show:

| Check | Result |
|---|---|
| Default library/examples/tests/demo build | 5,008 jobs, exit 0, no warnings |
| External public-only client | 2,499 jobs, exit 0, no warnings |
| Extracted supplement build | 4,986 jobs, exit 0, no warnings |
| Short demo | Seven expected lines; exact values 1/2, 13/63, 5/27, 1, 0 |
| Fresh fixed-input R comparison | 16 fixtures, 16,480 states, 168,232 numeric checks, zero failures |
| Scientific corruption controls | Reversed bits, reversed neighbors and changed entry rejected |
| Original comparison after neutral case-name mapping | Mathematical TSV output byte-identical |

The supplement artifact has 19 members and SHA-256
`28514c18ac89b734a9fd3402c4e79668e102481f26a583d7c8c32bf5aea812aa`.
It contains original harness/specification code and fixture data, with no supplied
PDFs, original/derived R text, generated local configuration, result tables or raw
historical environment records. It is an optional client; the public core needs no R.

The tested mode uses offline dependency caches, not an internet-fresh bootstrap or an
all-dependencies rebuild. Exact final source fingerprints, any repeated clean run,
command/log identities, numerical policies and source-hash checks are recorded in
[CHECKS.json](CHECKS.json). This review distinguishes those execution records from
static scans and from the proofs checked by Lean.

## Reviewed source identities

| File | SHA-256 |
|---|---|
| `README.md` | `be7dbc996a3e52ffe1da37ad9a846281866b8064dcbd6d3dbe022b47ed5a1cfb` |
| `docs/CLAIMS.json` | `1835b0a3c1a01f7015448f869dd141a9830d206225f59b3b89b0f27771e3e801` |
| `scripts/check.py` | `a70ead040e405e8a7f60253053c8add5b4e5706176328cc47d5dc237a9a83b85` |
| `scripts/package_supplement.py` | `9323cad3768a53a4b42ba2508c07a91691233b7dd932bfa8fe399e6e92ef3bc4` |
| `OrgLibExamples/ThreeComponent.lean` | `fb25decf8005bf1388964d52a536c562f421dcdbcaefe9e958bd54d402bf5fd8` |
| `OrgLibExamples/Walkthrough.lean` | `17ccec4a549a1989e913890456a49f0082d7974de8b29cb26dd841b19cdf0335` |

Approval covers the stated local preparation and technical evidence. Human model/domain,
Lean/library and maintainer decisions remain pending in [WORKFLOW.md](WORKFLOW.md).
It does not grant rights to third-party source material or authorize publication.
No caller-repository commit or push was performed by this review.
