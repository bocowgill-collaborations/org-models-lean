# Optional R translation-validation supplement

The core builds without R. A separate `nk-r-validation-supplement.tar.gz` source
archive contains the larger fixed-input project. It is prepared separately and
is not stored in Git. A download location for this optional archive has not yet
been published; the public core and its proofs do not require it.

The supplement contains 16 rational fixtures, a standalone Lean evaluator, an
independent Python rational oracle, a first-party R harness, source correspondence
and exact/tolerance policies. It checks 16,480 states plus rotations/Hamming formulas:
168,232 numeric comparisons. Controls corrupt bit order, neighbor order and one entry.

It does not run the papers' full simulations or sample pseudorandom inputs. Original
R programs are supplied separately and are never sourced wholesale. Only the
fingerprinted evaluator functions are extracted. The controlled locus-specific
alternative is generated locally and labeled separately.

Extract the archive outside this repository and follow its README:

```sh
python3 configure.py --library-root /path/to/org-models-lean
lake build
python3 scripts/run_validation.py \
  --orgsci-source /path/to/gcm_model.R \
  --chapter-source /path/to/RSO_replication.R
```

Requires Python 3.11+, R, `glue`, `jsonlite`, and separately obtained originals
matching the [source fingerprints](../docs/SOURCE_CORRESPONDENCE.json). Configuration
preserves dependency pins; fresh outputs stay inside the extracted supplement.
Its standalone Lean evaluator also runs without R.

[CHECKS.json](../docs/CHECKS.json) records the current run and archive digest.
Detailed source-to-Lean mapping remains public in [SOURCES.md](../docs/SOURCES.md).
Original source extracts, derived R text, PDFs, correspondence and raw development
logs are excluded from the supplement source archive.
