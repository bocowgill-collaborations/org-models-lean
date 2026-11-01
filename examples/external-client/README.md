# External-client example

[Client.lean](Client.lean) imports only the public library, defines its own two-locus
instance, and applies bounds, K=0 maximality and rational-to-real transfer. Its
exact value is `3/4`; it does not use either application's example data.

After building the prototype, run from its root:

```sh
python3 examples/external-client/prepare_manifest.py
lake -d examples/external-client build Client
```

Python 3.11+ is sufficient. The helper copies exact dependency revisions from the
root manifest and adds the relative path dependency. It does not upgrade branches.
This example shares dependency caches but keeps its own `.lake/build` directory.
Its generated manifest is ignored.

The layout assumes this directory is two levels below the library. If moved,
update `path`/`packagesDir` in [lakefile.toml](lakefile.toml), and the root calculation,
path dependency and `packagesDir` in [prepare_manifest.py](prepare_manifest.py).
A successful client build checks its own theorem applications and exact-value guard.
