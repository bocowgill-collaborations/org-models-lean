#!/usr/bin/env python3
"""Resolve the local client with the exact dependency revisions in orglib's lock file."""

from copy import deepcopy
import json
from pathlib import Path


def main() -> None:
    client = Path(__file__).resolve().parent
    root = client.parent.parent
    root_manifest = json.loads((root / "lake-manifest.json").read_text())
    packages = deepcopy(root_manifest["packages"])
    for package in packages:
        package["inherited"] = True
    packages.append({
        "type": "path",
        "name": "orglib",
        "dir": "../..",
        "manifestFile": "lake-manifest.json",
        "inherited": False,
        "configFile": "lakefile.toml",
    })
    manifest = {
        "version": root_manifest["version"],
        "packagesDir": "../../.lake/packages",
        "packages": packages,
        "name": "orglib_client_example",
        "lakeDir": ".lake",
    }
    (client / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Prepared client manifest with {len(packages) - 1} exact dependency pins.")


if __name__ == "__main__":
    main()
