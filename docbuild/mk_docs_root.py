#!/usr/bin/env python3
"""Generate docbuild/TauCetiDocs.lean, a root module that imports every TauCeti module.

doc-gen4's library `docs` facet documents a library's *root* modules and their import
closure. TauCeti's own root (`TauCeti.lean`) is intentionally empty and imports nothing —
the library is assembled from the `TauCeti.*` glob, not from a re-exporting root — so
pointing doc-gen at it documents nothing. This script writes an aggregator root that
`public import`s all 500-plus modules, so its closure is the whole library (and, in turn,
the Mathlib declarations it depends on). Run it before `lake build TauCetiDocs:docs`.

The output is a build artifact, not source: it is git-ignored and regenerated (in CI and
locally) so it can never drift from the module tree.
"""

from pathlib import Path

HERE = Path(__file__).resolve().parent          # .../docbuild
SRC = HERE.parent / "TauCeti"                    # .../TauCeti
OUT = HERE / "TauCetiDocs.lean"


def module_names() -> list[str]:
    names = []
    for path in SRC.rglob("*.lean"):
        rel = path.relative_to(SRC.parent).with_suffix("")
        names.append(".".join(rel.parts))
    return sorted(names)


def main() -> None:
    mods = module_names()
    lines = ["module", ""]
    lines += [f"public import {m}" for m in mods]
    OUT.write_text("\n".join(lines) + "\n")
    print(f"wrote {OUT} importing {len(mods)} modules")


if __name__ == "__main__":
    main()
