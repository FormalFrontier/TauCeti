"""Copy the root project's toolchain and dependency pins into `web/examples`.

Run with: python3 scripts/sync_web_pins.py          (rewrite)
          python3 scripts/sync_web_pins.py --check  (report, change nothing)

`web/examples` compiles the TauCeti library, so it must do so with exactly the Lean and exactly
the Mathlib the library is written for. `scripts/test_web_pins.py` explains why at length and
enforces it; this script is the other half, the one that makes satisfying it free. The daily
Mathlib bump in `.github/workflows/update.yml` calls it, and a human doing a bump by hand should
too.

The examples manifest is DERIVED, not independently resolved: it is the root manifest's package
list, plus the two entries only this project has -- the path requirement on the repository root,
and SubVerso, which is resolved by `web/` and shared. Deriving it rather than running `lake update`
keeps the bump job free of a toolchain install and a Mathlib clone, and it cannot drift, because
every shared entry is copied from the root manifest verbatim rather than re-resolved.

That is only safe while the derivation reproduces what Lake itself writes. `test_web_pins.py`
checks exactly that: it re-runs this script against the checked-in files and requires no change.
The manifests in the tree are written by real `lake update` runs, so if Lake ever changes its
resolution or its formatting, the next genuine update makes that test fail loudly rather than
letting this script quietly write something Lake would not have.
"""

import argparse
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ROOT_MANIFEST = ROOT / "lake-manifest.json"
ROOT_TOOLCHAIN = ROOT / "lean-toolchain"
EXAMPLES_DIR = ROOT / "web/examples"
EXAMPLES_MANIFEST = EXAMPLES_DIR / "lake-manifest.json"
EXAMPLES_TOOLCHAIN = EXAMPLES_DIR / "lean-toolchain"
EXAMPLES_LAKEFILE = EXAMPLES_DIR / "lakefile.lean"

# The revision in the Mathlib requirement, which is a bare commit so that it cannot resolve to
# something different later. Only the revision is rewritten; the surrounding text is left alone.
MATHLIB_REV = re.compile(
    r'(require\s+mathlib\s+from\s+git\s*\n?\s*'
    r'"https://github\.com/leanprover-community/mathlib4"\s*@\s*")([0-9a-f]{40})(")'
)

# Entries the examples project has and the root project does not, in the positions Lake writes
# them: the path requirement first, then SubVerso after Mathlib.
LOCAL_FIRST = "TauCeti"
LOCAL_AFTER_MATHLIB = "subverso"


def load(path):
    return json.loads(path.read_text())


def render(manifest):
    """Serialise a manifest the way Lake does, so a derived file and a `lake update` agree.

    Lake writes one top-level key per line indented by a single space, and one package field per
    line indented by three, with packages separated by two. Reproducing it exactly is what keeps
    a genuine `lake update` from showing up as a whitespace diff.
    """
    def field(key, value, indent):
        return f'{indent}{json.dumps(key)}: {json.dumps(value)}'

    def package(entry):
        fields = [field(k, v, "   ") for k, v in entry.items()]
        return "{" + ",\n".join(fields)[3:] + "}"

    parts = []
    for key, value in manifest.items():
        if key == "packages":
            body = ",\n  ".join(package(entry) for entry in value)
            parts.append(f' "packages":\n [{body}]')
        else:
            parts.append(field(key, value, " "))
    return "{" + ",\n".join(parts)[1:] + "}\n"


def derived_manifest():
    """The examples manifest the root pins imply, preserving this project's own two entries."""
    root_packages = {p["name"]: p for p in load(ROOT_MANIFEST)["packages"]}
    current = load(EXAMPLES_MANIFEST)
    local = {p["name"]: p for p in current["packages"]}

    for name in (LOCAL_FIRST, LOCAL_AFTER_MATHLIB):
        if name not in local:
            raise SystemExit(
                f"web/examples/lake-manifest.json has no {name} entry to preserve; it is not the "
                "manifest this script knows how to derive. Re-run `lake update` in web/examples "
                "and reconcile by hand.")
    if "mathlib" not in root_packages:
        raise SystemExit("the root lake-manifest.json pins no mathlib")

    # Mathlib differs in one field only: the root nominates `master` and records the resolved
    # commit, while this project pins the commit itself, so that the two cannot come apart.
    mathlib = dict(root_packages["mathlib"])
    mathlib["inputRev"] = mathlib["rev"]

    packages = [local[LOCAL_FIRST], mathlib, local[LOCAL_AFTER_MATHLIB]]
    packages += [entry for name, entry in root_packages.items() if name != "mathlib"]

    return {**current, "packages": packages}


def planned_changes():
    """[(path, new_text)] for every file whose contents the root pins disagree with."""
    changes = []

    toolchain = ROOT_TOOLCHAIN.read_text()
    if EXAMPLES_TOOLCHAIN.read_text() != toolchain:
        changes.append((EXAMPLES_TOOLCHAIN, toolchain))

    rev = {p["name"]: p for p in load(ROOT_MANIFEST)["packages"]}["mathlib"]["rev"]
    lakefile = EXAMPLES_LAKEFILE.read_text()
    rewritten, count = MATHLIB_REV.subn(lambda m: m.group(1) + rev + m.group(3), lakefile)
    if count != 1:
        raise SystemExit(
            f"expected exactly one pinned mathlib commit in {EXAMPLES_LAKEFILE.relative_to(ROOT)}, "
            f"found {count}; refusing to guess which requirement to rewrite")
    if rewritten != lakefile:
        changes.append((EXAMPLES_LAKEFILE, rewritten))

    manifest = render(derived_manifest())
    if EXAMPLES_MANIFEST.read_text() != manifest:
        changes.append((EXAMPLES_MANIFEST, manifest))

    return changes


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true",
                        help="exit 1 if anything would change, and write nothing")
    args = parser.parse_args(argv)

    changes = planned_changes()
    for path, _ in changes:
        print(f"{'would update' if args.check else 'updated'} {path.relative_to(ROOT)}")
    if not changes:
        print("web/examples already matches the root pins")
        return 0
    if args.check:
        return 1
    for path, text in changes:
        path.write_text(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
