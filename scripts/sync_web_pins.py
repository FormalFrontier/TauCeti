"""Generate `web/examples/lake-manifest.json` from the root project's pins.

Run with: python3 scripts/sync_web_pins.py          (write it)
          python3 scripts/sync_web_pins.py --check  (report, write nothing)

`web/examples` compiles the TauCeti library, so it must do so with exactly the Lean and exactly
the Mathlib the library is written for. Both are therefore DERIVED from the root's rather than
resolved independently, and neither is committed: `.gitignore` covers them, and the Pages
workflow generates them before building.

The toolchain has to be written out rather than inherited. elan does resolve a toolchain from
the nearest ancestor directory, so simply deleting `web/examples/lean-toolchain` looks like it
would make this project use the root's -- but the nearest ancestor is `web/`, and
`web/lean-toolchain` pins the Verso site's Lean, which lags the library's. Deleting the file
therefore pins this project to exactly the stale toolchain that broke the site in September
2026, silently. Verified by measurement, not by reading elan's documentation.

The alternative, which this replaces, was to commit both copies and keep them synced. That
worked, but it put two files outside `TauCeti/` into every daily Mathlib bump, and the merge
policy refuses to auto-merge a pull request touching a lakefile or an unlisted path. So every
bump would have stopped for a human. Deriving the manifest at build time keeps the bump touching
only the root pins, which is what the policy already allows.

Nothing here re-resolves anything. Every shared package is copied from the root manifest
verbatim, so the two cannot disagree about a revision. The only entries this synthesises are the
two the examples project has and the root does not: the path requirement on the repository root,
and SubVerso.

SubVerso is deliberately shared with `web/` rather than the root. It exists so that a Verso
document can describe Lean code built by a DIFFERENT Lean version, which is why this project can
sit on the root toolchain while `web/` stays on Verso's. What it does not promise is
compatibility between its own versions, its data format being an implementation detail, so both
sides must resolve the same commit -- and that commit is read from `web/lake-manifest.json`,
which is committed and is what the site actually builds against.
"""

import argparse
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ROOT_MANIFEST = ROOT / "lake-manifest.json"
ROOT_TOOLCHAIN = ROOT / "lean-toolchain"
WEB_MANIFEST = ROOT / "web/lake-manifest.json"
EXAMPLES_DIR = ROOT / "web/examples"
EXAMPLES_MANIFEST = EXAMPLES_DIR / "lake-manifest.json"
EXAMPLES_TOOLCHAIN = EXAMPLES_DIR / "lean-toolchain"
EXAMPLES_LAKEFILE = EXAMPLES_DIR / "lakefile.lean"

SUBVERSO_URL = "https://github.com/leanprover/subverso"
MATHLIB_URL = "https://github.com/leanprover-community/mathlib4"

# The revision each requirement nominates, read from the lakefile so that the generated
# manifest's `inputRev` says what the lakefile asked for rather than a second, independent claim.
def _require(name, url):
    return re.compile(
        rf'require\s+{name}\s+from\s+git\s*\n?\s*"{re.escape(url)}"\s*@\s*"([^"]+)"')

MATHLIB_REQUIRE = _require("mathlib", MATHLIB_URL)
SUBVERSO_REQUIRE = _require("subverso", SUBVERSO_URL)

# The path requirement on the repository root, which is what makes this project compile the
# library at all. Written out because there is no committed manifest left to copy it from.
TAUCETI_ENTRY = {
    "type": "path", "scope": "", "name": "TauCeti",
    "manifestFile": "lake-manifest.json", "inherited": False,
    "dir": "../..", "configFile": "lakefile.toml",
}


def load(path):
    return json.loads(path.read_text())


def nominated(pattern, what):
    text = "".join(line for line in EXAMPLES_LAKEFILE.read_text().splitlines(keepends=True)
                   if not line.lstrip().startswith("--"))
    found = pattern.findall(text)
    if len(found) != 1:
        raise SystemExit(
            f"expected exactly one {what} requirement in "
            f"{EXAMPLES_LAKEFILE.relative_to(ROOT)}, found {len(found)}")
    return found[0]


def render(manifest):
    """Serialise a manifest the way Lake does, so a generated file and a `lake update` agree."""
    def field(key, value, indent):
        return f'{indent}{json.dumps(key)}: {json.dumps(value)}'

    def package(entry):
        return "{" + ",\n".join(field(k, v, "   ") for k, v in entry.items())[3:] + "}"

    parts = []
    for key, value in manifest.items():
        if key == "packages":
            body = ",\n  ".join(package(entry) for entry in value)
            parts.append(f' "packages":\n [{body}]')
        else:
            parts.append(field(key, value, " "))
    return "{" + ",\n".join(parts)[1:] + "}\n"


def derived_manifest():
    root = load(ROOT_MANIFEST)
    root_packages = {p["name"]: p for p in root["packages"]}
    if "mathlib" not in root_packages:
        raise SystemExit("the root lake-manifest.json pins no mathlib")

    web = {p["name"]: p for p in load(WEB_MANIFEST)["packages"]}
    if "subverso" not in web:
        raise SystemExit("web/lake-manifest.json resolves no subverso to share")

    subverso = {
        "url": SUBVERSO_URL, "type": "git", "subDir": None, "scope": "",
        # The commit the Verso site builds against; see the module docstring.
        "rev": web["subverso"]["rev"], "name": "subverso",
        "manifestFile": "lake-manifest.json",
        "inputRev": nominated(SUBVERSO_REQUIRE, "subverso"),
        "inherited": False, "configFile": "lakefile.lean",
    }
    # Named for its effect: reading it also refuses a lakefile that has stopped asking for
    # Mathlib the way the root does, which would make copying the root's entry a lie.
    nominated(MATHLIB_REQUIRE, "mathlib")

    packages = [TAUCETI_ENTRY, root_packages["mathlib"], subverso]
    packages += [p for name, p in root_packages.items() if name != "mathlib"]
    return {
        "version": root["version"], "packagesDir": root["packagesDir"],
        "packages": packages, "name": "examples",
        "lakeDir": root["lakeDir"], "fixedToolchain": root["fixedToolchain"],
    }


def planned_changes():
    """[(path, contents)] for every generated file whose contents are not what the root implies."""
    changes = []
    # Written, not inherited: `web/lean-toolchain` sits between this directory and the root and
    # names Verso's Lean, so an absent file here resolves to that rather than to the library's.
    toolchain = ROOT_TOOLCHAIN.read_text()
    if not EXAMPLES_TOOLCHAIN.exists() or EXAMPLES_TOOLCHAIN.read_text() != toolchain:
        changes.append((EXAMPLES_TOOLCHAIN, toolchain))
    manifest = render(derived_manifest())
    if not EXAMPLES_MANIFEST.exists() or EXAMPLES_MANIFEST.read_text() != manifest:
        changes.append((EXAMPLES_MANIFEST, manifest))
    return changes


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true",
                        help="exit 1 if the generated manifest differs, and write nothing")
    args = parser.parse_args(argv)
    changes = planned_changes()
    for path, _ in changes:
        print(f"{'would write' if args.check else 'wrote'} {path.relative_to(ROOT)}")
    if not changes:
        print("web/examples already carries the pins the root implies")
        return 0
    if args.check:
        return 1
    for path, text in changes:
        path.write_text(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
