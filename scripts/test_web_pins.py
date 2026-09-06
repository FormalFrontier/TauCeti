"""Ensure the site's examples project is pinned exactly as the root project is.

Run with: python3 scripts/test_web_pins.py

`web/examples` compiles the TauCeti library itself -- that is its entire purpose, since the site
showcases theorems and must type-check them against the real library rather than a copy. So it
needs a Lean toolchain and a Mathlib, and it declares its own. Nothing in Lake makes those
declarations agree with the root project's, and nothing outside `pages.yml` ever builds this
project, so when they part company the only symptom is the three-hourly Pages job going red while
every pull request stays green.

That is not hypothetical. The root pins move every day under `.github/workflows/update.yml`, which
never touched `web/examples`. By September 2026 the examples project was two Lean releases and
several hundred Mathlib commits behind, and the site build broke on a deck-transformation `HSMul`
instance -- a file that compiled perfectly well at the root pins. The site had already been serving
stale content for a day before anyone looked, because a failing scheduled workflow is quiet.

The invariant this file enforces is what makes the arrangement sound:

    web/examples builds the TauCeti library at EXACTLY the root toolchain and the root Mathlib.

Once that holds, "the examples project builds the library" is the same question as "the root
project builds the library", which is a required check on every pull request. The site build
becomes trustworthy for free, with no second expensive CI job compiling Mathlib a second time --
and, as a bonus, the two projects can share a Lake artifact cache instead of duplicating the work.

SubVerso is the one deliberate exception, and it points the other way. It exists precisely so that
a Verso document can describe Lean code built by a DIFFERENT Lean version, which is why `web/` may
sit on Verso's toolchain while `web/examples` sits on the root's. What SubVerso does not promise is
compatibility between its own versions: its data format is documented as an implementation detail.
So the toolchains may differ across those two projects, but the resolved SubVerso commit may not.

To move the root pins, move these copies in the same commit. `update.yml` does that automatically
for the daily Mathlib bump; a hand-written bump has to do it by hand.
"""

import json
import pathlib
import re
import subprocess
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
ROOT_MANIFEST = ROOT / "lake-manifest.json"
ROOT_TOOLCHAIN = ROOT / "lean-toolchain"
WEB_MANIFEST = ROOT / "web/lake-manifest.json"
EXAMPLES_DIR = ROOT / "web/examples"
EXAMPLES_MANIFEST = EXAMPLES_DIR / "lake-manifest.json"
EXAMPLES_TOOLCHAIN = EXAMPLES_DIR / "lean-toolchain"
EXAMPLES_LAKEFILE = EXAMPLES_DIR / "lakefile.lean"
SYNC = ROOT / "scripts/sync_web_pins.py"

# The Mathlib requirement in web/examples/lakefile.lean, which must name the root manifest's
# revision as a bare commit. A branch or tag here would resolve to whatever it pointed at on the
# day someone last ran `lake update`, which is exactly the drift this file exists to prevent.
MATHLIB_REQUIRE = re.compile(
    r'require\s+mathlib\s+from\s+git\s*\n?\s*'
    r'"https://github\.com/leanprover-community/mathlib4"\s*@\s*"([0-9a-f]{40})"'
)
# The path requirement on the repository root. If this ever goes away, the examples project stops
# compiling the library, and every other check in this file stops meaning anything -- the whole
# argument above rests on the two projects building the same source.
TAUCETI_REQUIRE = re.compile(r'require\s+«?TauCeti»?\s+from\s+"\.\./\.\."')

# Resolved by `web/`, not declared here: see the module docstring.
SHARED_WITH_WEB = "subverso"


def source(path):
    """The file with whole-line `--` comments dropped, so only declarations are matched."""
    return "".join(line for line in path.read_text().splitlines(keepends=True)
                   if not line.lstrip().startswith("--"))


def packages(manifest):
    """Package name -> entry, for the git packages a manifest pins."""
    data = json.loads(manifest.read_text())
    return {p["name"]: p for p in data["packages"] if p.get("type") == "git"}


def revisions(manifest):
    return {name: entry["rev"] for name, entry in packages(manifest).items()}


class WebPins(unittest.TestCase):
    def test_the_files_exist(self):
        # Every test below reads these; a rename would otherwise make the suite vacuously green.
        for path in (ROOT_MANIFEST, ROOT_TOOLCHAIN, WEB_MANIFEST,
                     EXAMPLES_MANIFEST, EXAMPLES_TOOLCHAIN, EXAMPLES_LAKEFILE):
            with self.subTest(path=path.name):
                self.assertTrue(path.is_file(), f"missing {path.relative_to(ROOT)}")

    def test_examples_still_builds_the_library(self):
        # The premise of every other check in this file.
        self.assertRegex(
            source(EXAMPLES_LAKEFILE), TAUCETI_REQUIRE,
            "web/examples/lakefile.lean no longer requires TauCeti from '../..'. If the examples "
            "project has stopped compiling the library, the pin invariant this file enforces is "
            "no longer what makes the site build trustworthy -- revisit the module docstring "
            "rather than deleting this test.")

    def test_examples_uses_the_root_toolchain(self):
        self.assertEqual(
            EXAMPLES_TOOLCHAIN.read_text().strip(), ROOT_TOOLCHAIN.read_text().strip(),
            "web/examples/lean-toolchain differs from the root lean-toolchain. The examples "
            "project compiles the TauCeti library, so it must do so with the Lean the library is "
            "written for. Copy the root lean-toolchain over it.")

    def test_lakefile_pins_the_root_mathlib_revision(self):
        text = source(EXAMPLES_LAKEFILE)
        found = MATHLIB_REQUIRE.findall(text)
        self.assertEqual(
            len(found), 1,
            "expected exactly one `require mathlib from git ... @ \"<40-hex commit>\"` in "
            f"web/examples/lakefile.lean, found {len(found)}. A branch or tag pin here would "
            "resolve to whatever it pointed at on the day someone last ran `lake update`.")
        expected = revisions(ROOT_MANIFEST)["mathlib"]
        self.assertEqual(
            found[0], expected,
            "web/examples/lakefile.lean pins a different Mathlib from the root lake-manifest.json "
            f"(examples {found[0]}, root {expected}). Update the require to the root revision and "
            "re-run `lake update` in web/examples.")

    def test_examples_manifest_matches_the_root_manifest(self):
        root_revs = revisions(ROOT_MANIFEST)
        examples_revs = revisions(EXAMPLES_MANIFEST)
        # Checked against the manifest rather than the lakefile because the manifest is what Lake
        # actually builds from: an edited require with a stale manifest beside it still builds the
        # old Mathlib, and would otherwise slip past the check above.
        for name, expected in sorted(root_revs.items()):
            with self.subTest(package=name):
                self.assertIn(
                    name, examples_revs,
                    f"the root project pins {name} but web/examples/lake-manifest.json does not. "
                    "Re-run `lake update` in web/examples.")
                self.assertEqual(
                    examples_revs[name], expected,
                    f"web/examples pins {name} at {examples_revs.get(name)}, the root project at "
                    f"{expected}. Re-run `lake update` in web/examples after matching the Mathlib "
                    "require, so the whole dependency closure follows the root.")

    def test_examples_pins_nothing_the_root_does_not(self):
        extra = set(revisions(EXAMPLES_MANIFEST)) - set(revisions(ROOT_MANIFEST))
        self.assertEqual(
            extra, {SHARED_WITH_WEB},
            "web/examples resolves git packages the root project does not pin: "
            f"{sorted(extra - {SHARED_WITH_WEB})}. Anything the examples project depends on beyond "
            f"the root closure and {SHARED_WITH_WEB} is unpinned by the root and free to drift; "
            "add it to this test deliberately, with a rule for keeping it honest.")

    def test_subverso_matches_the_verso_site(self):
        web = revisions(WEB_MANIFEST)
        examples = revisions(EXAMPLES_MANIFEST)
        self.assertIn(SHARED_WITH_WEB, web, "web/lake-manifest.json does not resolve subverso")
        self.assertIn(SHARED_WITH_WEB, examples,
                      "web/examples/lake-manifest.json does not resolve subverso")
        self.assertEqual(
            examples[SHARED_WITH_WEB], web[SHARED_WITH_WEB],
            "web/examples and web/ resolve different SubVerso commits (examples "
            f"{examples[SHARED_WITH_WEB]}, site {web[SHARED_WITH_WEB]}). SubVerso supports being "
            "built on a different Lean toolchain from the Verso that reads its output, but makes "
            "no promise across its own versions -- its data format is an implementation detail. "
            "The site would read the extracted snippets with a reader that did not write them.")

    def test_the_sync_script_agrees_with_lake(self):
        # scripts/sync_web_pins.py DERIVES this project's manifest from the root's rather than
        # re-resolving it, which is only sound while the derivation reproduces what Lake itself
        # writes. The manifests in the tree come from real `lake update` runs, so requiring the
        # script to leave them untouched is what ties the two together: if Lake ever changes how
        # it resolves or formats a manifest, the next genuine update fails here instead of the
        # script quietly writing something Lake would not have.
        result = subprocess.run(
            [sys.executable, str(SYNC), "--check"],
            capture_output=True, text=True, cwd=ROOT)
        self.assertEqual(
            result.returncode, 0,
            "scripts/sync_web_pins.py --check wants to change the checked-in files:\n"
            f"{result.stdout}{result.stderr}\n"
            "Either the pins are out of sync (run the script without --check), or the script no "
            "longer reproduces what `lake update` writes and needs updating to match Lake.")


if __name__ == "__main__":
    unittest.main()
