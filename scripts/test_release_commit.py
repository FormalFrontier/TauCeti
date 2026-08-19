#!/usr/bin/env python3
"""Unit tests for scripts/release_commit.py.

Run with: python3 scripts/test_release_commit.py

No network and no git: everything here is text in, problems out. This is the checker
that decides whether `.github/workflows/release-tag.yml` may build a commit
unsandboxed and publish its oleans, so the tests are written as "what must this
refuse", not "what does it accept".
"""

import json
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import release_commit as rc  # noqa: E402

M = "db584cd6d46c92f209a44c0f1c829460d327499d"
OTHER = "1111111111111111111111111111111111111111"

BASE = {
    "version": "1.2.0",
    "packagesDir": ".lake/packages",
    "packages": [
        {"url": "https://github.com/leanprover-community/mathlib4", "type": "git",
         "subDir": None, "scope": "", "rev": OTHER, "name": "mathlib",
         "manifestFile": "lake-manifest.json", "inputRev": "master",
         "inherited": False, "configFile": "lakefile.lean"},
        {"url": "https://github.com/leanprover-community/batteries", "type": "git",
         "subDir": None, "scope": "leanprover-community", "rev": "2" * 40,
         "name": "batteries", "manifestFile": "lake-manifest.json", "inputRev": "main",
         "inherited": True, "configFile": "lakefile.toml"},
    ],
    "name": "TauCeti", "lakeDir": ".lake", "fixedToolchain": False,
}

MATHLIB = {
    "version": "1.3.0",
    "packagesDir": ".lake/packages",
    "packages": [
        {"url": "https://github.com/leanprover-community/batteries", "type": "git",
         "subDir": None, "scope": "leanprover-community", "rev": "3" * 40,
         "name": "batteries", "manifestFile": "lake-manifest.json", "inputRev": "main",
         "inherited": False, "configFile": "lakefile.toml"},
    ],
    "name": "mathlib", "lakeDir": ".lake", "fixedToolchain": True,
}


def valid_release_manifest():
    """What toolchain_tags.py produces: our root fields and mathlib entry, mathlib's
    dependency set, `inherited` normalised the way our own Lake writes it."""
    manifest = json.loads(json.dumps(BASE))
    manifest["version"] = MATHLIB["version"]
    mathlib_pkg = dict(manifest["packages"][0], rev=M)
    deps = [dict(p, inherited=True) for p in MATHLIB["packages"]]
    manifest["packages"] = [mathlib_pkg] + deps
    return manifest


def dumps(obj):
    return json.dumps(obj, indent=1)


class Toolchain(unittest.TestCase):
    def test_accepts_the_release_s_own_toolchain(self):
        self.assertEqual(
            rc.check_toolchain("leanprover/lean4:v4.33.0\n", "leanprover/lean4:v4.33.0\n",
                               "v4.33.0"), [])

    def test_rejects_a_different_toolchain(self):
        problems = rc.check_toolchain("leanprover/lean4:v4.34.0-rc1",
                                      "leanprover/lean4:v4.33.0", "v4.33.0")
        self.assertTrue(any("lean-toolchain is" in p for p in problems))

    def test_rejects_a_tag_that_does_not_name_the_release_it_claims(self):
        # If mathlib's own lean-toolchain at the tag is not X, the tag is mislabelled
        # and building against it would produce something that is not "TauCeti on X".
        problems = rc.check_toolchain("leanprover/lean4:v4.33.0",
                                      "leanprover/lean4:v4.32.0", "v4.33.0")
        self.assertTrue(any("does not name the release" in p for p in problems))

    def test_rejects_a_name_that_is_not_a_release(self):
        for name in ("master", "v4.32.0-rc1-patch1", "nightly-2026-01-01", ""):
            self.assertTrue(rc.check_toolchain("x", "x", name), name)


class Manifest(unittest.TestCase):
    def check(self, manifest=None, base=None, mathlib=None, rev=M):
        return rc.check_manifest(dumps(manifest or valid_release_manifest()),
                                 dumps(base or BASE), dumps(mathlib or MATHLIB), rev)

    def test_accepts_a_valid_release_manifest(self):
        self.assertEqual(self.check(), [])

    def test_inherited_is_not_compared(self):
        # bump-guard compares (type, url, rev, inputRev) and not `inherited`, because
        # whether Lake wrote true or false there says nothing about which revision is
        # pinned. The constructor normalises it; the verifier must not care either way.
        manifest = valid_release_manifest()
        manifest["packages"][1]["inherited"] = False
        self.assertEqual(self.check(manifest), [])

    def test_rejects_a_mathlib_pin_that_is_not_the_release_tag(self):
        manifest = valid_release_manifest()
        manifest["packages"][0]["rev"] = "9" * 40
        self.assertTrue(any("not the release tag commit" in p for p in self.check(manifest)))

    def test_rejects_a_repository_swap(self):
        manifest = valid_release_manifest()
        manifest["packages"][0]["url"] = "https://github.com/attacker/mathlib4"
        self.assertTrue(any("url changed" in p for p in self.check(manifest)))

    def test_accepts_a_url_that_differs_only_by_a_git_suffix_or_slash(self):
        manifest = valid_release_manifest()
        manifest["packages"][0]["url"] = BASE["packages"][0]["url"] + ".git"
        self.assertEqual(self.check(manifest), [])

    def test_rejects_a_changed_nomination(self):
        # `inputRev` names the branch the pin is trusted to come from. A release commit
        # that repointed it at a tag would still look plausible but would take the
        # manifest out of bump-guard's reach forever after.
        manifest = valid_release_manifest()
        manifest["packages"][0]["inputRev"] = "v4.33.0"
        self.assertTrue(any("nominated branch changed" in p for p in self.check(manifest)))

    def test_rejects_a_dependency_mathlib_does_not_have(self):
        manifest = valid_release_manifest()
        manifest["packages"].append(dict(MATHLIB["packages"][0], name="sneaky",
                                         rev="4" * 40))
        self.assertTrue(any("does not depend on" in p for p in self.check(manifest)))

    def test_rejects_a_missing_dependency(self):
        manifest = valid_release_manifest()
        manifest["packages"] = manifest["packages"][:1]
        self.assertTrue(any("omits" in p for p in self.check(manifest)))

    def test_rejects_a_dependency_repointed_independently_of_mathlib(self):
        manifest = valid_release_manifest()
        manifest["packages"][1]["rev"] = "5" * 40
        self.assertTrue(any("but mathlib pins" in p for p in self.check(manifest)))

    def test_rejects_a_path_dependency_and_a_non_sha_rev(self):
        manifest = valid_release_manifest()
        manifest["packages"][1]["type"] = "path"
        self.assertTrue(any("not git" in p for p in self.check(manifest)))
        manifest = valid_release_manifest()
        manifest["packages"][1]["rev"] = "main"
        self.assertTrue(any("40-hex" in p for p in self.check(manifest)))

    def test_rejects_a_duplicated_package(self):
        manifest = valid_release_manifest()
        manifest["packages"].append(dict(manifest["packages"][1]))
        self.assertTrue(any("more than once" in p for p in self.check(manifest)))

    def test_rejects_a_changed_root_field(self):
        for field, value in (("name", "NotTauCeti"), ("lakeDir", "/tmp/lake"),
                             ("fixedToolchain", True), ("packagesDir", "/elsewhere")):
            manifest = valid_release_manifest()
            manifest[field] = value
            with self.subTest(field=field):
                self.assertTrue(any(repr(field) in p for p in self.check(manifest)))

    def test_the_manifest_format_version_may_move_with_the_toolchain(self):
        # `version` is Lake's own manifest-format version, so the release commit's Lake
        # legitimately writes a different one from the base's.
        self.assertEqual(self.check(), [])

    def test_rejects_a_non_sha_release_rev(self):
        self.assertTrue(self.check(rev="master"))

    def test_rejects_unparseable_json(self):
        self.assertTrue(rc.check_manifest("{", dumps(BASE), dumps(MATHLIB), M))


class CommandLine(unittest.TestCase):
    def run_check(self, manifest, toolchain="leanprover/lean4:v4.33.0"):
        with tempfile.TemporaryDirectory() as directory:
            paths = {}
            for name, text in (("pr-manifest", dumps(manifest)),
                               ("pr-toolchain", toolchain),
                               ("base-manifest", dumps(BASE)),
                               ("mathlib-manifest", dumps(MATHLIB)),
                               ("mathlib-toolchain", "leanprover/lean4:v4.33.0")):
                paths[name] = os.path.join(directory, name)
                with open(paths[name], "w") as handle:
                    handle.write(text)
            return rc.main(["check", "--release", "v4.33.0", "--rev", M]
                           + [f"--{k}={v}" for k, v in paths.items()])

    def test_exit_zero_for_a_valid_release_commit(self):
        self.assertEqual(self.run_check(valid_release_manifest()), 0)

    def test_exit_one_for_an_invalid_one(self):
        manifest = valid_release_manifest()
        manifest["packages"][0]["rev"] = "9" * 40
        self.assertEqual(self.run_check(manifest), 1)


class ConstructorAgreement(unittest.TestCase):
    """The constructor's output must satisfy this independent verifier.

    Skipped until both land on main, because each is introduced by its own PR."""

    def test_toolchain_tags_output_passes_the_verifier(self):
        try:
            sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                            "pr_status"))
            import toolchain_tags as tt  # noqa: F401
        except ImportError:
            self.skipTest("scripts/toolchain_tags.py is not on this branch yet")
        derived = tt.derive_manifest(dumps(BASE), dumps(MATHLIB), M)
        self.assertEqual(rc.check_manifest(derived, dumps(BASE), dumps(MATHLIB), M), [])
        toolchain = tt.derive_toolchain("leanprover/lean4:v4.32.0", "v4.33.0")
        self.assertEqual(
            rc.check_toolchain(toolchain, "leanprover/lean4:v4.33.0", "v4.33.0"), [])


if __name__ == "__main__":
    unittest.main()
