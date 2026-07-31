#!/usr/bin/env python3
"""Tests for the review-bot-only lakefile pin validator."""

from __future__ import annotations

import json
import pathlib
import tempfile

from check_bot_lakefile import ValidationError, validate


OLD = "1" * 40
NEW = "2" * 40
BASE = '''name = "TauCeti"

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "master"

[[lean_lib]]
name = "TauCeti"
'''


def _case(pr_text: str, *, manifest_rev: str = NEW, input_rev: str = NEW):
    tmp = tempfile.TemporaryDirectory()
    root = pathlib.Path(tmp.name)
    base = root / "base.toml"
    pr = root / "pr.toml"
    manifest = root / "lake-manifest.json"
    base.write_text(BASE)
    pr.write_text(pr_text)
    manifest.write_text(json.dumps({"packages": [{
        "name": "mathlib", "type": "git", "rev": manifest_rev, "inputRev": input_rev,
    }]}))
    return tmp, base, pr, manifest


def _valid_text() -> str:
    return BASE.replace('rev = "master"', f'rev = "{NEW}"')


def test_accepts_the_exact_bot_pin():
    tmp, base, pr, manifest = _case(_valid_text())
    with tmp:
        assert validate(base, pr, manifest) == NEW


def test_accepts_depinning_back_to_master_with_a_forward_manifest_pin():
    pinned_base = BASE.replace('rev = "master"', f'rev = "{OLD}"')
    tmp, base, pr, manifest = _case(BASE, manifest_rev=NEW, input_rev="master")
    with tmp:
        base.write_text(pinned_base)
        assert validate(base, pr, manifest) == "master"


def test_rejects_any_second_lakefile_change():
    text = _valid_text().replace('name = "TauCeti"', 'name = "Other"', 1)
    tmp, base, pr, manifest = _case(text)
    with tmp:
        try:
            validate(base, pr, manifest)
        except ValidationError as exc:
            assert "exactly one" in str(exc)
        else:
            raise AssertionError("accepted a second lakefile change")


def test_rejects_a_branch_or_tag_instead_of_an_immutable_sha():
    tmp, base, pr, manifest = _case(BASE.replace('rev = "master"', 'rev = "stable"'),
                                    manifest_rev="stable", input_rev="stable")
    with tmp:
        try:
            validate(base, pr, manifest)
        except ValidationError as exc:
            assert "neither master nor a 40-hex" in str(exc)
        else:
            raise AssertionError("accepted a mutable revision")


def test_rejects_manifest_revision_mismatch():
    tmp, base, pr, manifest = _case(_valid_text(), manifest_rev=OLD)
    with tmp:
        try:
            validate(base, pr, manifest)
        except ValidationError as exc:
            assert "does not match manifest" in str(exc)
        else:
            raise AssertionError("accepted a mismatched manifest revision")


def test_rejects_a_non_exact_manifest_input():
    tmp, base, pr, manifest = _case(_valid_text(), input_rev="master")
    with tmp:
        try:
            validate(base, pr, manifest)
        except ValidationError as exc:
            assert "inputRev" in str(exc)
        else:
            raise AssertionError("accepted a non-exact manifest inputRev")


def test_rejects_editing_another_dependency_rev():
    other = '''\n[[require]]\nname = "other"\ngit = "https://example.com/other"\nrev = "stable"\n'''
    tmp, base, pr, manifest = _case(BASE + other)
    with tmp:
        base.write_text(BASE + other)
        pr.write_text((BASE + other).replace('rev = "stable"', f'rev = "{NEW}"'))
        try:
            validate(base, pr, manifest)
        except ValidationError as exc:
            assert "not Mathlib" in str(exc)
        else:
            raise AssertionError("accepted another dependency's rev change")


def test_rejects_adding_or_removing_a_lakefile_line():
    for text in (_valid_text() + "# extra\n", _valid_text().replace('name = "TauCeti"\n', "", 1)):
        tmp, base, pr, manifest = _case(text)
        with tmp:
            try:
                validate(base, pr, manifest)
            except ValidationError as exc:
                assert "exactly one existing line" in str(exc)
            else:
                raise AssertionError("accepted a lakefile line addition/removal")


def run():
    tests = [value for name, value in sorted(globals().items())
             if name.startswith("test_") and callable(value)]
    for test in tests:
        test()
        print(f"ok  {test.__name__}")
    print(f"\n{len(tests)} passed")


if __name__ == "__main__":
    run()
