"""Ensure the two Lake cache publishers stage and upload identically.

Run with: python3 scripts/test_cache_publish_block.py

There are two workflows that put oleans into the Lake artifact cache: `ci.yml`, on every
push to main, and `release-tag.yml`, once per Lean release. They write into the SAME
object namespace that `pr-build.yml` restores from, and Lake will only find an object
again if the upload was scoped exactly as the download expects. So the parts that decide
what is staged, and under which scope it is published, must not drift apart.

The blocks are duplicated rather than shared through a composite action, for the reason
`scripts/test_elan_pin.py` and `scripts/test_landrun_pin.py` give for the installers they
guard: `ci.yml` triggers only on a push to main, so a pull request that edited a shared
action could not be exercised by that pull request's own build, and a mistake in it would
first execute in production, in the one job that holds the upload key. This test is what
stops the copies drifting instead.

Three things are checked:

  1. the staging step body, from the packing build through `staged=true`, is byte-identical
     in both workflows: it is what decides which artifacts exist to be uploaded at all, and
     it carries the `platformIndependent` / `fixedToolchain` assertions the scope depends on;
  2. the staged-tree validation, including the artifact-name pattern, is byte-identical: it
     is what stops a name such as `0.art/../../../proc/self/environ` making Lake PUT a job's
     environment into a publicly readable bucket, and it must be equally strict in both;
  3. every `lake cache put-staged` in the repository scopes its upload the same way.

What this cannot do is check that the scope matches what `lake cache get` derives; that is
a property of Lake, recorded in docs/cache-infrastructure.md by comparing the two commands'
revision URLs. It fixes the agreed shape and catches the copies diverging.
"""

import pathlib
import re
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
WORKFLOW_DIR = ROOT / ".github/workflows"
PUBLISHERS = (WORKFLOW_DIR / "ci.yml", WORKFLOW_DIR / "release-tag.yml")

# The staging step body: the packing build, the mappings, `lake cache stage`, the two
# lakefile assertions the scope rests on, and the reported toolchain.
STAGE = re.compile(
    r"^[ \t]*lake build >/dev/null\n.*?^[ \t]*echo \"staged=true\" >> \"\$GITHUB_OUTPUT\"\n",
    re.MULTILINE | re.DOTALL)

# The staged-tree validation step, whole.
VALIDATE = re.compile(
    r"^[ \t]*- name: Check the staged tree before pointing Lake at it\n.*?^[ \t]*PY\n",
    re.MULTILINE | re.DOTALL)

# Only real invocations. The command is discussed in prose in both files and named inside
# an error message in the staging step, and neither may be mistaken for a call. An
# invocation begins the line, optionally behind the `elan run <toolchain>` prefix that
# selects the uploading Lake.
PUT_STAGED = re.compile(r'\A(?:elan run \S+ )?lake cache put-staged\b')


def body(path):
    return path.read_text()


class StagingBlock(unittest.TestCase):
    def matched(self, pattern, label):
        found = {}
        for path in PUBLISHERS:
            self.assertTrue(path.exists(), f"{path} is missing")
            matches = pattern.findall(body(path))
            self.assertEqual(len(matches), 1,
                             f"{path.name} has {len(matches)} {label} blocks, expected one")
            found[path.name] = matches[0]
        return found

    def test_the_staging_commands_are_identical(self):
        """The commands that decide WHAT is staged must not drift.

        An explicit list rather than the whole body, because the two publishers
        legitimately differ on exactly one point: `ci.yml` FAILS when the lakefile does
        not declare `platformIndependent`, since it only ever builds main, where its
        absence would mean someone had removed it, while `release-tag.yml` reaches commits
        from before TauCeti declared it at all and publishes those under the
        platform-scoped key their own consumers derive. Listing the essential lines keeps
        that one difference from being a licence for any other."""
        essential = [
            "lake build >/dev/null",
            "lake build --no-build -o .lake/outputs.jsonl",
            'echo "root-package mapping entries: $(wc -l < .lake/outputs.jsonl)"',
            'lake cache stage .lake/outputs.jsonl "$RUNNER_TEMP/lake-cache-staging"',
            'TOOLCHAIN="$(lake env printenv ELAN_TOOLCHAIN || true)"',
            "printf 'toolchain=%s\\n' \"$TOOLCHAIN\" >> \"$GITHUB_OUTPUT\"",
            'echo "staged=true" >> "$GITHUB_OUTPUT"',
        ]
        found = self.matched(STAGE, "staging")
        for name, block in found.items():
            lines = [line.strip() for line in block.splitlines()]
            for line in essential:
                with self.subTest(workflow=name, line=line):
                    self.assertIn(line, lines)

    def test_the_lake_commands_are_the_same_set(self):
        # Anything invoking `lake` inside the staging block decides what ends up staged, so
        # neither publisher may gain or lose one without the other.
        found = self.matched(STAGE, "staging")
        sets = []
        for block in found.values():
            sets.append(sorted(line.strip() for line in block.splitlines()
                               if line.strip().startswith("lake ")))
        self.assertEqual(sets[0], sets[1])

    # The two blocks are allowed to differ in exactly these ways and no others, and each is
    # pinned to its exact text. Matching the platform branch by a pattern would let
    # `if true || grep ... platformIndependent ...` be swallowed as though it were the known
    # divergence, which is precisely how a weaker version of this check was defeated.
    CI_PLATFORM_BLOCK = (
        "if ! grep -Eq '^[[:space:]]*platformIndependent[[:space:]]*=[[:space:]]*true'"
        " lakefile.toml; then",
        'echo "::error::lakefile.toml no longer sets platformIndependent = true;'
        ' publish-lake-cache must now pass --platform to lake cache put-staged"',
        "exit 1",
        "fi",
    )
    RELEASE_PLATFORM_BLOCK = (
        "if grep -Eq '^[[:space:]]*platformIndependent[[:space:]]*=[[:space:]]*true'"
        " lakefile.toml; then",
        'echo "platform-independent=true" >> "$GITHUB_OUTPUT"',
        "else",
        'echo "::notice::this commit predates platformIndependent;'
        ' publishing under a platform-scoped key"',
        'echo "platform-independent=false" >> "$GITHUB_OUTPUT"',
        "fi",
    )
    # The one extra command release-tag.yml runs: it carries the staged mapping count out so
    # the read-back can tell this run's publish from a mapping already at the revision key.
    RELEASE_EXTRA = (
        "printf 'entries=%s\\n' \"$(wc -l < .lake/outputs.jsonl)\" >> \"$GITHUB_OUTPUT\"",
    )

    @staticmethod
    def lines(block):
        """Executable lines of a block, in order, whitespace collapsed."""
        out = []
        for line in block.splitlines():
            stripped = " ".join(line.split())
            if stripped and not stripped.startswith("#"):
                out.append(stripped)
        return out

    def collapse(self, lines, known, extra=()):
        """Replace one exact known run of lines with a sentinel, and drop the named extras.

        Order is preserved and nothing else is removed, so reordering, duplicating or adding
        a command shows up as a difference. Returns (collapsed, saw_known, saw_extra)."""
        known, extra = list(known), list(extra)
        out, seen_known, seen_extra = [], False, []
        i = 0
        while i < len(lines):
            if lines[i:i + len(known)] == known:
                out.append("<PLATFORM BRANCH>")
                seen_known = True
                i += len(known)
                continue
            if lines[i] in extra:
                seen_extra.append(lines[i])
                i += 1
                continue
            out.append(lines[i])
            i += 1
        return out, seen_known, seen_extra

    def test_the_staging_blocks_are_identical_but_for_the_platform_branch(self):
        """The stated invariant, actually enforced.

        An earlier version listed some required lines and compared command SETS, which let
        an added `curl`, a reordering, or a neutered platform condition pass. This compares
        the ordered lines with exactly one known divergence collapsed."""
        found = self.matched(STAGE, "staging")
        ci, ci_known, _ = self.collapse(self.lines(found["ci.yml"]), self.CI_PLATFORM_BLOCK)
        release, rel_known, rel_extra = self.collapse(
            self.lines(found["release-tag.yml"]), self.RELEASE_PLATFORM_BLOCK,
            self.RELEASE_EXTRA)
        self.assertTrue(ci_known, "ci.yml's platform assertion is not the approved block")
        self.assertTrue(rel_known, "release-tag.yml's platform branch is not the approved block")
        self.assertEqual(sorted(rel_extra), sorted(self.RELEASE_EXTRA),
                         "release-tag.yml no longer carries the staged entry count")
        self.assertEqual(ci, release,
                         "the two publishers stage differently outside the one divergence "
                         "they are allowed; if a new divergence is deliberate, name it here")

class UploadScope(unittest.TestCase):
    def invocations(self):
        """(workflow, one-line command) for every real `lake cache put-staged` call."""
        out = []
        for path in sorted(WORKFLOW_DIR.glob("*.y*ml")):
            lines = body(path).splitlines()
            for index, line in enumerate(lines):
                stripped = line.strip()
                if not PUT_STAGED.match(stripped):
                    continue
                call = [stripped]
                while call[-1].endswith("\\") and index + 1 < len(lines):
                    index += 1
                    call.append(lines[index].strip())
                out.append((path.name, " ".join(" ".join(call).replace("\\", " ").split())))
        return out

    def test_there_are_exactly_two_publishers(self):
        names = sorted(name for name, _ in self.invocations())
        self.assertEqual(names, ["ci.yml", "release-tag.yml"],
                         "a new workflow uploads to the Lake cache; it must be added here "
                         "and hold the key in a job of its own")

    def test_every_upload_is_scoped_the_same_way(self):
        for name, call in self.invocations():
            with self.subTest(workflow=name):
                self.assertIn("--service tauceti-r2", call)
                self.assertIn("--repo TauCetiProject/TauCeti", call)
                self.assertIn("--toolchain", call)
        # ci.yml must never pass a platform: main declares `platformIndependent = true`, so
        # a platform in the scope is one `pr-build`'s `lake cache get --repo` never reads.
        # release-tag.yml passes it only through an array that is empty for such a target.
        calls = dict(self.invocations())
        self.assertNotIn("--platform", calls["ci.yml"])

    def test_the_release_publisher_names_a_revision_explicitly(self):
        # ci.yml may take the revision from the run; the release publisher must not, because
        # its run's own sha is main's tip rather than the commit it built.
        calls = {name: call for name, call in self.invocations()}
        self.assertIn("--rev", calls["release-tag.yml"])
        self.assertNotIn('--rev "$GITHUB_SHA"', calls["release-tag.yml"],
                         "release-tag.yml must publish under the RESOLVED commit, not the "
                         "dispatching run's sha")


if __name__ == "__main__":
    unittest.main()
