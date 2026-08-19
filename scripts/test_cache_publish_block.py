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

    def test_the_staging_body_is_identical(self):
        found = self.matched(STAGE, "staging")
        first, second = list(found.values())
        self.assertEqual(first, second,
                         "ci.yml and release-tag.yml stage differently; the upload scope and "
                         "the set of staged artifacts must be decided the same way in both")

    def test_the_staged_tree_validation_is_identical(self):
        found = self.matched(VALIDATE, "staged-tree validation")
        first, second = list(found.values())
        self.assertEqual(first, second,
                         "the staged-tree check differs between the publishers; the weaker "
                         "one decides what an attacker-chosen artifact name can do")

    def test_the_validation_keeps_the_artifact_name_pattern(self):
        # Named explicitly, so relaxing the pattern cannot pass merely by relaxing it in
        # both copies at once.
        for path in PUBLISHERS:
            self.assertIn(r"\A[0-9A-Za-z]+(\.[0-9A-Za-z]+)*\Z", body(path), path.name)


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
                # `platformIndependent = true` is what makes Lake leave the platform out of
                # the scope, and the staging step asserts it. Passing --platform here would
                # publish under a scope pr-build's `lake cache get` never reads.
                self.assertNotIn("--platform", call)

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
