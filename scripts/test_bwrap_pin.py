"""Ensure every workflow that runs code under bwrap trusts the same binary.

Run with: python3 scripts/test_bwrap_pin.py

pr-build.yml sandboxes untrusted PR sources; pr-profile.yml measures them; nightly-verify.yml
sandboxes a cache-restored build that imports the artifacts it is judging. All three pin the
bubblewrap package, its .deb's SHA-256 and the SHA-256 of the binary that .deb installs, and
any of them would be weakened by trusting a different binary than the others.

The pin is deliberately duplicated rather than shared through a composite action: pr-build.yml
sits on the merge queue's critical path and runs from the base definition under
pull_request_target, so a shared action could not be exercised by the PR that introduced it.
This test is what stops the copies drifting.

The `.lake` normalisation is checked here too, because the pinned version depends on it:
noble ships bubblewrap 0.9.0, which predates the fix for GHSA-pxhw-h44j-8pfx, and what keeps
that safe is that no candidate-controlled symlink survives to be followed. Pinning noble's own
package is what stops this pin expiring; a package from a suite the runner does not track is
deleted from the pool as soon as Ubuntu uploads a newer one.

The AppArmor profile is checked here too. Ubuntu 24.04 denies unprivileged user namespaces, so
without the profile bwrap cannot build its sandbox at all — and a workflow that installed bwrap
but not the profile would fail rather than silently run unconfined, which is the right way
round, but the self-test is what actually guarantees that.
"""

import pathlib
import re
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
WORKFLOWS = (
    ROOT / ".github/workflows/pr-build.yml",
    ROOT / ".github/workflows/pr-profile.yml",
    ROOT / ".github/workflows/nightly-verify.yml",
)
VER = re.compile(r"^\s*BWRAP_VER:\s*([0-9][0-9A-Za-z.\-+~:]*)\s*$", re.MULTILINE)
DEB_SHA = re.compile(r"^\s*BWRAP_DEB_SHA256:\s*([0-9a-f]{64})\s*$", re.MULTILINE)
BIN_SHA = re.compile(r"^\s*BWRAP_SHA256:\s*([0-9a-f]{64})\s*$", re.MULTILINE)


class BwrapPin(unittest.TestCase):
    def test_every_sandboxing_workflow_pins_the_same_bwrap(self):
        seen = {}
        for workflow in WORKFLOWS:
            text = workflow.read_text()
            vers, debs, bins = VER.findall(text), DEB_SHA.findall(text), BIN_SHA.findall(text)
            self.assertEqual(len(vers), 1, f"expected one BWRAP_VER in {workflow.name}")
            self.assertEqual(len(debs), 1, f"expected one BWRAP_DEB_SHA256 in {workflow.name}")
            self.assertEqual(len(bins), 1, f"expected one BWRAP_SHA256 in {workflow.name}")
            seen[workflow.name] = (vers[0], debs[0], bins[0])
        distinct = set(seen.values())
        self.assertEqual(
            len(distinct), 1,
            "workflows disagree on which bwrap to trust: "
            + ", ".join(f"{name} pins {pin}" for name, pin in sorted(seen.items())),
        )

    def assertContains(self, needle, text, workflow):
        # assertIn would print the whole workflow on failure.
        self.assertTrue(needle in text, f"{workflow}: missing {needle!r}")

    def assertOmits(self, needle, text, workflow):
        self.assertTrue(needle not in text, f"{workflow}: unexpectedly contains {needle!r}")

    def test_every_sandboxing_workflow_verifies_both_checksums(self):
        # A pin that is downloaded but never checked is not a pin. The binary is checked as
        # well as the .deb, because dpkg is what decides what actually lands on disk.
        for workflow in WORKFLOWS:
            with self.subTest(workflow=workflow.name):
                text = workflow.read_text()
                self.assertContains('echo "${BWRAP_DEB_SHA256}  bwrap.deb" | sha256sum -c -', text, workflow.name)
                self.assertContains('echo "${BWRAP_SHA256}  /usr/bin/bwrap" | sha256sum -c -', text, workflow.name)

    def test_every_sandboxing_workflow_installs_the_apparmor_profile(self):
        # Without it, bwrap cannot create a user namespace on Ubuntu 24.04. Granting the
        # capability to this one binary is the point: clearing
        # kernel.apparmor_restrict_unprivileged_userns would lift it runner-wide.
        for workflow in WORKFLOWS:
            with self.subTest(workflow=workflow.name):
                text = workflow.read_text()
                self.assertContains("sudo apparmor_parser -r /etc/apparmor.d/bwrap", text, workflow.name)
                # The profile grants the capability to one binary; the sysctl would lift the
                # restriction for everything on the runner. Naming it in a comment is fine.
                self.assertOmits("sysctl -w kernel.apparmor_restrict_unprivileged_userns", text, workflow.name)

    def test_every_sandboxing_workflow_self_tests_before_running_candidate_code(self):
        # `--unshare-all` expands to `--unshare-user-try`, which skips the user namespace
        # rather than failing when it cannot be created. Comparing the namespace inside the
        # sandbox against the host's is what catches that silent degradation.
        for workflow in WORKFLOWS:
            with self.subTest(workflow=workflow.name):
                text = workflow.read_text()
                self.assertContains("readlink /proc/self/ns/user", text, workflow.name)
                self.assertContains('[ "$sb_ns" = "$host_ns" ]', text, workflow.name)
                self.assertContains("refusing to run candidate code", text, workflow.name)

    def test_every_policy_hardens_the_synthetic_root(self):
        # `--tmpfs /` leaves a writable synthetic root, including the directories bwrap creates
        # to hang the binds off. Without `--remount-ro /` candidate code can plant an executable
        # under $HOME and win the PATH lookup for the audits that run after the build.
        for workflow in WORKFLOWS:
            with self.subTest(workflow=workflow.name):
                text = workflow.read_text()
                for policy in self._policies(text):
                    self.assertIn("--remount-ro /", policy)
                    # bwrap is PID 1 of the sandbox and keeps its own environment, so it has to
                    # be started without one (containers/bubblewrap#725).
                    self.assertTrue(policy.startswith("env -i /usr/bin/bwrap"), policy[:60])
                    # `--unshare-all` would use the "try" form for the user namespace.
                    self.assertIn("--unshare-user ", policy)
                    self.assertNotIn("--unshare-all", policy)
                    # A PATH the sandbox can write is the other half of the hijack above.
                    self.assertNotIn("$HOME/.local/bin", policy)

    def _policies(self, text):
        """Every bwrap invocation in a workflow, joined back into one line each."""
        out, cur = [], None
        for line in text.splitlines():
            stripped = line.strip()
            if cur is None and stripped.startswith("env -i /usr/bin/bwrap"):
                cur = [stripped]
            elif cur is not None:
                cur.append(stripped)
            if cur is not None and not stripped.endswith("\\"):
                out.append(" ".join(x.rstrip("\\").strip() for x in cur))
                cur = None
        assert out, "no bwrap policy found"
        return out

    def test_the_self_test_runs_before_any_candidate_code(self):
        # Ordering, not mere presence: a self-test placed after the build would satisfy a
        # substring search and prove nothing.
        import yaml
        for workflow in WORKFLOWS:
            with self.subTest(workflow=workflow.name):
                doc = yaml.safe_load(workflow.read_text())
                names = [str(s.get("name", "")) for job in doc["jobs"].values()
                         for s in job.get("steps", [])]
                install = [i for i, n in enumerate(names) if "Install bubblewrap" in n]
                sandboxed = [i for i, n in enumerate(names)
                             if "under bwrap" in n or "heartbeats" in n or "under bwrap," in n]
                self.assertTrue(install, "no bubblewrap install step")
                for s in sandboxed:
                    self.assertTrue(any(i < s for i in install),
                                    f"{workflow.name}: sandboxed step {names[s]!r} precedes the self-test")

    def test_lake_is_normalised_before_anything_touches_it(self):
        """The step that makes the pinned bubblewrap version safe.

        Two reasons, expiring differently. The pinned bubblewrap is noble's 0.9.0, which
        follows a symlink committed at `.lake` while creating the sandbox mount point
        (GHSA-pxhw-h44j-8pfx); upstream fixed that in 0.12.0, so that reason retires when the
        pin can move. The other does not: `mkdir -p` and the trusted Mathlib cache restore
        follow the same symlink themselves, before any sandbox exists, and no bubblewrap
        version fixes that. Either way the step has to exist and has to come before every other
        step that names a candidate `.lake`.
        """
        import yaml
        for workflow in WORKFLOWS:
            with self.subTest(workflow=workflow.name):
                doc = yaml.safe_load(workflow.read_text())
                steps = [s for job in doc["jobs"].values() for s in job.get("steps", [])]
                names = [str(s.get("name", "")) for s in steps]
                norm = [i for i, n in enumerate(names) if n.startswith("Normalise")]
                self.assertTrue(norm, f"{workflow.name}: no .lake normalisation step")
                first_norm = min(norm)
                # It must unlink rather than follow, and must verify what it left behind.
                body = str(steps[first_norm].get("run", ""))
                self.assertIn("rm -rf", body)
                self.assertNotIn("/.lake/", body.replace("mkdir -p", ""))  # no trailing slash
                self.assertIn("-L", body)  # asserts the result is not a symlink
                # Nothing earlier may name a candidate .lake.
                for i, step in enumerate(steps[:first_norm]):
                    blob = yaml.safe_dump(step)
                    for tree in ("pr/.lake", "head/.lake", "base/.lake", "reference/.lake"):
                        self.assertNotIn(
                            tree, blob,
                            f"{workflow.name}: step {names[i]!r} touches {tree} "
                            f"before it is normalised")

    def test_no_workflow_still_invokes_landrun(self):
        # Comments may still name landrun to explain what changed and why; what must be gone
        # is any call to it, and any Landlock-shaped flag left behind in a policy.
        for workflow in WORKFLOWS:
            with self.subTest(workflow=workflow.name):
                text = workflow.read_text()
                self.assertOmits("landrun --", text, workflow.name)
                self.assertOmits("Zouuup/landrun", text, workflow.name)
                for flag in ("--rox ", "--rwx "):
                    self.assertOmits(flag, text, workflow.name)


if __name__ == "__main__":
    unittest.main()
