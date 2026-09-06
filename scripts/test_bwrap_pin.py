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

    # Which trees each workflow checks out and must normalise before touching.
    TREES = {
        "pr-build.yml": ("pr",),
        "pr-profile.yml": ("base", "head"),
        "nightly-verify.yml": ("reference",),
    }

    # Any bwrap invocation must look exactly like this. Anything else is either an unsafe
    # policy or a form this test cannot reason about; both must fail.
    SAFE_PREFIX = "env -i /usr/bin/bwrap"
    BWRAP_TOKEN = re.compile(
        r"(?:^|[;&|(]\s*|\bthen\s+|\belse\s+|--\s+)((?:env -i\s+)?(?:/usr/bin/)?bwrap)\s")

    @staticmethod
    def _is_prose(stripped):
        # Comments and the quoted arguments of the printf failure message both talk about
        # bwrap without invoking it.
        return stripped.startswith("#") or stripped.startswith("'") or stripped.startswith('"')

    def _invocations(self, text):
        """Every bwrap invocation in a workflow, each joined back into a single line."""
        lines, out, cur = text.splitlines(), [], None
        for line in lines:
            stripped = line.strip()
            if cur is None and not self._is_prose(stripped) \
                    and self.BWRAP_TOKEN.match(stripped):
                cur = [stripped]
            elif cur is not None:
                cur.append(stripped)
            if cur is not None and not stripped.endswith("\\"):
                out.append(" ".join(x.rstrip("\\").strip() for x in cur))
                cur = None
        return out

    def test_every_bwrap_invocation_uses_the_safe_form(self):
        # The earlier version of this test only looked at lines already beginning with the
        # safe prefix, so rewriting a policy to bare `bwrap` removed it from the test rather
        # than failing it. Now every invocation has to be accounted for.
        for workflow in WORKFLOWS:
            with self.subTest(workflow=workflow.name):
                text = workflow.read_text()
                invocations = self._invocations(text)
                self.assertTrue(invocations, f"{workflow.name}: no bwrap invocation found")
                for inv in invocations:
                    if inv.startswith("/usr/bin/bwrap --version"):
                        continue  # the post-install smoke check, which runs no policy
                    self.assertTrue(
                        inv.startswith(self.SAFE_PREFIX),
                        f"{workflow.name}: bwrap invocation not in the safe form: {inv[:110]}")
                    for required in ("--tmpfs /", "--remount-ro /", "--unshare-user ",
                                     "--disable-userns"):
                        self.assertIn(required, inv, f"{workflow.name}: {inv[:80]}")
                    self.assertNotIn("--unshare-all", inv)
                    self.assertNotIn("$HOME/.local/bin", inv)

    def test_lake_is_the_only_destination_inside_a_candidate_tree(self):
        # The whole argument for pinning a bubblewrap older than 0.12.0 is that `.lake` is the
        # only place bwrap creates a mount point inside content the candidate controls. A
        # second such destination would silently invalidate it.
        dest = re.compile(r"--(?:ro-)?bind \S+ \"?(\$PWD/[A-Za-z0-9_.-]+[^\"\s]*)")
        for workflow in WORKFLOWS:
            with self.subTest(workflow=workflow.name):
                for inv in self._invocations(workflow.read_text()):
                    if not inv.startswith(self.SAFE_PREFIX):
                        continue
                    dests = [d.strip('"') for d in dest.findall(inv)]
                    roots = [d for d in dests if "/" not in d[len("$PWD/"):]]
                    for d in dests:
                        under = [r for r in roots if d.startswith(r + "/")]
                        if under:
                            self.assertTrue(
                                d == under[0] + "/.lake",
                                f"{workflow.name}: {d} is a bwrap destination inside the "
                                f"candidate tree {under[0]}, but only <tree>/.lake may be. "
                                f"Either normalise it too or move the pin to bubblewrap "
                                f">= 0.12.0.")

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
        version fixes that.

        Checked per job, per tree, against the exact commands, because a test that merely
        finds a step whose name starts with "Normalise" is satisfied by a step that does
        nothing.
        """
        import yaml
        for workflow in WORKFLOWS:
            trees = self.TREES[workflow.name]
            doc = yaml.safe_load(workflow.read_text())
            for job_name, job in doc["jobs"].items():
                steps = job.get("steps") or []
                if not any(str(s.get("with", {}).get("path", "")) in trees for s in steps):
                    continue  # this job checks nothing out
                for tree in trees:
                    with self.subTest(workflow=workflow.name, job=job_name, tree=tree):
                        checkout = [i for i, s in enumerate(steps)
                                    if str((s.get("with") or {}).get("path", "")) == tree]
                        self.assertTrue(checkout, f"no checkout with path: {tree}")
                        norm = [i for i, s in enumerate(steps)
                                if f"rm -rf {tree}/.lake" in str(s.get("run", ""))]
                        self.assertTrue(norm, f"nothing runs `rm -rf {tree}/.lake`")
                        self.assertGreater(min(norm), min(checkout),
                                           f"{tree}/.lake is normalised before it is checked out")
                        body = str(steps[min(norm)].get("run", ""))
                        self.assertIn(f"mkdir -p {tree}/.lake", body)
                        self.assertIn(f"[ -L {tree}/.lake ]", body)
                        self.assertNotIn(f"rm -rf {tree}/.lake/", body)  # would follow the link
                        # Nothing between checkout and normalisation may name it.
                        for i in range(min(checkout) + 1, min(norm)):
                            self.assertNotIn(
                                f"{tree}/.lake", yaml.safe_dump(steps[i]),
                                f"step {steps[i].get('name')!r} touches {tree}/.lake "
                                f"before it is normalised")

    def test_measure_py_builds_the_same_policy(self):
        # scripts/perf/measure.py assembles the policy in Python, so the workflow-shaped
        # checks above cannot see it.
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "measure", ROOT / "scripts" / "perf" / "measure.py")
        measure = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(measure)
        root = pathlib.Path("/w/head")
        argv = measure.sandbox_command(root, "/usr/bin/bwrap", pathlib.Path("/w/wd"), ["M"])
        self.assertEqual(argv[:3], ["/usr/bin/env", "-i", "/usr/bin/bwrap"],
                         "bwrap must start with an empty environment; it is PID 1 of the "
                         "sandbox and keeps its own env at /proc/1/environ")
        joined = " ".join(argv)
        for required in ("--tmpfs /", "--remount-ro /", "--unshare-user", "--disable-userns",
                         "--die-with-parent", "--new-session"):
            self.assertIn(required, joined)
        self.assertNotIn("--unshare-all", joined)
        # The only writable bind, and the only destination inside the candidate tree.
        binds = [(argv[i], argv[i + 1], argv[i + 2]) for i, a in enumerate(argv)
                 if a in ("--bind", "--ro-bind")]
        inside = [d for _, _, d in binds if d.startswith(str(root) + "/")]
        self.assertEqual(inside, [str(root / ".lake")], f"unexpected destinations: {inside}")
        self.assertEqual([d for k, _, d in binds if k == "--bind"], [str(root / ".lake")])
        path = argv[argv.index("PATH", argv.index("--setenv")) + 1]
        self.assertNotIn(".local", path, "a sandbox-writable directory on PATH")

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
