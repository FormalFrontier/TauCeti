"""Snapshot and compare the compiled outputs of two builds of the same commit.

Run with: python3 scripts/compare-build-outputs.py manifest BUILD_DIR OUT_FILE
          python3 scripts/compare-build-outputs.py compare FRESH_MANIFEST REFERENCE_MANIFEST

`manifest` records SHA-256 of every build artifact under BUILD_DIR. `compare` checks that two
such manifests agree: every artifact must appear in both at the same relative path with the
same digest. A difference means the cache handed a build something a clean compile of the same
sources does not produce.

The comparison is on SHA-256 of the file contents, deliberately not on Lake's own recorded
output hashes. `Lake.Hash` is a single UInt64 and explicitly not cryptographic, so comparing
Lake's hashes would inherit the very weakness this check exists to cover.

Splitting snapshot from compare is what lets the caller hash the clean build BEFORE anything
else runs on that machine. It also keeps the two sides symmetric: a manifest must be taken
right after `lake build`, since later commands such as `lake exe axioms` add root-package
outputs on one side only and would otherwise read as divergence.

SUFFIXES is every artifact Lake produces for a module, not just `.olean`. A cache entry can
differ in `Foo.olean.private` or in generated C while `Foo.olean` matches, and private and
server oleans affect what later imports see.

Statuses written to $GITHUB_OUTPUT as `status=`:

  agree         every artifact matched
  disagree      a path or a digest differed, in either direction
  inconclusive  either manifest was empty, so there was nothing to compare

`inconclusive` is a reportable outcome, not a pass. `compare` exits 0 in every case: the caller
decides what to do, and the from-source build's own success must never depend on this script.
"""

import hashlib
import os
import sys

SUFFIXES = (
    ".olean", ".olean.private", ".olean.server",
    ".ilean", ".ir", ".ir.sig", ".c", ".bc",
)


def manifest(root):
    """Return {relative path: sha256} for every build artifact under `root`."""
    out = {}
    for dirpath, _dirnames, filenames in os.walk(root):
        for name in filenames:
            if not name.endswith(SUFFIXES):
                continue
            full = os.path.join(dirpath, name)
            h = hashlib.sha256()
            with open(full, "rb") as f:
                for chunk in iter(lambda: f.read(1 << 20), b""):
                    h.update(chunk)
            out[os.path.relpath(full, root)] = h.hexdigest()
    return out


def read_manifest(path):
    out = {}
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line:
                continue
            digest, _, rel = line.partition("  ")
            out[rel] = digest
    return out


def do_manifest(build_dir, out_file):
    entries = manifest(build_dir)
    with open(out_file, "w", encoding="utf-8") as f:
        for rel in sorted(entries):
            f.write(f"{entries[rel]}  {rel}\n")
    print(f"recorded {len(entries)} artifacts from {build_dir} into {out_file}")
    return 0


def do_compare(fresh_path, reference_path):
    fresh, reference = read_manifest(fresh_path), read_manifest(reference_path)

    only_fresh = sorted(set(fresh) - set(reference))
    only_reference = sorted(set(reference) - set(fresh))
    differing = sorted(k for k in set(fresh) & set(reference) if fresh[k] != reference[k])

    print(f"clean-build artifacts:  {len(fresh)}")
    print(f"cached-build artifacts: {len(reference)}")
    print(f"only in clean:          {len(only_fresh)}")
    print(f"only in cached:         {len(only_reference)}")
    print(f"differing bytes:        {len(differing)}")

    if not fresh or not reference:
        status = "inconclusive"
        detail = f"nothing to compare (clean {len(fresh)}, cached {len(reference)})"
    elif only_fresh or only_reference or differing:
        status = "disagree"
        detail = (f"{len(differing)} differing, {len(only_fresh)} only in the clean build, "
                  f"{len(only_reference)} only in the cached build")
    else:
        status = "agree"
        detail = f"{len(fresh)} artifacts identical"

    for label, items in (("differing", differing),
                         ("only in the clean build", only_fresh),
                         ("only in the cached build", only_reference)):
        for path in items[:10]:
            print(f"  {label}: {path}")
        if len(items) > 10:
            print(f"  ... and {len(items) - 10} more {label}")

    print(f"status: {status} ({detail})")
    step_output = os.environ.get("GITHUB_OUTPUT")
    if step_output:
        with open(step_output, "a", encoding="utf-8") as f:
            f.write(f"status={status}\n")
            f.write(f"detail={detail}\n")
    return 0


def main(argv):
    if len(argv) == 4 and argv[1] == "manifest":
        return do_manifest(argv[2], argv[3])
    if len(argv) == 4 and argv[1] == "compare":
        return do_compare(argv[2], argv[3])
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
