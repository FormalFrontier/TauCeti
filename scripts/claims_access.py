#!/usr/bin/env python3
"""Keep the shared claim namespace open to everyone who has landed a PR here, and sweep dead leases.

Workers run by different people must not spend two subscriptions on the same job, so before starting
one they take a lease: a `refs/tauceti-claims/<key>` ref, acquired by compare-and-swap, in a repository
every worker can push to. That repository is TauCetiProject/tauceti-claims, and it holds nothing else:
no code, no Actions, no relationship to this one. Coordinating workers must never need write access to
the library itself, which is the whole reason the leases do not live here.

So somebody has to be let in, and this decides who: the author of any merged pull request in this
repository. A maintainer looked at their work and took it, which is a better statement than org
membership and is already recorded on GitHub, so there is no list to keep. A worker whose operator has
not landed anything yet is not stuck waiting — it claims in its own fork until then, and so still
coordinates with the rest of its own fleet.

  grant  Invite every merged-PR author who is not already a collaborator or already invited. Grants
         are monotone: nothing is revoked automatically, because a quiet operator silently losing
         coordination is a confusing thing to debug from the worker side. Remove abuse by hand.
  sweep  Delete leases that expired more than SWEEP_GRACE_MINUTES ago. Releasing a lease deletes it,
         so these are the leavings of workers that died holding one; the grace period keeps the sweep
         clear of a live takeover, which is itself a compare-and-swap.

Reconciling (rather than reacting to a merge event) is what makes this self-healing: a missed webhook,
a failed API call, or an invitation that expired unaccepted after seven days is simply picked up on the
next run.

Env: GH_TOKEN (reads merged PRs here), CLAIMS_TOKEN (administers the claims repo: `Administration:
write` to invite, `Contents: write` to sweep), REPO (owner/name), optional CLAIMS_REPO, DRY_RUN=1,
SWEEP_GRACE_MINUTES.
"""

import json
import os
import subprocess
import sys
import time

REPO = os.environ.get("REPO", "")
GH_TOKEN = os.environ.get("GH_TOKEN", "")
CLAIMS_TOKEN = os.environ.get("CLAIMS_TOKEN", "")
CLAIMS_REPO = os.environ.get("CLAIMS_REPO", "TauCetiProject/tauceti-claims")
DRY_RUN = os.environ.get("DRY_RUN") == "1"
# A lease is swept only this long AFTER it expired. Taking over an expired lease is a CAS, so a
# worker may legitimately be reviving one at the moment we look at it; the grace period means the
# sweep cannot race that and delete a lease somebody is actively holding.
SWEEP_GRACE_MINUTES = int(os.environ.get("SWEEP_GRACE_MINUTES", "60"))
NS = "tauceti-claims"


def gh(args, token, check=True):
    """Run `gh` with an explicit token: this script holds two, and they are not interchangeable."""
    p = subprocess.run(["gh", *args], capture_output=True, text=True, env={**os.environ, "GH_TOKEN": token})
    if check and p.returncode != 0:
        raise RuntimeError(f"gh {' '.join(args)} failed: {(p.stderr or p.stdout).strip()}")
    return p


def gh_lines(args, token):
    """Lines from a `--paginate`d `gh api`. The filter must emit one record per LINE, not an array:
    with --paginate, gh runs the jq filter per page and concatenates, so an array filter yields
    `[...][...]` across pages, which is not JSON and would silently lose everyone past the first."""
    return [line.strip() for line in gh(args, token).stdout.splitlines() if line.strip()]


def human_authors(prs):
    """The distinct human authors among these PRs. Bots are excluded: the review and bump machinery
    opens PRs of its own, and no automation coordinates through the claim namespace. A deleted
    account arrives with no login and is skipped."""
    authors = set()
    for pr in prs or []:
        author = pr.get("author") or {}
        login = (author.get("login") or "").strip()
        if login and not author.get("is_bot") and not login.endswith("[bot]"):
            authors.add(login)
    return authors


def is_sweepable(lease_json, cutoff):
    """Is this lease expired long enough to delete? A lease we cannot read or parse is left alone:
    an unfamiliar ref in this namespace is not ours to delete."""
    try:
        expires = (json.loads(lease_json) or {}).get("expires_at")
    except (json.JSONDecodeError, TypeError, AttributeError):
        return False
    if not isinstance(expires, (int, float)) or isinstance(expires, bool):
        return False
    return 0 < expires <= cutoff


def merged_pr_authors():
    out = gh(["pr", "list", "--repo", REPO, "--state", "merged", "--limit", "5000", "--json", "author"], GH_TOKEN)
    return human_authors(json.loads(out.stdout or "[]"))


def already_admitted():
    """Logins that already have access, or have been asked: direct collaborators plus people who have
    not clicked yet (workers accept their own invitation, but an operator who has not started one
    since the grant still has it pending).

    This does NOT see people whose access comes from the organization. The collaborators endpoint
    resolves those only for a caller that can read org membership, and this App is installed on one
    repository and has no organization permissions at all, by design. `has_access` covers them."""
    collaborators = gh_lines(
        ["api", "--paginate", f"/repos/{CLAIMS_REPO}/collaborators?per_page=100", "--jq", ".[].login"],
        CLAIMS_TOKEN,
    )
    invitations = gh_lines(
        ["api", "--paginate", f"/repos/{CLAIMS_REPO}/invitations?per_page=100", "--jq", ".[].invitee.login"],
        CLAIMS_TOKEN,
    )
    return set(collaborators) | set(invitations)


def has_access(login):
    """Can this login already push, however they got it? Asked per candidate rather than read off the
    collaborator list, because that list omits organization members (see `already_admitted`), and
    without this an org member is a candidate on every single run, forever."""
    p = gh(
        ["api", f"/repos/{CLAIMS_REPO}/collaborators/{login}/permission", "--jq", ".permission"],
        CLAIMS_TOKEN,
        check=False,
    )
    return p.returncode == 0 and p.stdout.strip() in ("write", "maintain", "admin")


def grant():
    """Invite every author who is not in yet. A failure on one login does not stop the others, but
    the job still ends red so somebody looks (an org that forbids outside collaborators, or requires
    2FA of them, fails exactly here)."""
    candidates = sorted(merged_pr_authors() - already_admitted())
    invited = 0
    failures = 0
    for login in candidates:
        if has_access(login):
            continue  # an organization member; nothing to grant and nothing to report
        if DRY_RUN:
            print(f"grant: would invite {login}")
            invited += 1
            continue
        p = gh(
            ["api", "-X", "PUT", f"/repos/{CLAIMS_REPO}/collaborators/{login}", "-f", "permission=push"],
            CLAIMS_TOKEN,
            check=False,
        )
        if p.returncode != 0:
            failures += 1
            print(f"grant: FAILED to invite {login}: {(p.stderr or p.stdout).strip()}", file=sys.stderr)
            continue
        # 201 answers with the invitation; 204 (empty) means they could already push after all, so
        # say what happened rather than claiming an invitation that was never sent.
        print(f"grant: invited {login} to {CLAIMS_REPO}" if p.stdout.strip() else f"grant: {login} already had access")
        invited += 1
    if not invited:
        print("grant: every merged-PR author already has the claim namespace")
    return failures


def sweep():
    """Delete long-expired leases. The lease is the ref's commit MESSAGE (an orphan commit over an
    empty tree), so reading one is a single API call and no clone is needed."""
    refs = gh_lines(
        [
            "api",
            "--paginate",
            f"/repos/{CLAIMS_REPO}/git/matching-refs/{NS}?per_page=100",
            "--jq",
            '.[] | .ref + " " + .object.sha',
        ],
        CLAIMS_TOKEN,
    )
    cutoff = time.time() - SWEEP_GRACE_MINUTES * 60
    failures = 0
    for entry in refs:
        ref, _, sha = entry.partition(" ")
        lease = gh(["api", f"/repos/{CLAIMS_REPO}/git/commits/{sha}", "--jq", ".message"], CLAIMS_TOKEN, check=False)
        if lease.returncode != 0 or not is_sweepable(lease.stdout, cutoff):
            continue
        if DRY_RUN:
            print(f"sweep: would delete expired {ref}")
            continue
        # `/git/<ref>` is `/git/refs/tauceti-claims/<key>`: the ref name already carries its prefix.
        deleted = gh(["api", "-X", "DELETE", f"/repos/{CLAIMS_REPO}/git/{ref}"], CLAIMS_TOKEN, check=False)
        if deleted.returncode == 0:
            print(f"sweep: deleted expired {ref}")
        else:
            failures += 1
            print(f"sweep: FAILED to delete {ref}: {(deleted.stderr or deleted.stdout).strip()}", file=sys.stderr)
    return failures


if __name__ == "__main__":
    for name, value in (("GH_TOKEN", GH_TOKEN), ("CLAIMS_TOKEN", CLAIMS_TOKEN), ("REPO", REPO)):
        if not value:
            raise SystemExit(f"claims_access: ${name} is required")
    sys.exit(1 if grant() + sweep() else 0)
