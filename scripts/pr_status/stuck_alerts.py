#!/usr/bin/env python3
"""Post *stuck-automation* alerts to a dedicated Zulip topic (Tau Ceti > Stuck PRs).

This is an EMERGENCY channel, not a "ask the humans for help" queue. Every alert
here means a piece of Tau Ceti's own automation was supposed to make progress and
could not unstick itself: a bump that will not cross a breaking change, a green PR
the merge machinery never merged, a scheduled job that stopped firing, main gone
red. The expected response to any alert is to FIX THE INFRASTRUCTURE, e.g. a
script, a workflow, a pin, or a guard, so that the situation cannot recur. Do not
hand-hold one PR and move on. If an alert can only ever be resolved by a human
doing a one-off favour, it does not belong here; see the "deliberately NOT
alerted" list below.

Detectors (each names the infra failure it implies):

  1. stuck-bump      The last-known-good bump PR (branch hopscotch/lkg-bump) has a
                     RED `build` check that has stayed red past a grace window. The
                     daily bump cannot cross a mathlib breaking change on its own;
                     something needs a fix, e.g. a proof, scripts/lint-env.sh, or a
                     guard.
  2. stale-pin       main's mathlib pin has not moved in several days. The bump has
                     stopped advancing, e.g. a wedged PR, an unresolved
                     first-known-bad freeze, or update.yml silently broken.
  3. stranded-pr     A PR that is in-scope (TauCeti/ + allowed roots, bump-guard
                     green for any pin change), `build` green, every blocking
                     rubric green at HEAD, not draft/hold, mergeable, and quiet for
                     the grace window. auto-merge / the queue / merge-sweep broke.
  4. review-stuck    An open `Review stuck: PR #N` issue whose PR #N is also still
                     open: the review engine self-flagged a PR it cannot resolve.
                     An issue left open after its PR merged or closed is stale
                     bookkeeping by the (out-of-repo) worker, not a live wedge.
  5. dead-scheduler  A scheduled workflow is missing, disabled, or its last
                     SCHEDULED run is older than its cadence + slack. GitHub
                     disabled the cron (60-day inactivity), or it errors at dispatch.
  6. main-red        The CI run for main's tip commit reached a non-success terminal
                     conclusion. The "main is always green" invariant is broken.
  7. stale-fkb       An open first-known-bad issue (label `dependency-incompatibility`)
                     has been open past a grace window. A regression against TauCeti
                     nobody has landed the fix for.

Deliberately NOT alerted (normal backlog, not stuck automation -- alerting on
these would cheapen the topic and train people to ignore it):
  * a PR awaiting its first review verdict -- CI review generation is off by
    default (CI_REVIEW_ENABLED); reviews are run by humans / the worker on their
    own cadence, so "no verdict yet" is expected, not stuck;
  * a PR with changes-requested that nobody addressed -- housekeeping.py retires
    these after STALE_DAYS;
  * open roadmap / help-wanted issues -- that IS the ask-the-humans queue.

Idempotent, like zulip.py: exactly one bot-owned message per active
alert key, tagged with a hidden `<!--stuck:v1 <key>-->` marker on its LAST line.
Each run reconciles the topic against live GitHub state:
  * a NEW alert posts a message (the only event that notifies watchers);
  * an ONGOING alert is left byte-identical, so a persisting emergency is not
    re-edited every hour (bodies carry no live counters, only stable thresholds);
  * a CLEARED alert has its message edited to a ✅ form (edits do not notify);
  * a RECURRENCE (an alert whose latest message is already ✅) posts a NEW message
    rather than editing the buried one, so a re-fired incident is actually seen.
There are no @-mentions (the topic is watched, not pinged).

FAIL CLOSED, never fail open. A detector may raise, e.g. on a GitHub outage, a rate
limit, or a bug. When it does, its alerts are NOT cleared: its key-prefix is marked
"unknown" for the run and existing messages under that prefix are left exactly as
they are. The alternative
-- treating "the check failed" as "the emergency is over" -- is the worst possible
behaviour for a watchdog. Only a genuinely-absent alert from a detector that ran
cleanly is resolved.

Run status mirrors the healthcheck philosophy: the ALERTS are the signal, not the
run's red/green, so a run that checks and posts exits 0 even with ten alerts open.
Only a persistent Zulip CONFIG break (bad key, forbidden bot, not subscribed --
verified up front via zulip.check) fails the run loudly: if we cannot
post, the emergency channel itself is down, and that must not be silent.

Usage:
    stuck_alerts.py            # reconcile all detectors against the topic
    stuck_alerts.py --dry-run  # print the alerts it would post; touch no Zulip

Environment:
    ZULIP_API_KEY, ZULIP_EMAIL, ZULIP_SITE   bot credentials (required unless --dry-run)
    ZULIP_CHANNEL                            default "Tau Ceti"
    ZULIP_TOPIC                              default "Stuck PRs"
    GH_REPO                                  default "TauCetiProject/TauCeti"
    GH_TOKEN / GITHUB_TOKEN                  used by `gh` for the GitHub API

Only python3's standard library and an authenticated `gh` CLI are required. The
Zulip client, credential handling, and sanitizer are reused from zulip.py
(same package dir); pointing that client at a different topic is the module's own
documented mechanism: ZULIP_TOPIC (set to "Stuck PRs" by the workflow) is read at
import, so send/find target this topic.
"""

import base64
import datetime
import json
import os
import re
import sys

# Reuse the proven Zulip client + helpers. Because ZULIP_TOPIC is read at import
# time, the workflow sets it to "Stuck PRs" and every send/narrow below targets
# this topic without any change to zulip.py.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core  # noqa: E402
import zulip as zp  # noqa: E402

REPO = core.REPO
LKG_BRANCH = "hopscotch/lkg-bump"  # keep in sync with update.yml's LKG_BRANCH

# Keys we generate use only this alphabet; the marker is anchored to the final
# line and its key validated against this grammar, so untrusted text that happens
# to contain a `<!--stuck:v1 ...-->` string cannot masquerade as one of our
# markers or hijack another alert's key.
KEY_RE = re.compile(r"[a-z0-9][a-z0-9._/-]*")
MARKER_RE = re.compile(r"<!--stuck:v1 (" + KEY_RE.pattern + r")-->\s*\Z")

# --- thresholds --------------------------------------------------------------
# Each scheduler threshold is ~2-3x the workflow's cadence, generous enough to
# ride out GitHub's routine scheduled-run delays without false-firing.
BUMP_STUCK_HOURS = 24
PIN_STALE_DAYS = 4
STRANDED_HOURS = 6
FKB_STALE_DAYS = 3
SCHEDULERS = {
    # workflow file            (human name,               max age hours)
    "update.yml":            ("daily mathlib bump",       30),
    "pages.yml":             ("pages / doc-gen publish",  30),
    "housekeeping.yml":      ("queue housekeeping",        7),
    "zulip-healthcheck.yml": ("zulip healthcheck",        15),
    "merge-sweep.yml":       ("merge sweep",               4),
}
# A PR carrying any of these labels is intentionally parked; never "stranded".
HOLD_LABELS = {"keep", "hold", "wip", "human", "do-not-close", "blocked"}
# The downstream-reports first-known-bad tracking issue carries this label
# (author github-actions[bot]); the label is the stable signal, not the title.
FKB_LABEL = "dependency-incompatibility"
# CI conclusions that mean main is broken (not just `failure`).
RED_CONCLUSIONS = {"failure", "timed_out", "startup_failure"}


def now_utc():
    return datetime.datetime.now(datetime.timezone.utc)


def parse_ts(s):
    """Parse a GitHub ISO-8601 UTC timestamp (e.g. 2026-07-20T19:06:08Z)."""
    return datetime.datetime.fromisoformat(s.replace("Z", "+00:00"))


def hours_since(s):
    return (now_utc() - parse_ts(s)).total_seconds() / 3600.0


# ----- gh helpers -------------------------------------------------------------
# `gh api --jq` prints each jq result on its own line, and `--paginate` simply
# concatenates the per-page streams, so a jq that yields ONE VALUE PER LINE gives
# valid JSONL across any number of pages. gh_stream parses that (fixes the naive
# single-`json.loads` that broke past one page). gh_obj is for a jq yielding a
# single JSON value; gh_scalar is for a raw string (never JSON-decoded).

def gh_stream(path, jq, paginate=True):
    """Parsed list from a jq that emits one JSON value per line (e.g. `.[] | {…}`)."""
    out = core.gh_api(path, jq=jq, paginate=paginate)
    return [json.loads(ln) for ln in out.splitlines() if ln.strip()]


def gh_obj(path, jq):
    """Single parsed JSON value from a jq that yields one object, or None."""
    out = core.gh_api(path, jq=jq).strip()
    if not out:
        return None
    return json.loads(out.splitlines()[0])


def gh_scalar(path, jq, paginate=False):
    """Raw stripped string from a jq that yields a scalar (never json.loads it)."""
    return core.gh_api(path, jq=jq, paginate=paginate).strip()


def gh_lines(path, jq, paginate=True):
    """List of raw (non-JSON) string lines from a jq that emits bare strings, e.g.
    `.[].filename`. Unlike gh_stream this does NOT json.loads each line (a bare
    filename is not valid JSON)."""
    return [ln for ln in core.gh_api(path, jq=jq, paginate=paginate).splitlines() if ln.strip()]


# (state, updated_at) of the newest commit status for a context, shared with the
# `core` derivation (per_page=100 there so a status burst cannot hide `build` /
# `bump-guard`); alias so this module's detectors read as before.
newest_status = core.newest_status


# ----- detectors --------------------------------------------------------------
# Each returns a list of alert dicts {key, title, body}. `key` is stable across
# runs (so the same ongoing situation reconciles to the same message) and its
# prefix (the part before the first "/") names the detector, so a detector that
# errors marks exactly its own keys "unknown" and never clears them.

def detect_stuck_bump():
    prs = gh_stream(
        f"/repos/{REPO}/pulls?state=open&head=TauCetiProject:{LKG_BRANCH}&per_page=5",
        jq='.[] | {number, head: .head.sha, created_at}', paginate=False)
    out = []
    for pr in prs:
        state, _ = newest_status(pr["head"], "build")
        # Clock off the PR's age, not the build-status timestamp. A HEALTHY LKG
        # bump PR merges within hours and a fresh one is created per advance, so an
        # open LKG PR older than the window is reliably stuck. The build-status
        # `updated_at` is the wrong clock here: the daily bump force-pushes this
        # branch, re-running the SAME red build and resetting that timestamp every
        # day -- which would permanently mask a genuine multi-day wedge (observed
        # on PR #1057). Requiring the build to be currently red avoids firing on a
        # PR that has since gone green and is merging.
        if state in ("failure", "error") and hours_since(pr["created_at"]) >= BUMP_STUCK_HOURS:
            out.append({
                "key": f"stuck-bump/{pr['number']}",
                "title": "Mathlib bump wedged — LKG bump PR build stays red",
                "body": (
                    f"The last-known-good bump PR "
                    f"https://github.com/{REPO}/pull/{pr['number']} has had a red "
                    f"`build` check and has been open over {BUMP_STUCK_HOURS}h. The daily bump cannot "
                    f"cross a mathlib breaking change on its own.\n\n"
                    f"**Fix:** open the failing build, and land whatever fix it needs "
                    f"together with the pin move in one human-owned PR, so the bump "
                    f"can resume."),
            })
    return out


def detect_stale_pin():
    # Staleness is "how long since the pin last MOVED", not the age of the pinned
    # commit: right after a bump to an LKG commit that itself lags master, the
    # pinned commit can be days old while the bump is perfectly healthy. The daily
    # bump rewrites lake-manifest.json whenever mathlib advances, so the manifest's
    # last-change date on main is a direct proxy for the bump cadence.
    date = gh_scalar(f"/repos/{REPO}/commits?path=lake-manifest.json&sha=main&per_page=1",
                     jq='.[0].commit.committer.date // ""')
    if not date or hours_since(date) / 24.0 < PIN_STALE_DAYS:
        return []
    rev = ""
    content = gh_scalar(f"/repos/{REPO}/contents/lake-manifest.json?ref=main", jq='.content')
    if content:
        try:  # contents is base64 with embedded newlines; b64decode discards them
            data = json.loads(base64.b64decode(content).decode())
            rev = next((p["rev"] for p in data.get("packages", [])
                        if p["name"] == "mathlib"), "")
        except Exception:
            rev = ""
    pin = f" (mathlib `{rev[:10]}`)" if rev else ""
    return [{
        "key": "stale-pin",
        "title": "Mathlib pin has stopped advancing",
        "body": (
            f"`lake-manifest.json` on main{pin} has not changed in over "
            f"{PIN_STALE_DAYS} days; the daily bump has stalled.\n\n"
            f"**Fix:** find why — a wedged bump PR (see any stuck-bump alert), an "
            f"unresolved first-known-bad freeze, or `update.yml` failing — and clear "
            f"it so `hopscotch/lkg-bump` can move forward again."),
    }]


def is_automerge_scope(files):
    """Mirror the path allowlist enforced by pr-build and TauCetiReview."""
    if not files:
        return False
    allowed_roots = {"TauCeti.lean", "lake-manifest.json", "lean-toolchain"}
    return all(path.startswith("TauCeti/") or path in allowed_roots for path in files)


def detect_stranded_prs():
    prs = gh_stream(
        f"/repos/{REPO}/pulls?state=open&base=main&per_page=100",
        jq='.[] | {number, head: .head.sha, draft, updated_at, '
           'author: .user.login, labels: [.labels[].name]}')
    out = []
    for pr in prs:
        if pr.get("draft"):
            continue
        if HOLD_LABELS.intersection(n.lower() for n in pr.get("labels", [])):
            continue
        head = pr["head"]
        state, updated = newest_status(head, "build")
        if state != "success" or not updated:
            continue
        # Readiness clock: the LATER of the build going green and the PR's last
        # activity. Starting only from the build time would fire instantly when a
        # review approves a PR whose build passed yesterday (the merge path has had
        # no chance yet); updated_at bumps on that approval/commit/label.
        ready_since = min(hours_since(updated), hours_since(pr["updated_at"]))
        if ready_since < STRANDED_HOURS:
            continue
        # NOTE: scoreboard_meta is the trusted scoreboard comment auto-merge reads
        # to TRIGGER a re-check; it is not the authoritative merge ledger, so this
        # is best-effort and can lag. The mergeable + in-scope + quiet-window guards
        # below keep the false-emergency rate low; a fully authoritative read of the
        # TauCetiReview ledger is a possible future hardening.
        if core.review_state(core.scoreboard_meta(pr["number"]), head) != "approved":
            continue
        # Filenames are bare strings, not JSON -- gh_lines, not gh_stream.
        files = gh_lines(f"/repos/{REPO}/pulls/{pr['number']}/files?per_page=300",
                         jq='.[].filename')
        if not files:
            continue
        touches_pin = any(
            f in ("lake-manifest.json", "lean-toolchain", "lakefile.toml") for f in files)
        if not is_automerge_scope(files):
            continue  # a human-owned path legitimately does not auto-merge
        if touches_pin and newest_status(head, "bump-guard")[0] != "success":
            continue
        # Only alert when GitHub positively says the PR CAN merge. `.mergeable` is
        # true|false|null; do NOT use jq `//` (it maps false->the default too). A
        # conflicting PR (false) is not being wrongly withheld; an as-yet-uncomputed
        # PR (null) we skip this run and recheck next hour (a real strand persists).
        if gh_scalar(f"/repos/{REPO}/pulls/{pr['number']}", jq='.mergeable') != "true":
            continue
        out.append({
            "key": f"stranded-pr/{pr['number']}",
            "title": "Green PR is not being merged",
            "body": (
                f"https://github.com/{REPO}/pull/{pr['number']} is in-scope, `build` "
                f"green, and every blocking rubric green at HEAD, yet has sat unmerged "
                f"for over {STRANDED_HOURS}h while merge-sweep runs hourly.\n\n"
                f"**Fix:** the merge path is broken — check `auto-merge.yml`, the merge "
                f"queue, and `merge-sweep.yml` (and the pinned TauCetiReview merge-only "
                f"/ merge-sweep workflow) for why a ready PR is not being taken."),
        })
    return out


REVIEW_STUCK_TITLE_RE = re.compile(r"Review stuck: PR #([0-9]+)")


def flagged_pr_is_finished(number):
    """True iff the PR the issue flagged is definitely merged or closed.

    Any doubt (an API error, a number that is not a PR, an unexpected state) is
    False, so the caller keeps alerting. Fail closed: a live wedge must never be
    silenced by a lookup that did not work.
    """
    try:
        return gh_scalar(f"/repos/{REPO}/pulls/{number}", jq='.state // ""') == "closed"
    except Exception as exc:
        zp.log(f"review-stuck: state of PR #{number} unreadable ({exc}); alerting anyway")
        return False


def detect_review_stuck():
    # Match the exact title grammar and interpolate NOTHING from the (untrusted)
    # title into the message: the alert renders a fixed title and links the issue
    # by its numeric id, so a crafted title cannot inject a marker or a mention.
    # The flagged PR's number is recovered from that same grammar and re-checked
    # here against a digits-only pattern before it reaches an API path.
    issues = gh_stream(
        f"/repos/{REPO}/issues?state=open&per_page=100",
        jq='.[] | select(.pull_request == null) '
           '| select(.title | test("^Review stuck: PR #[0-9]+$")) | {number, title}')
    out = []
    for i in issues:
        # The engine is wedged only while the PR it flagged is still open. The
        # worker that files these issues closes them once their PR merges or is
        # closed, but that self-close is out of this repo and has been observed to
        # miss: issue #1137's PR #1134 merged 16 minutes later and the alert still
        # fired for two days. An issue outliving its PR is stale bookkeeping, not
        # an emergency, and the topic is worthless once it cries wolf.
        m = REVIEW_STUCK_TITLE_RE.fullmatch(i.get("title") or "")
        if m and flagged_pr_is_finished(m.group(1)):
            zp.log(f"review-stuck: issue #{i['number']} names finished PR #{m.group(1)}; skipping")
            continue
        out.append({
            "key": f"review-stuck/{i['number']}",
            "title": "Review engine self-flagged a PR it cannot resolve",
            "body": (
                f"An open `Review stuck` issue is unresolved: "
                f"https://github.com/{REPO}/issues/{i['number']}\n\n"
                f"**Fix:** this is not a one-off review to nudge. The engine hit a "
                f"state it has no rule for, e.g. a rubric contradiction or an error "
                f"loop. Fix the review logic / rubric in TauCetiReview so it cannot "
                f"re-wedge."),
        })
    return out


def detect_dead_schedulers():
    out = []
    for wf, (name, max_hours) in SCHEDULERS.items():
        try:
            out.extend(_check_scheduler(wf, name, max_hours))
        except Exception as exc:
            # A transient error on one workflow (or an ambiguous 404) must not abort
            # the whole detector -- that would mark ALL schedulers "unknown" and skip
            # the ones that are genuinely stalled. Log and move on.
            zp.log(f"scheduler check for {wf} failed (non-fatal): {exc}")
    return out


def _check_scheduler(wf, name, max_hours):
    meta = gh_obj(f"/repos/{REPO}/actions/workflows/{wf}",
                  jq='{state: (.state // "")}')
    state = meta.get("state") if meta else ""
    if state and state != "active":
        return [_sched_alert(wf, name,
            f"`{wf}` is `{state}` (GitHub disables a cron after 60 days of repo "
            f"inactivity, or on repeated failure).",
            f"Re-enable it (`gh workflow enable {wf}`) and fix the underlying cause.")]
    # Only SCHEDULED runs prove the cron fires; a workflow_dispatch or push run
    # (e.g. pages.yml on a web/ change) must not make a dead schedule look alive.
    last = gh_scalar(
        f"/repos/{REPO}/actions/workflows/{wf}/runs?event=schedule&per_page=1",
        jq='.workflow_runs[0].created_at // ""')
    if not last:
        return [_sched_alert(wf, name, f"`{wf}` has no scheduled run on record.",
                             "Confirm the cron is configured and firing.")]
    if hours_since(last) >= max_hours:
        return [_sched_alert(wf, name,
            f"`{wf}`'s last scheduled run was over {max_hours}h ago (its cadence + "
            f"slack); the schedule has stopped firing.",
            "Check the Actions tab for a dispatch error or an org-level disable.")]
    return []


def _sched_alert(wf, name, problem, fix):
    return {
        "key": f"dead-scheduler/{wf}",
        "title": f"Scheduler not firing — {name}",
        "body": f"{problem}\n\n**Fix:** {fix}",
    }


def detect_main_red():
    tip = gh_scalar(f"/repos/{REPO}/commits/main", jq='.sha // ""')
    if not tip:
        return []
    # Evaluate the CI run for main's CURRENT tip specifically, so an old green run
    # cannot mask a red (or never-completed) run on the commit that is actually
    # main right now.
    run = gh_obj(
        f"/repos/{REPO}/actions/workflows/ci.yml/runs?head_sha={tip}&per_page=1",
        jq='.workflow_runs[0] | {status: (.status // ""), conclusion: (.conclusion // "")}')
    if not run or run.get("status") != "completed":
        return []  # in progress or not yet run — not (yet) a red-main emergency
    if run.get("conclusion") not in RED_CONCLUSIONS:
        return []
    return [{
        "key": "main-red",
        "title": "main is RED",
        "body": (
            f"CI on main's tip (`{tip[:10]}`) concluded `{run['conclusion']}`. The "
            f"\"main is always green\" invariant is broken.\n\n"
            f"**Fix:** identify the merge or environment change that broke it and land a "
            f"revert or forward-fix immediately — a red main blocks every bump and merge."),
    }]


def detect_stale_fkb():
    issues = gh_stream(
        f"/repos/{REPO}/issues?state=open&labels={FKB_LABEL}&per_page=100",
        jq='.[] | select(.pull_request == null) | {number, created_at}')
    out = []
    for i in issues:
        if hours_since(i["created_at"]) / 24.0 < FKB_STALE_DAYS:
            continue
        out.append({
            "key": f"stale-fkb/{i['number']}",
            "title": "Mathlib incompatibility unresolved",
            "body": (
                f"A first-known-bad tracking issue (`{FKB_LABEL}`) has been open for "
                f"over {FKB_STALE_DAYS} days: https://github.com/{REPO}/issues/{i['number']}. "
                f"The pin is frozen at the last-known-good commit until it is fixed.\n\n"
                f"**Fix:** land the fix PR whose manifest is pinned at the first-known-bad commit so the "
                f"freeze lifts and the daily bump resumes toward master."),
        })
    return out


# (prefix, detector). The prefix is the part of every key before the first "/",
# so a detector that raises marks exactly its own alerts "unknown" for the run.
DETECTORS = [
    ("stuck-bump", detect_stuck_bump),
    ("stale-pin", detect_stale_pin),
    ("stranded-pr", detect_stranded_prs),
    ("review-stuck", detect_review_stuck),
    ("dead-scheduler", detect_dead_schedulers),
    ("main-red", detect_main_red),
    ("stale-fkb", detect_stale_fkb),
]


def key_prefix(key):
    return key.split("/", 1)[0]


def collect_alerts():
    """Run every detector. Returns (alerts, failed_prefixes). A detector that
    raises contributes no alerts AND has its prefix recorded as failed, so the
    reconcile step leaves that prefix's existing messages untouched (fail closed)
    instead of resolving live emergencies during an API blip."""
    alerts, failed = [], set()
    for prefix, det in DETECTORS:
        try:
            alerts.extend(det() or [])
        except Exception as exc:
            zp.log(f"detector {det.__name__} [{prefix}] failed (non-fatal): {exc}")
            failed.add(prefix)
    return alerts, failed


# ----- reconcile against the topic -------------------------------------------

RED = "\U0001f534"   # 🔴
GREEN = "✅"     # ✅


def parse_marker(content):
    """The alert key iff `content` ends with a well-formed marker whose key matches
    the strict grammar, else None. Anchoring to the end + strict grammar means
    untrusted text embedding a marker-like string cannot be read as one of ours."""
    m = MARKER_RE.search(content)
    return m.group(1) if m else None


def alert_content(a):
    return f"{RED} **{a['title']}**\n\n{a['body']}\n\n<!--stuck:v1 {a['key']}-->"


def resolved_content(key, title):
    return (f"{GREEN} **{title}** — cleared\n\n_No longer active as of the latest "
            f"check._\n\n<!--stuck:v1 {key}-->")


def newest_by_key(msgs, bot_id):
    """key -> the bot's newest message carrying that key's marker."""
    out = {}
    for m in msgs:
        if m["sender_id"] != bot_id:
            continue
        key = parse_marker(m["content"])
        if key is None:
            continue
        if key not in out or m["id"] > out[key]["id"]:
            out[key] = m
    return out


def is_resolved(msg):
    return msg["content"].lstrip().startswith(GREEN)


def reconcile(z, alerts, failed, dry_run):
    bot_id = z.my_user_id()
    msgs = z.get_messages([
        {"operator": "channel", "operand": zp.CHANNEL},
        {"operator": "topic", "operand": zp.TOPIC},
    ])
    existing = newest_by_key(msgs, bot_id)
    active = {a["key"]: a for a in alerts}

    for key, a in active.items():
        content = alert_content(a)
        msg = existing.get(key)
        if msg is None or is_resolved(msg):
            # New, or a recurrence whose latest message is already ✅: post a fresh
            # message so watchers actually see the (re-)fired incident. Editing the
            # buried ✅ back to red would notify no one.
            zp.log(f"POST alert {key}: {a['title']}")
            if not dry_run:
                z.send_message(content)
        elif msg["content"] != content:
            zp.log(f"refresh alert {key}")
            if not dry_run:
                z.update_message(msg["id"], content)
        else:
            zp.log(f"ongoing alert {key} (unchanged)")

    for key, msg in existing.items():
        if key in active or is_resolved(msg):
            continue
        if key_prefix(key) in failed:
            zp.log(f"detector for {key} failed this run; NOT resolving (fail closed)")
            continue
        zp.log(f"RESOLVED alert {key}")
        if not dry_run:
            z.update_message(msg["id"], resolved_content(key, _title_of(msg["content"], key)))


def _title_of(content, key):
    """Best-effort recovery of the bolded title from an existing message body."""
    for line in content.splitlines():
        if "**" in line:
            parts = line.split("**")
            if len(parts) >= 2 and parts[1].strip():
                return parts[1].strip()
    return key


def main(argv):
    dry_run = "--dry-run" in argv[1:]
    alerts, failed = collect_alerts()
    zp.log(f"{len(alerts)} active alert(s): {sorted(a['key'] for a in alerts)}"
           + (f"; detectors unknown this run: {sorted(failed)}" if failed else ""))

    if dry_run:  # never touches Zulip, with or without creds — consistent output
        for a in alerts:
            print("\n" + alert_content(a))
        return 0

    email = (os.environ.get("ZULIP_EMAIL") or "").strip()
    api_key = (os.environ.get("ZULIP_API_KEY") or "").strip()
    site = (os.environ.get("ZULIP_SITE") or "https://leanprover.zulipchat.com").strip()
    if not (email and api_key):
        return zp.fail_config("ZULIP_EMAIL / ZULIP_API_KEY not set (no bot configured)")

    z = zp.Zulip(email, api_key, site)
    try:
        zp.check(z)  # up-front: bad key / forbidden / not subscribed -> fail red
        reconcile(z, alerts, failed, dry_run)
    except zp.ConfigError as exc:  # emergency channel itself is down: fail loud
        return zp.fail_config(str(exc))
    except Exception as exc:  # a transient Zulip hiccup is cosmetic; self-heals
        zp.log(f"reconcile failed (non-fatal): {exc}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
