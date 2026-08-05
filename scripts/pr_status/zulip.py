#!/usr/bin/env python3
"""Mirror a TauCeti PR's lifecycle onto Zulip emoji reactions.

We keep exactly one bot-owned message per PR in a dedicated channel/topic
(default: "Tau Ceti" > "PRs") and reconcile two independent, mutually-exclusive
groups of emoji reactions on it from the PR's status (see core.derive):

  CI (build) group        review / lifecycle group
    running   -> yellow      review has begun        -> eyes
    passed    -> green_circle review is pending       -> (none)
    failed    -> red_circle  changes_requested/block -> writing
                             all review done, green   -> check
                             merged                   -> merge      (realm emoji)
                             closed, not merged       -> closed-pr  (realm emoji)

The status comes from core.derive, which reads GitHub truth (PR state, the
canonical `<!--tauceti-scoreboard-->` comment's meta JSON, and the `build` commit
status). This sink only renders it, so the same `reconcile` powers both the
event-driven GitHub Actions and a one-shot backfill over historical PRs. Run it
as often as you like; it converges the reactions to match GitHub and nothing else.

Only the *bot's own* reactions are authoritative: presence is judged by the
bot's user id, so a human reacting on a message never confuses reconciliation,
and we only ever add/remove our own reactions.

Usage:
    zulip.py reconcile <pr_number> [--create|--create-if-open] [--strict] [--ci STATE]
    zulip.py backfill [--dry-run] [--strict]  # JSONL PR states on stdin
    zulip.py check

`--create` posts the per-PR message if it does not exist yet (used by the PR
"opened" workflow and when intentionally seeding missing posts). Without it, a
PR with no message yet is left alone (other events only react to an existing
message, never create one). `--create-if-open` is the label-event self-heal: it
creates a missing post only if current GitHub truth still says the PR is open.

`--strict` makes a transient reconciliation error exit non-zero instead of
being swallowed as cosmetic. Normal event-driven runs stay self-healing; the
historical backfill uses strict mode so a partial migration is visible and can
be safely rerun.

`backfill` reads one PR-state JSON object per line from stdin, authenticates the
bot once, edits only messages that already exist, continues past per-PR errors,
and reports all failures at the end. `--dry-run` performs every read and reports
the number of changes without writing messages or reactions.

`check` is a credentials/health probe: it authenticates and confirms the bot is
subscribed to the channel, then exits 0. It touches no PR and no message, so a
scheduled job can run it to catch a broken key during quiet periods, when no PR
event would otherwise exercise the integration.

`--ci STATE` (running|success|failure|none) forces the CI group instead of
deriving it from the `build` commit status. The `pr-build` workflow posts the
`build` status only at the end, so its "requested" event passes `--ci running`
to show 🟡 while the build is in flight.

Environment:
    ZULIP_API_KEY, ZULIP_EMAIL, ZULIP_SITE   bot credentials (required)
    ZULIP_CHANNEL                            default "Tau Ceti"
    ZULIP_TOPIC                              default "PRs"
    GH_REPO                                  default "TauCetiProject/TauCeti"
    GH_TOKEN / GITHUB_TOKEN                  used by `gh` for the GitHub API

The only runtime dependencies are python3's standard library and an
authenticated `gh` CLI -- no third-party packages.

Failure modes are split on purpose, because "a reaction didn't update" and "the
whole integration is dead" deserve different volumes:

  * A *transient* hiccup (one Zulip 5xx, a network blip, a single missing PR)
    is cosmetic and self-heals on the next reconcile, so we log it and exit 0.
  * A *configuration* failure -- missing/empty creds, a bad API key (401), a
    forbidden bot (403), or the bot not subscribed to the channel -- breaks
    every PR and will not fix itself. We log it, emit a GitHub Actions
    `::error::` annotation (visible even under `continue-on-error`), and exit
    non-zero so the workflow run goes red. This is the loud signal that the
    secret needs re-setting; see scripts/pr_status/README.md for the fix.
"""

import base64
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

import core

REPO = core.REPO
CHANNEL = os.environ.get("ZULIP_CHANNEL", "Tau Ceti")
TOPIC = os.environ.get("ZULIP_TOPIC", "PRs")
ZWSP = "​"  # zero-width space, used to defuse mentions/linkifiers
# Messages from before the repository transfer still contain this URL. Reconcile
# recognizes it, then updates the post to REPO's canonical URL in place.
LEGACY_REPOS = ("FormalFrontier/TauCeti",)
_MESSAGE_NOT_GIVEN = object()


class ConfigError(RuntimeError):
    """A persistent auth/permission/config failure that will not self-heal:
    missing or empty creds, a bad API key (401), a forbidden bot (403), or the
    bot not being subscribed to the channel. Raised so the caller can surface it
    loudly (non-zero exit + ::error:: annotation) instead of the quiet cosmetic
    path, because it breaks the integration for *every* PR, not just one."""

# name -> (reaction_type, emoji_code). Unicode emoji resolve by name on the
# server, so emoji_code is None; realm (custom) emoji must carry their id.
EMOJI = {
    # CI (build) group
    "yellow":           ("unicode_emoji", None),
    "green_circle":     ("unicode_emoji", None),
    "red_circle":       ("unicode_emoji", None),
    # review / lifecycle group
    "eyes":             ("unicode_emoji", None),
    # Legacy state, retained in the group so reconcile removes old ▶️ reactions.
    "play":             ("unicode_emoji", None),
    "writing":          ("unicode_emoji", None),
    "check":            ("unicode_emoji", None),
    "merge":            ("realm_emoji", "18527"),
    "closed-pr":        ("realm_emoji", "61293"),
}
CI_GROUP = ["yellow", "green_circle", "red_circle"]
REVIEW_GROUP = ["eyes", "play", "writing", "check", "merge", "closed-pr"]

# core.derive's CI states -> this sink's emoji. An unreported build is the
# `awaiting-CI` state, so it is yellow too; terminal PRs clear the group.
CI_EMOJI = {"running": "yellow", "success": "green_circle",
            "failure": "red_circle", None: "yellow"}


def log(msg):
    print(msg, flush=True)


def sleep_for(delay):
    """Sleep for all of `delay`, in chunks so one wait never exceeds 60 seconds."""
    remaining = max(0.1, delay)
    while remaining > 0:
        chunk = min(remaining, 60)
        time.sleep(chunk)
        remaining -= chunk


def pr_url(pr):
    return f"https://github.com/{REPO}/pull/{pr}"


# ----- Zulip REST (stdlib urllib; no third-party dependency) ------------------

class Zulip:
    def __init__(self, email, api_key, site):
        self.base = site.rstrip("/") + "/api/v1"
        self.auth = "Basic " + base64.b64encode(f"{email}:{api_key}".encode()).decode()

    def _call(self, method, path, params, tolerate=(), retry=True):
        attempts = 6 if retry else 1
        for attempt in range(attempts):
            data = urllib.parse.urlencode(params).encode() if params else None
            url = self.base + path
            if method in ("GET", "DELETE") and data:
                url += "?" + data.decode()
                data = None
            req = urllib.request.Request(url, data=data, method=method)
            req.add_header("Authorization", self.auth)
            if data:
                req.add_header("Content-Type", "application/x-www-form-urlencoded")
            try:
                with urllib.request.urlopen(req) as resp:
                    return json.loads(resp.read().decode())
            except urllib.error.HTTPError as e:
                payload = {}
                try:
                    payload = json.loads(e.read().decode())
                except Exception:
                    pass
                if payload.get("code") in tolerate:
                    return payload
                if attempt + 1 < attempts and (e.code == 429 or 500 <= e.code < 600):
                    if e.code == 429:
                        raw_delay = (
                            e.headers.get("Retry-After")
                            or payload.get("retry-after")
                            or 1
                        )
                        try:
                            delay = max(0.1, float(raw_delay))
                        except (TypeError, ValueError):
                            delay = 1
                        reason = "rate limit"
                    else:
                        delay = 2 ** attempt
                        reason = f"HTTP {e.code}"
                    log(f"Zulip {reason}; retrying in {delay:.1f}s")
                    sleep_for(delay)
                    continue
                detail = f"Zulip {method} {path} failed: {e.code} {payload or e.reason}"
                # A persistent creds/permission break (vs a one-off hiccup) is a
                # ConfigError, so main() fails loudly instead of swallowing it. 401
                # and Zulip's UNAUTHORIZED code (e.g. "Malformed API key") are always
                # auth. A 403 counts only when Zulip itself answered with a JSON body
                # (a real permission error); an opaque 403 from a WAF/proxy has no
                # payload and is treated as a transient hiccup, not a config break.
                if (e.code == 401
                        or payload.get("code") == "UNAUTHORIZED"
                        or (e.code == 403 and payload)):
                    raise ConfigError(detail)
                raise RuntimeError(detail)
            except urllib.error.URLError as e:
                if attempt + 1 < attempts:
                    delay = 2 ** attempt
                    log(f"Zulip network error; retrying in {delay:.1f}s: {e.reason}")
                    sleep_for(delay)
                    continue
                raise RuntimeError(f"Zulip {method} {path} failed: {e.reason}") from e

    def my_user_id(self):
        return self._call("GET", "/users/me", None)["user_id"]

    def my_subscriptions(self):
        return [s["name"] for s in
                self._call("GET", "/users/me/subscriptions", None)["subscriptions"]]

    def get_message_page(self, narrow, anchor="newest", num_before=1000):
        params = {
            "anchor": anchor, "num_before": num_before, "num_after": 0,
            "apply_markdown": "false",  # raw markdown, so content compares exactly
            "narrow": json.dumps(narrow),
        }
        return self._call("GET", "/messages", params)

    def get_messages(self, narrow, num_before=1000):
        return self.get_message_page(narrow, num_before=num_before)["messages"]

    def send_message(self, content):
        # Sending is not idempotent: if Zulip accepts the request but the
        # response is lost, retrying would create a permanent duplicate post.
        r = self._call("POST", "/messages", {
            "type": "stream", "to": CHANNEL, "topic": TOPIC, "content": content,
        }, retry=False)
        return r["id"]

    def update_message(self, message_id, content):
        self._call("PATCH", f"/messages/{message_id}", {"content": content})

    def _emoji_params(self, name):
        rtype, code = EMOJI[name]
        p = {"emoji_name": name}
        if rtype == "realm_emoji":
            p.update(emoji_code=code, reaction_type="realm_emoji")
        return p

    def add_reaction(self, message_id, name):
        # Already present -> the end state is what we want.
        self._call("POST", f"/messages/{message_id}/reactions",
                   self._emoji_params(name), tolerate=("REACTION_ALREADY_EXISTS",))

    def remove_reaction(self, message_id, name):
        # Already absent -> the end state is what we want.
        self._call("DELETE", f"/messages/{message_id}/reactions",
                   self._emoji_params(name),
                   tolerate=("REACTION_DOES_NOT_EXIST", "REACTION_DOESNT_EXIST"))


def find_message(z, pr, bot_id):
    """The bot's own message linking to this PR, or None.

    Match requires the exact PR URL (word-boundaried so #17 never matches #171)
    AND that the bot authored the message, so a human's message that quotes the
    link can never be mistaken for the status message.
    """
    urls = [pr_url(pr)] + [
        f"https://github.com/{repo}/pull/{pr}" for repo in LEGACY_REPOS
    ]
    hits = []
    for url in urls:
        msgs = z.get_messages([
            {"operator": "channel", "operand": CHANNEL},
            {"operator": "topic", "operand": TOPIC},
            {"operator": "search", "operand": url},
        ])
        pat = re.compile(re.escape(url) + r"(?![0-9])")
        hits.extend(
            m for m in msgs if m["sender_id"] == bot_id and pat.search(m["content"])
        )
        if hits:
            break
    return min(hits, key=lambda m: m["id"]) if hits else None


def topic_message_index(z, bot_id):
    """Index every bot-authored PR post with a handful of paginated topic reads.

    The event-driven path searches for one PR. A historical backfill instead
    reads the topic once, avoiding thousands of full-text searches and sharing
    the Zulip rate-limit budget politely.
    """
    repos = tuple(dict.fromkeys((REPO, *LEGACY_REPOS)))
    url_re = re.compile(
        r"https://github\.com/(?:"
        + "|".join(re.escape(repo) for repo in repos)
        + r")/pull/([0-9]+)(?![0-9])"
    )
    narrow = [
        {"operator": "channel", "operand": CHANNEL},
        {"operator": "topic", "operand": TOPIC},
    ]
    messages_by_id = {}
    anchor = "newest"
    while True:
        page = z.get_message_page(narrow, anchor=anchor)
        messages = page.get("messages") or []
        for message in messages:
            messages_by_id[message["id"]] = message
        if page.get("found_oldest") or not messages:
            break
        next_anchor = min(message["id"] for message in messages)
        if next_anchor == anchor:
            raise RuntimeError("Zulip message pagination did not advance")
        anchor = next_anchor

    result = {}
    for message in messages_by_id.values():
        if message.get("sender_id") != bot_id:
            continue
        match = url_re.search(message.get("content") or "")
        if not match:
            continue
        pr = match.group(1)
        if pr not in result or message["id"] < result[pr]["id"]:
            result[pr] = message
    return result


def pr_message_content(pr, title, author, roadmaps):
    """The durable two-line PR post.

    Author and roadmap come from the same PR payload/API read as the title.
    Roadmap labels may be added after opening; labeled/unlabeled events run
    reconcile again and edit this message in place.
    """
    if author:
        safe_author = zulip_sanitize(author)
        if author.endswith("[bot]"):
            # GitHub App logins contain brackets, which do not form a reliable
            # Markdown link and do not have a github.com/<login> profile page.
            author_text = safe_author
        else:
            author_text = (
                f"[{safe_author}]"
                f"(https://github.com/{urllib.parse.quote(author, safe='')})"
            )
    else:
        author_text = "unknown"
    roadmap_text = (
        ", ".join(zulip_sanitize(name.removeprefix("roadmap/")) for name in roadmaps)
        or "unlabelled"
    )
    return (f"**{zulip_sanitize(title)}** · {pr_url(pr)}  \n"
            f"author: {author_text} · roadmap: {roadmap_text}")


def zulip_sanitize(text):
    """Defuse the only Zulip markup in a PR title that would do real harm: an
    `@`-mention (pings people) or a linkifier like `#1234` / `@**group**` (wrong
    auto-link). A zero-width space after each `@`/`#` breaks those patterns
    invisibly, so the title still reads exactly as written -- no backslash noise.
    Ordinary emphasis in a title is the author's own and renders harmlessly."""
    return re.sub(r"([@#])", lambda m: m.group(1) + ZWSP, text)


def set_group(z, message, bot_id, group, desired, dry_run=False):
    """Ensure `desired` (or nothing) is the only reaction from `group` that the
    bot owns. Only the bot's own reactions count, so human reactions are left
    untouched and never block convergence."""
    mine = {r["emoji_name"] for r in message.get("reactions", [])
            if r["emoji_name"] in group and r.get("user_id") == bot_id}
    changes = 0
    for name in group:
        if name in mine and name != desired:
            changes += 1
            log(f"{'would remove' if dry_run else 'removing'} {name}")
            if not dry_run:
                z.remove_reaction(message["id"], name)
    if desired and desired not in mine:
        changes += 1
        log(f"{'would add' if dry_run else 'adding'} {desired}")
        if not dry_run:
            z.add_reaction(message["id"], desired)
    return changes


def review_emoji(status):
    """Review reaction derived from the same truth as the automatic labels.

    In particular, the live review marker that produces `review-in-progress`
    produces 👀 here. A completed blocking review produces ✍️, and an all-green
    review produces ✔️. Merely waiting for review has no review reaction.
    """
    if status["review"] == "approved":
        return "check"
    if status["review"] == "changes":
        return "writing"
    if status.get("review_inprogress"):
        return "eyes"
    return None


def reconcile(
        z, pr, create, ci_override, bot_id=None, state=None, dry_run=False,
        message=_MESSAGE_NOT_GIVEN, create_if_open=False):
    bot_id = z.my_user_id() if bot_id is None else bot_id
    # Read only the PR's own metadata first and find-or-create the durable message from its title,
    # BEFORE the fallible CI/scoreboard reads. Otherwise a transient GitHub hiccup during those reads
    # would abort the sole --create run and the PR would stay absent from Zulip indefinitely (later
    # events don't pass --create). Passing this state into derive() reads the PR just once.
    st = core.pr_state(pr) if state is None else state
    create = create or (
        create_if_open and st["state"] == "open" and not st["merged"]
    )
    content = pr_message_content(
        pr, st["title"], st.get("author", ""), st.get("roadmaps", []))
    if message is _MESSAGE_NOT_GIVEN:
        message = find_message(z, pr, bot_id)
    if message is None:
        if not create:
            log(f"no message for PR #{pr} yet and --create not set; nothing to do")
            return 0
        if dry_run:
            log(f"would create message for PR #{pr}")
            return 1
        mid = z.send_message(content)
        log(f"created message {mid} for PR #{pr}")
        message = {"id": mid, "reactions": []}
        changes = 1
    elif message.get("content") != content:
        # Self-heal: the title changed, or an older format/sanitizer left stale text.
        changes = 1
        log(f"{'would update' if dry_run else 'updating'} content "
            f"of message {message['id']} for PR #{pr}")
        if not dry_run:
            z.update_message(message["id"], content)
    else:
        changes = 0

    status = core.derive(pr, ci_override, state=st)
    rev = {"merged": "merge", "closed": "closed-pr"}.get(status["lifecycle"])
    if rev is None:  # open PR: render the review state
        rev = review_emoji(status)
    changes += set_group(z, message, bot_id, REVIEW_GROUP, rev, dry_run)

    # CI status is only meaningful while the PR is open; core.derive already
    # clears it (ci=None) on a terminal PR, so this maps straight through.
    ci_emoji = None if status["lifecycle"] != "open" else CI_EMOJI[status["ci"]]
    changes += set_group(z, message, bot_id, CI_GROUP, ci_emoji, dry_run)
    log(f"PR #{pr}: review={rev} ci={ci_emoji}")
    return changes


def backfill(z, rows, dry_run=False):
    """Reconcile JSONL PR states, continuing past item failures.

    Returns `(seen, changes, failures)`, where failures is a list of
    `(pr-or-line, message)` pairs. Persistent configuration failures still raise
    immediately because no later item can succeed.
    """
    bot_id = z.my_user_id()
    messages = topic_message_index(z, bot_id)
    log(f"indexed {len(messages)} existing PR posts")
    seen = 0
    changes = 0
    failures = []
    for line_number, line in enumerate(rows, 1):
        if not line.strip():
            continue
        try:
            state = json.loads(line)
            pr = str(state.pop("number"))
            if not pr.isdigit():
                raise ValueError("number is not a PR number")
            if not isinstance(state.get("roadmaps"), list):
                state["roadmaps"] = []
        except (json.JSONDecodeError, KeyError, TypeError, ValueError) as exc:
            failures.append((f"line {line_number}", f"invalid PR state: {exc}"))
            continue
        seen += 1
        try:
            changes += reconcile(
                z,
                pr,
                create=False,
                ci_override=None,
                bot_id=bot_id,
                state=state,
                dry_run=dry_run,
                message=messages.get(pr),
            )
        except ConfigError:
            raise
        except Exception as exc:
            log(f"PR #{pr} failed; continuing: {exc}")
            failures.append((f"PR #{pr}", str(exc)))
    mode = "dry-run" if dry_run else "backfill"
    log(f"{mode}: {seen} PRs, {changes} changes, {len(failures)} failures")
    for item, message in failures:
        log(f"FAILED {item}: {message}")
    return seen, changes, failures


def check(z):
    """Health probe: authenticate and confirm the bot can act in the channel.

    A bad key raises ConfigError from `my_user_id` (the 401 path); a bot that is
    not subscribed to the channel can authenticate but cannot post or react, so
    that is treated as a config failure too. Touches no PR and no message."""
    bot_id = z.my_user_id()
    subs = z.my_subscriptions()
    if CHANNEL not in subs:
        raise ConfigError(
            f"bot (user {bot_id}) is not subscribed to channel {CHANNEL!r}; "
            f"it cannot post or react there. Subscribe it and re-run.")
    log(f"OK: authenticated as user {bot_id}, subscribed to {CHANNEL!r}")


def fail_config(msg):
    """Report a persistent config break loudly: a GitHub Actions error
    annotation (visible in the run summary even under `continue-on-error`) plus a
    non-zero exit so the workflow run goes red. See the module docstring."""
    log(f"CONFIG ERROR: {msg}")
    if os.environ.get("GITHUB_ACTIONS") == "true":
        # Escape the workflow-command payload so a %, CR, or LF in the error text
        # (e.g. a Zulip JSON body) can't malform or truncate the annotation.
        safe = msg.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
        print(f"::error title=Zulip PR status integration is broken::{safe}", flush=True)
    return 1


def main(argv):
    cmd = argv[1] if len(argv) > 1 else None
    if cmd not in ("reconcile", "backfill", "check"):
        print(__doc__)
        return 2

    # Strip the creds: a stray trailing newline or surrounding whitespace in the
    # GitHub secret is the single most common way ZULIP_API_KEY breaks (the byte
    # rides into the Basic-auth header and Zulip rejects it as "Malformed API
    # key"). Defang it here so a sloppily-set secret still works.
    email = (os.environ.get("ZULIP_EMAIL") or "").strip()
    api_key = (os.environ.get("ZULIP_API_KEY") or "").strip()
    site = (os.environ.get("ZULIP_SITE") or "https://leanprover.zulipchat.com").strip()
    if not (email and api_key):
        return fail_config("ZULIP_EMAIL / ZULIP_API_KEY not set (no bot configured)")
    z = Zulip(email, api_key, site)

    if cmd == "check":
        try:
            check(z)
        except ConfigError as exc:  # broken creds/permissions: loud, fails the run
            return fail_config(str(exc))
        except Exception as exc:  # a transient probe failure is not a config break
            log(f"check failed (non-fatal): {exc}")
        return 0

    if cmd == "backfill":
        rest = argv[2:]
        strict = "--strict" in rest
        dry_run = "--dry-run" in rest
        try:
            _, _, failures = backfill(z, sys.stdin, dry_run=dry_run)
        except ConfigError as exc:
            return fail_config(str(exc))
        except Exception as exc:
            log(f"backfill failed: {exc}")
            return 1 if strict else 0
        return 1 if strict and failures else 0

    # cmd == "reconcile"
    pr = argv[2].lstrip("#") if len(argv) > 2 else ""
    if not pr.isdigit():
        log(f"not a PR number: {argv[2]!r}" if len(argv) > 2 else "missing PR number")
        return 0
    rest = argv[3:]
    create = "--create" in rest
    create_if_open = "--create-if-open" in rest
    strict = "--strict" in rest
    ci_override = None
    if "--ci" in rest:
        ci_override = rest[rest.index("--ci") + 1]

    try:
        reconcile(z, pr, create, ci_override, create_if_open=create_if_open)
    except ConfigError as exc:  # broken creds/permissions: loud, fails the run
        return fail_config(str(exc))
    except Exception as exc:  # cosmetic: never fail the caller over one reaction
        if strict:
            log(f"reconcile failed: {exc}")
            return 1
        log(f"reconcile failed (non-fatal): {exc}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
