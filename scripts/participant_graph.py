#!/usr/bin/env python3
"""Generate a compact SVG snapshot of human participation across Tau Ceti.

A participant is a human GitHub account that has opened a pull request or issue,
participated in one of those conversations (including reviews), or authored a
default-branch commit in any of the four project repositories.

The PR/issue participant connections avoid downloading every individual comment.
The largest repository still takes about a minute to scan, so this is intended for
the daily Pages build, not for a request-time web endpoint. Pure stdlib; `gh` supplies
authenticated GitHub access. Cross-repository queries rely on all four repositories
remaining public.
"""

import argparse
import datetime as dt
import html
import json
import subprocess
import sys
import time


BG = "#101936"
PANEL = "#1b2547"
BAR_BG = "#27335a"
TEXT = "#eef2fb"
MUTED = "#9aa6c9"

REPOSITORIES = [
    ("TauCetiProject/TauCeti", "TauCeti", "#ff9d4d"),
    ("TauCetiProject/TauCetiRoadmap", "TauCetiRoadmap", "#5eead4"),
    ("kim-em/TauCetiWorker", "TauCetiWorker", "#60a5fa"),
    ("TauCetiProject/TauCetiReview", "TauCetiReview", "#c084fc"),
]

# Some GitHub Apps surface through GraphQL as User nodes or without their REST
# `[bot]` suffix. Keep the project-specific aliases explicit; the generic suffix
# check below handles conventional bot accounts.
AUTOMATION_LOGINS = {
    "claude",
    "copilot",
    "copilot-pull-request-reviewer",
    "dependabot",
    "github-actions",
    "tau-ceti-claim-bot",
    "tau-ceti-roadmap-sync",
    "tauceti-review-bot",
    "web-flow",
}


def canonical_human(login: str | None) -> str | None:
    """Return a case-insensitive identity, or None for known automation."""
    if not login:
        return None
    actor = login.casefold()
    unsuffixed = actor.removesuffix("[bot]")
    if actor.endswith("[bot]") or unsuffixed in AUTOMATION_LOGINS:
        return None
    return actor


def gh_json(*args: str):
    """Run one read-only gh query, retrying transient API/transport failures."""
    for attempt in range(3):
        try:
            out = subprocess.run(
                ["gh", *args],
                check=True,
                text=True,
                stdout=subprocess.PIPE,
                timeout=120,
            ).stdout
            return json.loads(out)
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired):
            if attempt == 2:
                raise
            delay = 2 ** attempt
            print(f"GitHub query failed; retrying in {delay}s", file=sys.stderr)
            time.sleep(delay)


def connection_query(field: str) -> str:
    if field == "pullRequests":
        states = "[OPEN, CLOSED, MERGED]"
    elif field == "issues":
        states = "[OPEN, CLOSED]"
    else:
        raise ValueError(f"unsupported connection: {field}")
    return f"""
query($owner: String!, $name: String!, $cursor: String) {{
  repository(owner: $owner, name: $name) {{
    {field}(
      first: 100,
      after: $cursor,
      states: {states},
      orderBy: {{field: CREATED_AT, direction: ASC}}
    ) {{
      nodes {{
        number
        author {{ login }}
        participants(first: 100) {{
          nodes {{ login }}
          pageInfo {{ hasNextPage }}
        }}
      }}
      pageInfo {{ hasNextPage endCursor }}
    }}
  }}
}}
"""


def actors_from_page(page: dict, field: str, repo: str) -> tuple[set[str], bool, str | None]:
    """Extract human actors and outer pagination state from one GraphQL page."""
    connection = page["data"]["repository"][field]
    people: set[str] = set()
    for item in connection["nodes"]:
        participants = item["participants"]
        if participants["pageInfo"]["hasNextPage"]:
            raise RuntimeError(
                f"{repo} {field} #{item['number']} has more than 100 participants; "
                "refusing to undercount"
            )
        logins = [item.get("author", {}).get("login") if item.get("author") else None]
        logins.extend(actor.get("login") for actor in participants["nodes"])
        people.update(actor for login in logins if (actor := canonical_human(login)))
    info = connection["pageInfo"]
    return people, info["hasNextPage"], info.get("endCursor")


def fetch_connection(repo: str, field: str) -> set[str]:
    owner, name = repo.split("/", 1)
    query = connection_query(field)
    people: set[str] = set()
    cursor = None
    while True:
        args = [
            "api", "graphql",
            "-f", f"query={query}",
            "-f", f"owner={owner}",
            "-f", f"name={name}",
        ]
        if cursor is not None:
            args.extend(["-f", f"cursor={cursor}"])
        page = gh_json(*args)
        found, has_next, cursor = actors_from_page(page, field, repo)
        people.update(found)
        if not has_next:
            return people
        if not cursor:
            raise RuntimeError(f"{repo} {field} pagination had no end cursor")


def fetch_contributors(repo: str) -> set[str]:
    """Fetch linked default-branch commit authors.

    Anonymous email identities cannot be deduplicated against linked accounts or
    across repositories, so counting them would make the headline less accurate.
    """
    pages = gh_json(
        "api", "--paginate", "--slurp",
        f"repos/{repo}/contributors?per_page=100",
    )
    people: set[str] = set()
    for page in pages:
        for contributor in page:
            actor = canonical_human(contributor.get("login"))
            if actor is not None:
                people.add(actor)
    return people


def fetch_all() -> dict[str, set[str]]:
    result = {}
    for repo, _, _ in REPOSITORIES:
        result[repo] = (
            fetch_connection(repo, "pullRequests")
            | fetch_connection(repo, "issues")
            | fetch_contributors(repo)
        )
    return result


def load_data(path: str) -> tuple[dict[str, set[str]], str | None]:
    with open(path, encoding="utf-8") as data_file:
        raw = json.load(data_file)
    if "repositories" in raw:
        generated = raw.get("generatedAt")
        raw = raw["repositories"]
    else:
        generated = None
    expected = {repo for repo, _, _ in REPOSITORIES}
    if set(raw) != expected:
        raise ValueError(f"data repositories must be exactly: {', '.join(sorted(expected))}")
    return {
        repo: {actor for login in logins if (actor := canonical_human(login))}
        for repo, logins in raw.items()
    }, generated


def dump_data(path: str, people: dict[str, set[str]], generated: str) -> None:
    with open(path, "w", encoding="utf-8") as out:
        json.dump({
            "generatedAt": generated,
            "repositories": {
                repo: sorted(people[repo])
                for repo, _, _ in REPOSITORIES
            },
        }, out, indent=2)
        out.write("\n")


def render(people: dict[str, set[str]], title: str, out: str, as_of: str) -> int:
    total_people = set().union(*people.values())
    total = len(total_people)
    counts = {repo: len(people[repo]) for repo, _, _ in REPOSITORIES}
    scale = max(total, 1)

    W, H = 980, 430
    L, R, T = 245, 70, 132
    pw = W - L - R
    bar_h, gap = 42, 18

    bars = []
    for i, (repo, label, color) in enumerate(REPOSITORIES):
        count = counts[repo]
        y = T + i * (bar_h + gap)
        width = pw * count / scale
        bars.extend([
            f'<text class="label" x="{L-18}" y="{y+27}">{html.escape(label)}</text>',
            f'<rect x="{L}" y="{y}" width="{pw}" height="{bar_h}" rx="8" fill="{BAR_BG}"/>',
            f'<rect x="{L}" y="{y}" width="{width:.1f}" height="{bar_h}" rx="8" fill="{color}"/>',
            f'<text class="count" x="{L+width+12:.1f}" y="{y+27}">{count}</text>',
        ])

    safe_as_of = html.escape(as_of)
    subtitle = f"{total} people across {len(REPOSITORIES)} repositories as of {as_of}"
    breakdown = ", ".join(
        f"{label}: {counts[repo]}"
        for repo, label, _ in REPOSITORIES
    )
    svg = f'''<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}"
     font-family="ui-sans-serif,system-ui,-apple-system,'Segoe UI',Roboto,sans-serif"
     role="img" aria-labelledby="participation-title participation-description">
  <title id="participation-title">{html.escape(title)}: {html.escape(subtitle)}</title>
  <desc id="participation-description">{html.escape(breakdown)}. People active in several repositories are counted in each bar.</desc>
  <style>
    .title{{fill:{TEXT};font-size:19px;font-weight:600}}
    .total{{fill:{TEXT};font-size:42px;font-weight:700}}
    .sub{{fill:{MUTED};font-size:13px}}
    .label{{fill:{TEXT};font-size:15px;text-anchor:end}}
    .count{{fill:{TEXT};font-size:16px;font-weight:650}}
    .note{{fill:{MUTED};font-size:12.5px}}
  </style>
  <rect x="0.5" y="0.5" width="{W-1}" height="{H-1}" rx="12" fill="{BG}" stroke="{PANEL}"/>
  <text class="title" x="50" y="36">{html.escape(title)}</text>
  <text class="total" x="50" y="91">{total}</text>
  <text class="sub" x="112" y="86">unique people · {safe_as_of}</text>
  {''.join(bars)}
  <text class="note" x="50" y="{H-30}">
    Opened a PR/issue, commented or reviewed, or authored a default-branch commit. Multi-repo participants appear in each bar.
  </text>
</svg>
'''
    with open(out, "w", encoding="utf-8") as svg_file:
        svg_file.write(svg)
    return total


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", help="offline JSON snapshot; otherwise query GitHub with gh")
    ap.add_argument("--dump-data", help="write the fetched, filtered actor snapshot as JSON")
    ap.add_argument("--title", default="Tau Ceti — human participation")
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    today = dt.datetime.now(dt.timezone.utc).date().isoformat()
    try:
        if args.data:
            people, generated = load_data(args.data)
            as_of = generated or today
        else:
            people = fetch_all()
            as_of = today
        if args.dump_data:
            dump_data(args.dump_data, people, as_of)
        total = render(people, args.title, args.out, as_of)
    except (RuntimeError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
        sys.exit(f"participant graph generation failed: {exc}")

    detail = ", ".join(
        f"{label}={len(people[repo])}"
        for repo, label, _ in REPOSITORIES
    )
    print(f"wrote {args.out}: {total} unique people ({detail})")
