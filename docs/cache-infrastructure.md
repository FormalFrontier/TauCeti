# Lake artifact cache infrastructure

Where the build cache lives, who owns it, and which knob feeds which workflow.

## Mathlib download cache (GitHub Actions)

The main `ci.yml` workflow maintains a narrow snapshot of Mathlib's compressed download store:
`$MATHLIB_CACHE_DIR/*.ltar`. The `.ltar` files are content-addressed; cache-tool scratch files,
executables, and the unpacked `.lake` tree are not included. The local
`.github/actions/restore-mathlib-ltars` action sets `MATHLIB_CACHE_DIR` job-wide through
`$GITHUB_ENV`, defaulting to `$GITHUB_WORKSPACE/.mathlib-ltar-cache`; its `cache-dir` input can
override that location. Main publishes only after a non-exact restore: an exact key is immutable
and already contains this pin's snapshot. Before publishing, main runs `lake exe cache clean` so
the snapshot contains only files needed by the current pin; if pruning fails, it skips publication
instead of saving an unpruned snapshot. PR and merge-group jobs in `pr-build.yml` may restore this
trusted snapshot but never publish one. `pages.yml` and
`pr-profile.yml` are intentionally outside this initial rollout: `ci.yml` is included as the sole
publisher and `pr-build.yml` as the highest-volume consumer. `pr-profile.yml` has comparable
per-PR fetch volume but remains outside as a rollout control. Both excluded workflows continue
fetching into Mathlib's default cache directory.

Keys have the shape
`mathlib-ltar-v1-<os>-<arch>-<lean-toolchain hash>-<lake-manifest hash>`. An exact match reuses the
current pin. The restore prefix omits the manifest hash, so a Mathlib-only pin bump can start from
the newest snapshot for the same Lean toolchain and fetch only missing files. A toolchain bump has
no prefix match. In every case, `lake exe cache get` remains authoritative and downloads whatever
the snapshot lacks. This design mirrors Mathlib's own cache-snapshot warming in
`.github/workflows/build_template.yml` and `.github/actions/get-cache`, using `actions/cache`
instead of per-run artifacts.

GitHub Actions cache entries are immutable. If an entry is poisoned or the format becomes
incompatible, bump `mathlib-ltar-v1` once in
`.github/actions/restore-mathlib-ltars/action.yml`. To discard a single entry instead, find it with
`gh cache list --repo TauCetiProject/TauCeti` and delete its exact key with
`gh cache delete <key> --repo TauCetiProject/TauCeti`. A failed fetch also retries once with
`lake exe cache get!`, which forces every linked file to be downloaded and unpacked again.

## Cloudflare account

| | |
|---|---|
| Account | `kim@lean-fro.org` |
| Account ID | `d789bf36d237e0cb313be59b927c82bd` |
| Dashboard | https://dash.cloudflare.com/d789bf36d237e0cb313be59b927c82bd |
| R2 bucket | `tauceti-cache` |
| Registrar | `taucetiproject.org`, bought through Cloudflare Registrar in this same account |

The account ID is not a secret: it is the subdomain of the S3 endpoint below. If the dashboard
link 404s, the login you used is not a member of that account.

The account holds other buckets unrelated to this project. Only `tauceti-cache` is ours.

## Endpoints

Reads are anonymous. Lake's download path issues plain unauthenticated `curl` GETs and has no way
to sign them, so the read host must be public; only uploads use a key.

| Purpose | Value | Used by |
|---|---|---|
| `LAKE_CACHE_ARTIFACT_ENDPOINT_PUBLIC` | `https://cache.taucetiproject.org/artifacts` | `pr-build.yml` read |
| `LAKE_CACHE_REVISION_ENDPOINT_PUBLIC` | `https://cache.taucetiproject.org/revisions` | `pr-build.yml` read |
| `LAKE_CACHE_ARTIFACT_ENDPOINT` | `https://d789bf36….r2.cloudflarestorage.com/tauceti-cache/artifacts` | `ci.yml` upload |
| `LAKE_CACHE_REVISION_ENDPOINT` | `https://d789bf36….r2.cloudflarestorage.com/tauceti-cache/revisions` | `ci.yml` upload |
| `LAKE_CACHE_KEY` (secret) | `<ACCESS_KEY_ID>:<SECRET>`, read-write | `ci.yml`, `publish-lake-cache` job only |

Lake service names: `tauceti-public` for reads, `tauceti-r2` for uploads. Object keys are
`artifacts/TauCetiProject/TauCeti/<hash>.art`, so the endpoint variables hold only the prefix and
Lake appends the scope.

## Why the upload is its own job

`ci.yml` publishes in two jobs. `build` compiles main and *stages* the artifacts; the separate
`publish-lake-cache` job holds `LAKE_CACHE_KEY` and uploads them. The split is a trust boundary,
not a convenience.

`build` runs `lake build` unsandboxed, as the runner user, on whatever landed on main, and Lean
executes code at elaboration time. `run_cmd`, `initialize` and macro-time IO are all unrestricted:
the scope, import-boundary and `set_option` guards are textual scans, and a file that writes
during elaboration exits 0 with no diagnostic. Such code runs with the runner user's privileges,
so it can rewrite `$HOME/.elan/bin/lake`, prepend a directory to every later step's `PATH` through
`$GITHUB_PATH`, or set `LD_PRELOAD` or `BASH_ENV` for every later step through `$GITHUB_ENV`.
Hardening the individual commands that touch the key does not help: any secret placed in a later
step of that job is a secret placed in reach of code that landed on main. (This is not reachable
from an unmerged PR, which compiles only under landrun in `pr-build.yml`, with writes confined to
`base/.lake` and no secret in the sandbox's `--env` allowlist.)

So `build` runs `lake cache stage`, which needs no credential and touches no network, and hands
the staging directory to `publish-lake-cache` as a workflow artifact: about 60 MB, one flat
directory of `.ltar` files plus the mappings. That job checks out exactly one file and has no Lake
workspace and no dependencies, so no code from this repository or from Mathlib runs anywhere in
it, and it takes no `GITHUB_TOKEN` scopes. `lake cache put-staged` is the command for exactly
this: it does not configure the workspace and so does not execute arbitrary user code.

Nothing the build job reports is trusted there. The one file `publish-lake-cache` checks out is
`lean-toolchain`, because which toolchain it installs decides which `lake` binary handles the key,
and `elan toolchain install owner/repo:tag` fetches from that repository's releases. Taking that
name from the build job would hand the choice straight back to code that landed on `main`, which
can rewrite `lean-toolchain` on disk or poison the reporting step through `$GITHUB_ENV`. The pin
is read from the repository instead, its shape is re-checked against `leanprover/lean4:` releases,
and it must equal what the build job reports it built with.

Because it does not configure the workspace, `put-staged` cannot derive the toolchain and platform
halves of the upload scope, so the job passes `--rev` and `--toolchain` explicitly and relies on
the default of no platform. That reproduces the scope `lake cache put` derived, verified by
comparing the revision URLs the two commands emit, which are identical:
`revisions/TauCetiProject/TauCeti/tc/leanprover--lean4---<version>/<rev>.jsonl`. The platform is
absent because `lakefile.toml` sets `platformIndependent = true`; the staging step fails loudly if
that ever stops being true, since a silent mismatch would publish under a scope `pr-build` never
reads.

The staged tree arrives from a job that ran code that landed on main, so `publish-lake-cache`
checks it before pointing Lake at it: the tree must be a flat directory of regular files, and
every string in the mappings must be a plain `<hash>.<ext>` artifact name. Lake parses an artifact
name as everything after the first dot and joins it to the staging directory without checking that
the result stays inside, so an unchecked name like `0.art/../../../proc/self/environ` would
otherwise have Lake read the publishing job's environment and `PUT` it into a publicly readable
bucket.

## Why a custom domain

Cloudflare rate-limits `r2.dev` public bucket URLs and documents them as development-only
(https://developers.cloudflare.com/r2/buckets/public-buckets/); exceeding the limit returns HTTP 429
with Cloudflare error 1015
(https://developers.cloudflare.com/support/troubleshooting/http-status-codes/cloudflare-1xxx-errors/).
An R2 custom domain carries no such limit, so reads go through `cache.taucetiproject.org`. The
bucket's `r2.dev` URL is disabled, so there is nothing to silently fall back to.

A custom domain requires the zone in the same Cloudflare account as the bucket
(https://developers.cloudflare.com/r2/buckets/public-buckets/#add-your-domain-to-cloudflare).
Attaching only a subdomain while keeping DNS elsewhere needs Business (partial CNAME setup,
https://developers.cloudflare.com/dns/zone-setups/partial-setup/) or Enterprise (subdomain zone,
https://developers.cloudflare.com/dns/zone-setups/subdomain-setup/), hence a domain registered
in-account.

## Edge cache

`.art` is not one of the extensions Cloudflare caches by default
(https://developers.cloudflare.com/cache/concepts/default-cache-behavior/), so artifact reads are
cached by an explicit Cache Rule. Dashboard: Caching, then Cache Rules, on the
`taucetiproject.org` zone.

Rule expression:

```
(http.host eq "cache.taucetiproject.org" and starts_with(http.request.uri.path, "/artifacts/"))
```

Settings: cache eligibility "Eligible for cache"; Edge TTL "Ignore cache-control header and use
this TTL", one month. Browser TTL left at the default.

The rule is scoped to `/artifacts/` on purpose. Those keys are immutable content hashes, so a long
TTL is always safe. `/revisions/` is deliberately left uncached: a lookup for a revision that has
not been published yet returns 404, and a long-cached 404 would hide it from a later build once
main publishes it. Revision lookups are a handful of requests per build against a thousand or more
artifact fetches, so nothing is lost by leaving them alone.

Tiered Cache is a separate per-zone toggle and is not part of the rule above: Cloudflare documents
it as something you enable, under Caching, then Tiered Cache
(https://developers.cloudflare.com/cache/how-to/tiered-cache/). Smart topology is available on
every plan and needs no further configuration once Tiered Cache is on. Check the toggle on the
`taucetiproject.org` zone rather than assuming it; the Cache Rule above is what does the work
either way.

To check the rule is live, request the same artifact twice. `curl -I` works as well as a GET:
Cloudflare converts a cacheable `HEAD` into a `GET`, fetching and caching the full response and
returning only the headers (https://developers.cloudflare.com/cache/concepts/cache-behavior/), so a
`HEAD` reports the same `cf-cache-status` a `GET` would.

```bash
U=https://cache.taucetiproject.org/artifacts/TauCetiProject/TauCeti/<hash>.art
curl -s -o /dev/null -D - "$U" | grep -i cf-cache-status   # MISS on the first request
curl -s -o /dev/null -D - "$U" | grep -i cf-cache-status   # HIT on the second
```

`DYNAMIC` means the expression is not matching; `BYPASS` means something overrides it.
The hit ratio that actually determines the saving is under Caching, then Analytics.

## Cost

Egress from R2 is free. Reads are Class B operations: 10M per month free, then $0.36 per million
(https://developers.cloudflare.com/r2/pricing/, standard storage, prices read 2026-08-04).

Measured 2026-08-04:

| | |
|---|---|
| Artifacts fetched per build | 1,224 |
| Mean artifact size | 14 KiB, so about 17 MiB per build across those 1,224 fetches |
| `pr-build` runs per day | 734 |
| Class B reads | about 27M per month |
| Billable after the 10M free tier | about 17M, so roughly **$6 per month** |
| Egress | about 375 GB per month, free |
| Storage and Class A writes | a few GB and well inside the 1M free writes, so negligible |

Treat that as a range of roughly $4 to $9. The run count came from one busy day, and the artifact
count per build varies with how much of the dependency cone a PR invalidates.

To re-estimate, take an artifact count from any `sandboxed-build` job and a day's run count:

```bash
JOB=$(gh run view --repo TauCetiProject/TauCeti <run-id> \
        --json jobs -q '.jobs[]|select(.name=="sandboxed-build")|.databaseId' | head -1)
gh run view --repo TauCetiProject/TauCeti --job "$JOB" --log | grep -c 'downloaded artifact'
gh api -X GET repos/TauCetiProject/TauCeti/actions/workflows/pr-build.yml/runs \
  -f created=YYYY-MM-DD -q .total_count
```

Then reads per month is roughly `artifacts x runs_per_day x 30`, and the bill is
`max(0, reads - 10e6) / 1e6 x $0.36`.

That arithmetic charges every artifact fetch as a Class B read, so it is the bill without the edge
cache, and an upper bound on the real one. A custom domain puts Cloudflare Cache in front of the
bucket (https://developers.cloudflare.com/r2/buckets/public-buckets/#caching), and the Cache Rule
under [Edge cache](#edge-cache) is what claims that saving: a request answered at the edge never
reaches R2 and so is never billed as a Class B operation. The hit ratio under Caching, then
Analytics says how much of the 27M is still reaching the bucket.

## Related

- `pr-build.yml` retries a partial fetch and discards the cache rather than handing it to the
  offline sandbox. See the comment at that step for when part of it can be simplified.
- https://github.com/leanprover/lean4/issues/14670, open: Lake fails a build over a cache miss it
  has already recovered from.
- https://github.com/leanprover/lean4/pull/14651, merged: `lake cache get` exit status was
  unreliable. Ships in v4.34.0, not backported to v4.33.0.
