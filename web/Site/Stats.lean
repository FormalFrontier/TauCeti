import VersoBlog
open Verso Genre Blog
open Verso.Output Verso.Output.Html

/-- The two "lines of code by date" charts. The SVGs are regenerated at each site
deploy (and daily) into `static_files/` by the `pages` workflow, so this page never
needs touching as the project grows. They are embedded as a raw HTML blob: each
`<img>` simply points at the static asset. -/
def locGraphs : Html := {{
  <div class="loc-graphs">
    <figure class="loc-figure">
      <img class="loc-graph" src="static/loc-tauceti.svg"
           alt="Tau Ceti: lines of Lean by date"/>
      <figcaption>"The Lean library under " <code>"TauCeti/"</code> ", total lines by date."</figcaption>
    </figure>
    <figure class="loc-figure">
      <img class="loc-graph" src="static/loc-roadmap.svg"
           alt="Tau Ceti Roadmap: lines written by date"/>
      <figcaption>"The human-owned roadmap repository, total lines by date."</figcaption>
    </figure>
  </div>
}}

/-- The per-roadmap chart: cumulative net lines of Lean, split by the roadmap each
merged PR advances (its `roadmap/<Area>` label). Regenerated at each deploy by the
`pages` workflow (`scripts/loc_roadmap_graph.py`), from the PR labels rather than git,
so it too needs no committed state. Embedded as a raw HTML blob pointing at the asset. -/
def roadmapGraph : Html := {{
  <figure class="loc-figure loc-figure-wide">
    <img class="loc-graph" src="static/loc-per-roadmap.svg"
         alt="Tau Ceti: cumulative net lines of Lean per roadmap, over time"/>
    <figcaption>"Net lines added or refactored per roadmap, stacked, by the date each PR merged."</figcaption>
  </figure>
}}

/-- A current snapshot of participation across the four project repositories: the GitHub
accounts that remain once recognised automation is excluded, which is not the same as a
verified count of people. Regenerated daily by the `pages` workflow
(`scripts/participant_graph.py`) from GitHub PR/issue participant connections and
default-branch commit contributors. -/
private def participationGraph : Html := {{
  <figure class="loc-figure loc-figure-wide">
    <img class="loc-graph" src="static/participation.svg"
         alt="Participation across the four Tau Ceti repositories, by repository"/>
    <figcaption>"Participating accounts by repository, once recognised automation is excluded; an account active in several repositories appears in several bars."</figcaption>
  </figure>
}}

#doc (Page) "Statistics" =>

How much mathematics has Tau Ceti formalized, and how fast is the roadmap that
directs it growing? Each chart plots the total number of lines present at every
commit, counted straight from the git history and rebuilt from scratch at each
deploy, so the figures cannot drift.

:::blob locGraphs
:::

The vertical scales differ by an order of magnitude and on purpose: the library is
measured in tens of thousands of lines of Lean, the roadmap in thousands of lines of
prose and target statements. The library figure counts only the mathematics — the
files under `TauCeti/` — not the website or tooling.

Which roadmap is all that Lean serving? Every pull request is labelled with the
roadmap it advances, so we can split the library by roadmap. The chart below stacks
the net lines each roadmap has accrued — every merged PR's additions minus its
deletions, attributed to its roadmap — by the day the PR merged. Because it sums
diffs rather than counting the lines in the tree, a line later rewritten counts under
both PRs, so this measures work landed per roadmap, not a snapshot line count.
Infrastructure and refactor PRs, which advance no roadmap, are left out.

:::blob roadmapGraph
:::

Who has taken part? The snapshot below counts GitHub accounts that have
opened a pull request or issue, participated in those conversations (including
reviews), or authored a commit on the default branch of TauCeti, TauCetiRoadmap,
TauCetiWorker, or TauCetiReview. Accounts recognised as automation are dropped:
logins carrying GitHub's `[bot]` suffix, together with the project's own automation
aliases. Nothing verifies that the accounts left over belong to people, so any
automation the filter does not recognise is still counted. The headline
deduplicates accounts across all four repositories; the repository bars
deliberately overlap.

:::blob participationGraph
:::
