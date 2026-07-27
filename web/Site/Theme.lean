import VersoBlog
open Verso Genre Blog Site Syntax

open Output Html Template Theme in
def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <html lang="en">
        <head>
          <meta charset="utf-8"/>
          <meta name="viewport" content="width=device-width, initial-scale=1"/>
          <meta name="color-scheme" content="dark"/>
          <link rel="icon" href="static/favicon.ico" sizes="any"/>
          <link rel="icon" type="image/png" sizes="32x32" href="static/favicon-32x32.png"/>
          <link rel="icon" type="image/png" sizes="16x16" href="static/favicon-16x16.png"/>
          <link rel="apple-touch-icon" sizes="180x180" href="static/apple-touch-icon.png"/>
          <link rel="preconnect" href="https://fonts.googleapis.com"/>
          <link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Chakra+Petch:wght@400;500;600;700&display=swap"/>
          <title>{{ (← param (α := String) "title") }} " — Tau Ceti"</title>
          {{← builtinHeader }}
          <link rel="stylesheet" href="static/style.css"/>
          <script src="static/site.js" defer="defer"></script>
        </head>
        <body>
          <header class="site-nav">
            <div class="nav-inner">
              <a class="brand" href="."><img src="static/header.png" alt="Tau Ceti"/></a>
              <nav class="nav-links">
                <a href=".">"Home"</a>
                <a href="statistics">"Statistics"</a>
                <a href="about">"About"</a>
                <a href="https://github.com/TauCetiProject/TauCeti">"GitHub"</a>
              </nav>
            </div>
          </header>
          <main>
            {{ (← param "content") }}
          </main>
          <footer class="site-footer">
            <div class="foot-inner">
              <p class="foot-tag">"Let’s do lots of maths."</p>
              <ul class="foot-links">
                <li><a href="https://github.com/TauCetiProject/TauCeti">"TauCeti"</a></li>
                <li><a href="https://github.com/TauCetiProject/TauCetiRoadmap">"TauCetiRoadmap"</a></li>
                <li><a href="https://github.com/TauCetiProject/TauCetiReview">"TauCetiReview"</a></li>
              </ul>
              <p class="foot-legal">"AI-authored Lean mathematics · Apache-2.0"</p>
            </div>
          </footer>
        </body>
      </html>
    }}
  }
  |>.override #[] ⟨do
    return {{
      <div class="frontpage">
        <section class="hero">
          <img class="hero-img" src="static/tauceti-collaboration.jpg"
               alt="A hexapus reaching toward an AI across a tide pool, beneath twin suns and a ringed planet."/>
          <div class="hero-copy">
            <h1 class="hero-title">"Tau Ceti"</h1>
            <p class="hero-tag">"Let’s do lots of maths."</p>
            <p class="hero-sub">"AI-authored Lean mathematics, directed by a human-owned roadmap and gated by open, adversarial review."</p>
            <div class="cta-row">
              <a class="cta" href="https://github.com/TauCetiProject/TauCeti">"Explore the code →"</a>
              <a class="cta secondary" href="docs/">"Read the docs →"</a>
            </div>
          </div>
        </section>

        <section class="pillars">
          <div class="pillar">
            <h3>"Humans own the roadmap"</h3>
            <p>"Mathematicians set the targets in a separate, human-reviewed roadmap repository. People choose the maths."</p>
          </div>
          <div class="pillar">
            <h3>"AIs write the code"</h3>
            <p>"AI agents author the Lean proofs and open pull requests — every theorem machine-checked, no sorries, no stray axioms."</p>
          </div>
          <div class="pillar">
            <h3>"Open review gates everything"</h3>
            <p>"AI reviewers judge each PR against fixed, open-source rubrics — correctness, reuse, API, naming, generality — before it can merge."</p>
          </div>
        </section>

        <section class="band roadmap">
          <h2 class="section-title">"On the roadmap"</h2>
          <div class="cards four">
            <div class="card"><h3>"Universal covers"</h3></div>
            <div class="card"><h3>"The Jacobian challenge"</h3></div>
            <div class="card"><h3>"Reductive algebraic groups"</h3></div>
            <div class="card"><h3>"Partial differential equations"</h3></div>
          </div>
        </section>

        <section class="band growth">
          <h2 class="section-title">"Growing fast"</h2>
          <a class="growth-link" href="statistics">
            <img class="growth-img" src="static/loc-tauceti.svg"
                 alt="Tau Ceti: lines of Lean by date"/>
            <span class="growth-cta">"See the statistics →"</span>
          </a>
        </section>

        <section class="band repos">
          <h2 class="section-title">"Three repositories"</h2>
          <div class="cards three">
            <a class="card repo" href="https://github.com/TauCetiProject/TauCeti">
              <h3>"TauCeti"</h3>
              <p>"The AI-authored Lean mathematics."</p>
            </a>
            <a class="card repo" href="https://github.com/TauCetiProject/TauCetiRoadmap">
              <h3>"TauCetiRoadmap"</h3>
              <p>"The human-controlled roadmaps that direct the work."</p>
            </a>
            <a class="card repo" href="https://github.com/TauCetiProject/TauCetiReview">
              <h3>"TauCetiReview"</h3>
              <p>"The review rubrics and the machinery that runs review."</p>
            </a>
          </div>
        </section>

        <section class="band taste">
          <h2 class="section-title">"A taste of the maths"</h2>
          <p class="taste-note">"Four real theorems — one for each roadmap theme — extracted from the library and type-checked when this page is built, so they cannot drift out of date."</p>
          <div class="carousel">
            <button class="carousel-arrow prev" type="button" aria-label="Previous example">"‹"</button>
            <div class="carousel-track">
              {{← param "content" }}
            </div>
            <button class="carousel-arrow next" type="button" aria-label="Next example">"›"</button>
          </div>
        </section>
      </div>
    }}, id⟩
