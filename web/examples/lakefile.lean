import Lake
open Lake DSL

-- This project exists to type-check the theorems the site showcases against the real library,
-- and to extract highlighted snippets for Verso. It therefore compiles the TauCeti library
-- itself, which forces an invariant: its toolchain and its Mathlib pin must be EXACTLY the ones
-- the root project builds with. `lean-toolchain` here is a copy of the root `lean-toolchain`, and
-- the Mathlib revision below is a copy of the root `lake-manifest.json` pin.
--
-- The invariant is not a nicety. When these drift, this project compiles the root library against
-- a Mathlib and a Lean that library was never written for, and the build fails on whatever file
-- happens to use something newer -- with the root project's own CI perfectly green, because
-- nothing outside pages.yml builds this project. That is exactly what happened in September 2026:
-- the daily bump moved the root pins every day and never touched this file, and the site build
-- broke on a Deck transformation instance five days after the two pins parted company.
--
-- Conversely, once they agree, "this project builds the TauCeti library" reduces to "the root
-- project builds the TauCeti library", which is a required check on every pull request. That is
-- what makes the site build trustworthy without a second expensive CI job.
--
-- `scripts/test_web_pins.py` enforces all of this, and `.github/workflows/update.yml` carries
-- these copies along whenever it bumps the root pins.

-- Must equal the `subverso` revision resolved in `web/lake-manifest.json`, which the Verso site
-- builds against. SubVerso deliberately supports being built on a DIFFERENT Lean toolchain from
-- the Verso that reads its output -- that is the entire reason it exists as a separate package,
-- and it is why this project can sit on the root toolchain while `web/` stays on Verso's. What it
-- does not promise is compatibility between different SubVerso VERSIONS: its data format is an
-- implementation detail, so both sides must resolve the same commit.
require subverso from git
  "https://github.com/leanprover/subverso" @ "verso-v4.32.0"

-- Must equal the `mathlib` revision in the root `lake-manifest.json`. This top-level pin is what
-- overrides the `master` revision the root package requests transitively.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "5fcc6656691ed31965746c369f41fa75e567ac9d"

-- The real Tau Ceti library, from the repository root, so the showcased theorems are
-- type-checked against exactly the library that proves them.
require «TauCeti» from "../.."

package «examples» where

@[default_target]
lean_lib «Examples» where
