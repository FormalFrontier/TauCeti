/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.End.Basic
public import TauCeti.AlgebraicGeometry.AbelianVariety.Trivial

/-!
# The endomorphism ring of the trivial abelian variety

The trivial abelian variety `AbelianVariety.trivial K` has a unique endomorphism, so its
endomorphism ring is the zero ring and the multiplication-by-`n` endomorphism `[n]` is the identity
for every `n` — a check that the construction of
`TauCeti.AlgebraicGeometry.AbelianVariety.End.Basic` is not vacuous.

* `AbelianVariety.mulBy_trivial`: `[n] = 𝟙 (trivial K)`.

That `End (trivial K)` is the zero ring needs no declaration here: `AbelianVariety.End.instUnique`
turns the uniqueness of homomorphisms into the trivial abelian variety
(`AbelianVariety.uniqueHomToTrivial`) into `Unique (End (trivial K))` by instance search, which the
`example` below records.

This is the specialization of the endomorphism ring to the trivial abelian variety, kept apart from
`End.Basic` so that the generic construction does not depend on the trivial-variety theory. It
advances the same roadmap item, `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E, "`[n]` as an
isogeny". No external mathematics is vendored: both facts come from the uniqueness of homomorphisms
out of the zero object, already proved in
`TauCeti.AlgebraicGeometry.AbelianVariety.Trivial`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

variable {K : Type u} [Field K]

noncomputable section

-- The endomorphism ring of the trivial abelian variety is the zero ring, by
-- `AbelianVariety.End.instUnique` applied to `AbelianVariety.uniqueHomToTrivial`.
example : Unique (End (trivial K)) := inferInstance

/-- Every endomorphism of the trivial abelian variety, in particular every `[n]`, is the
identity. -/
@[simp] lemma mulBy_trivial (n : ℤ) :
    mulBy (trivial K) n = 𝟙 (trivial K) :=
  Subsingleton.elim _ _

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
