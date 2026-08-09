/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.Galois.Basic

/-!
# The Galois theory of separable quadratic extensions

Material complementing `Mathlib/FieldTheory/Galois/Basic.lean` for a separable quadratic
extension `L/K`: it has exactly two automorphisms, so the identity and any one nontrivial
automorphism exhaust `Gal(L/K)`, and an element fixed by a nontrivial automorphism lies in the
base field.

Mathlib already supplies the surrounding structure: `Algebra.IsQuadraticExtension` makes `L/K`
finite and normal (`Algebra.IsQuadraticExtension.normal`), hence Galois with separability
(`Algebra.IsQuadraticExtension.isGalois`); `IsGalois.card_aut_eq_finrank` counts the
automorphisms and `IsGalois.mem_range_algebraMap_iff_fixed` characterises the base field.

These are the descent inputs for the quadratic-twist layer of
`TauCetiRoadmap/EllipticCurves/README.md` (§Layer 5), consumed by
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisDescent.lean` and by
`TauCeti/RingTheory/Norm/Quadratic.lean`, which expresses the trace and norm of a
separable quadratic extension through its nontrivial automorphism.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/FieldTheory/Galois/Basic.lean` at the roadmap's pin `bc2fe8ff7396`, FLT PR #1088,
Apache 2.0). That file's own header reads `Authors: Kevin Buzzard, Claude`; following this
repository's convention for adapted material, the upstream authorship is credited here rather
than in the copyright header. Only the results consumed downstream are ported; the rest of
the source file is deferred to the Tau Ceti PRs that consume it.
-/

public section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

namespace Algebra.IsQuadraticExtension

/-- A separable quadratic extension has exactly two automorphisms. -/
theorem card_algEquiv_eq_two : Nat.card (L ≃ₐ[K] L) = 2 := by
  rw [IsGalois.card_aut_eq_finrank]
  exact finrank_eq_two K L

/-- The only automorphisms of a separable quadratic extension are the identity and any given
nontrivial automorphism. -/
theorem algEquiv_eq_one_or_eq {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) (φ : L ≃ₐ[K] L) : φ = 1 ∨ φ = σ := by
  rcases eq_or_ne φ 1 with h1 | h1
  · exact .inl h1
  · exact .inr (((Nat.card_eq_two_iff' 1).mp (card_algEquiv_eq_two K L)).unique h1 hσ)

/-- An element fixed by a nontrivial automorphism — hence, `Gal(L/K)` having order two, by all of
`Gal(L/K)` — lies in the base field. -/
theorem mem_range_algebraMap_of_apply_eq {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) {x : L} (hx : σ x = x) :
    x ∈ Set.range (algebraMap K L) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro φ
  rcases algEquiv_eq_one_or_eq K L hσ φ with rfl | rfl
  · exact AlgEquiv.one_apply x
  · exact hx

/-- A separable quadratic extension has a nontrivial automorphism. -/
theorem exists_algEquiv_ne_one : ∃ σ : L ≃ₐ[K] L, σ ≠ 1 :=
  ((Nat.card_eq_two_iff' 1).mp (card_algEquiv_eq_two K L)).exists

/-- The automorphism group of a separable quadratic extension consists of the identity and one
nontrivial element. -/
theorem univ_eq_pair [DecidableEq (L ≃ₐ[K] L)] {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    (Finset.univ : Finset (L ≃ₐ[K] L)) = {1, σ} :=
  (Finset.eq_univ_of_forall fun φ ↦ by simpa using algEquiv_eq_one_or_eq K L hσ φ).symm

end Algebra.IsQuadraticExtension

end
