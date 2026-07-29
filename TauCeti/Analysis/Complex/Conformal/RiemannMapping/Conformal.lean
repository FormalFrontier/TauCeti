/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Biholomorph
public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Existence

/-!
# The Riemann map as a conformal partial homeomorphism

The Riemann mapping theorem in `RiemannMapping/Existence.lean` produces a holomorphic bijection
between a simply connected proper domain and the open unit disc, together with a holomorphic
inverse. This file packages the same result as an `OpenPartialHomeomorph ℂ ℂ`. Its source and
target are exactly the domain and the disc, and both it and its inverse are holomorphic and
conformal on those sets.

This is the packaged-equivalence and `ConformalAt` companion required by the generality bar in
`TauCetiRoadmap/ConformalMapping/README.md`: the roadmap asks that the unbundled Riemann-map
statement be accompanied by the natural equivalence and conformality API.

## Main result

* `TauCeti.riemannMapping_openPartialHomeomorph` — a Riemann map packaged with its inverse,
  source, target, holomorphy, and conformality.
* `TauCeti.riemannMapping_homeomorph` — the resulting homeomorphism
  `Ω ≃ₜ Complex.UnitDisc`.

## Coordination with upstream Mathlib

The Riemann mapping theorem is being formalized upstream in
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505). This L3 theorem is
an explicitly temporary shim: delete it and refactor consumers to the public human-curated
Mathlib theorem and packaging once those land.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6 §1.
-/

public section

namespace TauCeti

open Complex Metric Set

/-- **The Riemann mapping theorem as a homeomorphism.** A simply connected open proper subset of
`ℂ`, regarded as a subtype, is homeomorphic to `Complex.UnitDisc`.

The homeomorphism is induced by the holomorphic bijection supplied by `TauCeti.riemannMapping`;
its forward and inverse formulas are
`DifferentiableOn.toHomeomorphOfBijOn_apply` and
`DifferentiableOn.toHomeomorphOfBijOn_symm_apply`. -/
theorem riemannMapping_homeomorph {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ) :
    Nonempty (Ω ≃ₜ Complex.UnitDisc) := by
  obtain ⟨f, hbij, hfd, -⟩ := riemannMapping hΩo hΩc hΩ
  exact ⟨TauCeti.DifferentiableOn.toHomeomorphOfBijOn hfd hΩo hbij⟩

/-- **The Riemann mapping theorem as a conformal open partial homeomorphism.** A simply connected
open proper subset `Ω` of `ℂ` is the source of an open partial homeomorphism whose target is the
open unit disc. The map and its inverse are holomorphic and conformal throughout their respective
domains. -/
theorem riemannMapping_openPartialHomeomorph {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      e.source = Ω ∧
      e.target = ball (0 : ℂ) 1 ∧
      DifferentiableOn ℂ e Ω ∧
      DifferentiableOn ℂ e.symm (ball (0 : ℂ) 1) ∧
      (∀ z ∈ Ω, ConformalAt e z) ∧
      ∀ w ∈ ball (0 : ℂ) 1, ConformalAt e.symm w := by
  obtain ⟨f, hbij, hfd, hinvd, -, -⟩ :=
    exists_bijOn_ball_differentiableOn_invFunOn hΩo hΩc hΩ
  refine ⟨TauCeti.DifferentiableOn.toOpenPartialHomeomorph hfd hΩo hbij.injOn,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact TauCeti.DifferentiableOn.toOpenPartialHomeomorph_source hfd hΩo hbij.injOn
  · exact
      (TauCeti.DifferentiableOn.toOpenPartialHomeomorph_target hfd hΩo hbij.injOn).trans
        hbij.image_eq
  · rw [TauCeti.DifferentiableOn.toOpenPartialHomeomorph_coe hfd hΩo hbij.injOn]
    exact hfd
  · rw [TauCeti.DifferentiableOn.toOpenPartialHomeomorph_coe_symm hfd hΩo hbij.injOn]
    exact hinvd
  · exact fun z hz =>
      TauCeti.DifferentiableOn.toOpenPartialHomeomorph_conformalAt hfd hΩo hbij.injOn hz
  · intro w hw
    exact TauCeti.DifferentiableOn.toOpenPartialHomeomorph_conformalAt_symm hfd hΩo hbij.injOn
      (hbij.image_eq ▸ hw)

end TauCeti
