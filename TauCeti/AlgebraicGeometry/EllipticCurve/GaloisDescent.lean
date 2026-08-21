/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import TauCeti.FieldTheory.Galois.Basic

/-!
# Galois descent for Weierstrass curve data

Let `L/K` be a separable quadratic extension. Data attached to a Weierstrass curve over `L` and
fixed by the nontrivial `σ ∈ Gal(L/K)` descends to `K`, because an element of `L` fixed by `σ` is
already in `K` (`Algebra.IsQuadraticExtension.mem_range_algebraMap_of_apply_eq`). Two descent
results are proved here:

* `WeierstrassCurve.VariableChange.exists_baseChange_eq_of_map_eq`: an admissible change of
  variables over `L` fixed by `σ` is the base change of one over `K`;
* `WeierstrassCurve.Affine.Point.exists_baseChange_eq_of_map_eq`: an affine point of `W` over
  `L` fixed by `σ` is the base change of a point over `K`.

Both are stated with `σ` an explicit nontrivial automorphism rather than a quantifier over
`Gal(L/K)`: for a quadratic extension the two are equivalent, and the consumers have a
distinguished `σ` in hand.

These are the descent steps of the quadratic-twist layer of
`TauCetiRoadmap/EllipticCurves/README.md` (§Layer 5): the twist point isomorphism and the
classification of twists both descend `L`-data fixed by the Galois action to `K`-data.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/GaloisDescent.lean` at the roadmap's pin
`bc2fe8ff7396`, FLT PR #1088, Apache 2.0). That file's own header reads
`Authors: Kevin Buzzard, Michael Stoll, Claude`; following this repository's convention for
adapted material, the upstream authorship is credited here rather than in the copyright header.
Ported against Mathlib's own `VariableChange.baseChange` and `Affine.Point.baseChange` rather
than the source's complements to them.
-/

public section

open Algebra.IsQuadraticExtension

namespace WeierstrassCurve

open scoped WeierstrassCurve.Affine

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]
variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

namespace VariableChange

/-- **Galois descent for changes of variables.** A change of variables over `L` fixed by the
nontrivial `σ ∈ Gal(L/K)` has all its coefficients in `K`, so it is the base change of a change
of variables over `K`. -/
lemma exists_baseChange_eq_of_map_eq {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) {C : VariableChange L}
    (hCinv : C.map σ.toAlgHom.toRingHom = C) : ∃ CK : VariableChange K, CK.baseChange L = C := by
  have mem : ∀ x : L, σ x = x → x ∈ Set.range (algebraMap K L) :=
    fun x hx ↦ mem_range_algebraMap_of_apply_eq K L hσ hx
  have hu : σ (C.u : L) = (C.u : L) := by
    simpa [Units.coe_map] using congrArg (fun D ↦ (D.u : L)) hCinv
  have hr : σ C.r = C.r := by
    simpa using congrArg VariableChange.r hCinv
  have hs : σ C.s = C.s := by
    simpa using congrArg VariableChange.s hCinv
  have ht : σ C.t = C.t := by
    simpa using congrArg VariableChange.t hCinv
  obtain ⟨uK, huK⟩ := mem _ hu
  obtain ⟨rK, hrK⟩ := mem _ hr
  obtain ⟨sK, hsK⟩ := mem _ hs
  obtain ⟨tK, htK⟩ := mem _ ht
  have huK' : uK ≠ 0 := by rintro rfl; rw [map_zero] at huK; exact C.u.ne_zero huK.symm
  refine ⟨⟨Units.mk0 uK huK', rK, sK, tK⟩, VariableChange.ext (Units.ext ?_) hrK hsK htK⟩
  simpa [VariableChange.baseChange] using huK

end VariableChange

namespace Affine.Point

/-- **Galois descent for points.** A point of `W(L)` fixed by the nontrivial `σ ∈ Gal(L/K)`
(hence, as `[L : K] = 2`, by all of `Gal(L/K)`) is the base change of a point of `W(K)`: its
coordinates, being fixed by `σ`, lie in `K`. -/
theorem exists_baseChange_eq_of_map_eq [DecidableEq K] [DecidableEq L]
    {W : WeierstrassCurve K} {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) {R : (W⁄L).Point}
    (hR : Affine.Point.map σ.toAlgHom R = R) :
    ∃ Q : (W⁄K).Point, Affine.Point.baseChange K L Q = R := by
  rcases R with _ | ⟨x, y, h⟩
  · exact ⟨0, Affine.Point.map_zero _⟩
  · rw [Affine.Point.map_some] at hR
    injection hR with hx hy
    obtain ⟨x₀, rfl⟩ := mem_range_algebraMap_of_apply_eq K L hσ hx
    obtain ⟨y₀, rfl⟩ := mem_range_algebraMap_of_apply_eq K L hσ hy
    -- `Algebra.ofId K L` and `algebraMap K L` are the same map; make the bridge explicit.
    simp only [← Algebra.ofId_apply] at h ⊢
    exact ⟨.some x₀ y₀ ((Affine.baseChange_nonsingular W
      (f := Algebra.ofId K L) (FaithfulSMul.algebraMap_injective K L) x₀ y₀).mp h),
      Affine.Point.map_some _ _⟩

end Affine.Point

end WeierstrassCurve

end
