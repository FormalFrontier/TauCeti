/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.EllipticCurve
public import Mathlib.NumberTheory.Height.Northcott
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.XRep

/-!
# The naïve height on an elliptic curve, and the approximate parallelogram law

For an affine point `P` of a Weierstrass curve over a field `K` with a theory of heights, the
*naïve height* is `h(P) = logHeight (x(P))`, the logarithmic height of the projective
`x`-coordinate `P.xRep`. The main result is the **approximate parallelogram law**,

```text
∃ C, ∀ P Q, |h(P + Q) + h(P - Q) - 2 * (h(P) + h(Q))| ≤ C,
```

which is the height half of the descent proving the Mordell–Weil theorem. Together with the
Northcott property it gives finiteness of the sets of points of bounded naïve height.

The route is the one the source takes: the unordered pair `{P, Q}` is recorded by the symmetric
function `sym2x P Q` of the two `x`-coordinates, the map `{P, Q} ↦ {P + Q, P - Q}` is induced on
those symmetric functions by the quadratic `addSubMap`, and the height of a value of a
homogeneous polynomial map is controlled by the height of its argument. The commuting square
holds only up to a nonzero scalar, which is harmless because `logHeight` is scale-invariant.

Everything this runs on mentions no height and lives under `Affine/`: the commuting square in
`TauCeti.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap`; the duplication formulae, the
`x`-coordinate addition formulae and their transport to `Point.xRep` in
`TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Duplication`; and finiteness of the fibres
of `xRep`, which the Northcott instance consumes, in
`TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.XRep`.

## Main results

* `WeierstrassCurve.Affine.Point.naiveHeight` : the naïve height `logHeight P.xRep`.
* `WeierstrassCurve.Affine.approx_parallelogram_law` : the approximate parallelogram law.
* `WeierstrassCurve.Affine.finite_naiveHeight_le` : finiteness of points of bounded naïve height.

## Relation to Mathlib, and the duplication risk, weighed

The infrastructure this rests on is Mathlib's and is *consumed*, not restated: `Point.xRep`,
`addSubMap`, `addSubMapCoeff`, `isHomogeneous_addSubMap` and `sym2x`, the height API, and in
particular `abs_logHeight_addSubMap_sub_two_mul_logHeight_le`, the polynomial-map height bound the
parallelogram law consumes.

That last lemma lives in `Mathlib/NumberTheory/Height/EllipticCurve.lean`, a file by the same
author as this development's source, whose module docstring is titled "The naïve height and the
approximate parallelogram law" and whose `TODO` list names three items: define the naïve height,
add the further ingredients for the approximate parallelogram law, and add the law itself. The
source also brackets the duplication block with a reference to Mathlib PR `#40303`. So the
material here is work the upstream author has slotted but not landed: at the Mathlib version this
repository pins, all of these declarations are absent, which is why they are stated here rather
than imported.

This is a deliberate, temporary duplication with a defined end. If a later pin bump lands that
upstream work, the superseded declarations here must be deleted and their uses repointed at
Mathlib in the same pull request, per this repository's no-compatibility-shims rule.

## References

* [M. Stoll, *EllipticCurves*](https://github.com/MichaelStollBayreuth/EllipticCurves), commit
  `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, `EllipticCurves/MordellWeil.lean`, Apache-2.0.
-/

public section


public section

open Height MvPolynomial Nat

namespace WeierstrassCurve

namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ### The naïve height -/

section AAV

variable [AdmissibleAbsValues F]

/-- The naïve logarithmic height of an affine point on `W`. -/
noncomputable def Point.naiveHeight (P : W.Point) : ℝ :=
  logHeight P.xRep

/-- The defining equation. Deliberately **not** `@[simp]`: tagging it makes `naiveHeight`
disappear on sight, which puts `naiveHeight_zero` and `naiveHeight_neg` out of simp-normal form
and makes them redundant. See the `api-design` thread on the PR. -/
lemma Point.naiveHeight_eq_logHeight (P : W.Point) : P.naiveHeight = logHeight P.xRep := by
  simp [Point.naiveHeight]

/-- The naïve height as a *scalar* logarithmic height: it is `logHeight₁` of the zeroth
homogeneous coordinate `P.xRep 0`. This is the form the Northcott instance consumes, since
`Northcott` is stated for `logHeight₁`. -/
lemma Point.naiveHeight_eq_logHeight₁ {P : W.Point} :
    P.naiveHeight = logHeight₁ (P.xRep 0) := by
  match P with
  | 0 => simp [naiveHeight, xRep]
  | some .. => simpa [naiveHeight] using (logHeight₁_eq_logHeight _).symm

/-- The point at infinity has height zero: its representative is `![1, 0]`. -/
@[simp]
lemma Point.naiveHeight_zero : (0 : W.Point).naiveHeight = 0 := by
  simp [naiveHeight_eq_logHeight, Point.xRep_zero]

/-- Negation preserves the naïve height, since `P` and `-P` share an `x`-coordinate. -/
@[simp]
lemma Point.naiveHeight_neg (P : W.Point) : (-P).naiveHeight = P.naiveHeight := by
  simp [naiveHeight_eq_logHeight, Point.xRep_neg]

variable (W)

/-- The height of `sym2x P Q` differs from `h(P) + h(Q)` by a bounded amount. -/
lemma abs_logHeight_sym2x_sub_le :
    ∃ C, ∀ P Q : W.Point, |logHeight (P.sym2x Q) - (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight_sym2_sub_le F
  refine ⟨C, fun P Q ↦ ?_⟩
  rw [P.naiveHeight_eq_logHeight, Q.naiveHeight_eq_logHeight, Point.sym2x_eq_xRep]
  have H (v : Fin 2 → F) : ![v 0, v 1] = v := by ext i : 1; fin_cases i <;> simp
  have h₀ (P : W.Point) : ![P.xRep 0, P.xRep 1] ≠ 0 := H P.xRep ▸ P.xRep_ne_zero
  specialize hC (h₀ P) (h₀ Q)
  rw [H P.xRep, H Q.xRep] at *
  grind only [= abs.eq_1, = max_def]

variable [W.toAffine.IsElliptic]

/-- **The approximate parallelogram law** for the naïve height on an elliptic curve.

The ellipticity hypothesis is not decorative and cannot be dropped: the proof consumes Mathlib's
`abs_logHeight_addSubMap_sub_two_mul_logHeight_le`, which is stated under `[W.IsElliptic]` and
whose own proof uses the discriminant unit `W.Δ'⁻¹`, an object that exists only for an elliptic
curve. -/
theorem approx_parallelogram_law [DecidableEq F] :
    ∃ C, ∀ (P Q : W.Point),
      |(P + Q).naiveHeight + (P - Q).naiveHeight - 2 * (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := abs_logHeight_sym2x_sub_le W
  obtain ⟨C₂, hC₂⟩ := abs_logHeight_addSubMap_sub_two_mul_logHeight_le W
  refine ⟨3 * C₁ + C₂, fun P Q ↦ ?_⟩
  obtain ⟨t, ht₀, ht⟩ := Point.exists_smul_sym2x_add_sub_eq_addSubMap_sym2x P Q
  replace ht := congrArg logHeight ht
  rw [Height.logHeight_smul_eq_logHeight _ ht₀] at ht
  have hPQ := hC₁ P Q
  have haddsub := hC₁ (P + Q) (P - Q)
  have hC := ht ▸ hC₂ (P.sym2x Q)
  -- Reduce to the essentials before `grind`.
  generalize (P + Q).naiveHeight + (P - Q).naiveHeight = A at haddsub ⊢
  generalize logHeight ((P + Q).sym2x (P - Q)) = B at hC haddsub
  generalize logHeight (P.sym2x Q) = B' at hPQ hC
  generalize P.naiveHeight + Q.naiveHeight = A' at hPQ ⊢
  grind only [= abs.eq_1, = max_def]

end AAV

/-! ### Northcott finiteness -/

section Northcott

variable [AdmissibleAbsValues F]

instance [Northcott (logHeight₁ (K := F))] : Northcott (Point.naiveHeight (F := F) (W := W)) := by
  eta_expand
  simp only [Point.naiveHeight_eq_logHeight₁]
  rw [← Function.comp_def]
  have : Filter.TendstoCofinite fun P : W.Point ↦ P.xRep 0 :=
    (Filter.tendstoCofinite_iff_finite_preimage_singleton _).mpr finite_preimage_xRep0
  exact Northcott.comp_of_finite_fibers ..

variable [Northcott (logHeight₁ (K := F))]

variable (W) in
/-- The set of `K`-points on `W` with naïve height bounded by `B` is finite. This is the
Northcott ingredient of the Mordell–Weil theorem. -/
lemma finite_naiveHeight_le (B : ℝ) : {P : W.Point | P.naiveHeight ≤ B}.Finite :=
  Northcott.finite_le B

end Northcott

end Affine

end WeierstrassCurve

end
