/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Order
public import TauCeti.AlgebraicGeometry.WeilDivisor.FixedDegree.Basic

/-!
# Fixed-degree positive and negative parts of a Weil divisor

This file packages the positive and negative parts of a formal Weil divisor as fixed-degree
effective divisors.  The order file proves that every formal divisor decomposes as
`D = D⁺ - D⁻`, with both parts effective and with disjoint support.  The fixed-degree divisor
API, in turn, is the formal model for symmetric powers.  The declarations here bridge those two
layers by turning `D⁺` and `D⁻` into `EffectiveDivisorOfDegree` terms with their actual degrees
as indices.

This is formal divisor bookkeeping for the Jacobian challenge roadmap's Layer A and Layer C:
`TauCetiRoadmap/JacobianChallenge/README.md`, specifically "Divisors on a curve: Weil divisors
`⊕_x ℤ`", "Degree", and the symmetric-power prerequisite "Relative effective Cartier divisors
and symmetric powers `Symᵈ X`".  No external mathematics is vendored; the proofs reuse Tau
Ceti's `WeilDivisor.Order` positive/negative-part API and the existing
`EffectiveDivisorOfDegree` packaging.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace EffectiveDivisorOfDegree

variable {X : Type*} {d : ℕ}

noncomputable section

/-! ### Positive and negative parts -/

/-- The positive part of a Weil divisor, packaged as an effective divisor of its own degree. -/
abbrev posPart (D : WeilDivisor X) :
    EffectiveDivisorOfDegree X (degree D⁺).toNat :=
  ⟨D⁺, WeilDivisor.isEffective_posPart D,
    (Int.toNat_of_nonneg (WeilDivisor.isEffective_posPart D).degree_nonneg).symm⟩

/-- The negative part of a Weil divisor, packaged as an effective divisor of its own degree. -/
abbrev negPart (D : WeilDivisor X) :
    EffectiveDivisorOfDegree X (degree D⁻).toNat :=
  ⟨D⁻, WeilDivisor.isEffective_negPart D,
    (Int.toNat_of_nonneg (WeilDivisor.isEffective_negPart D).degree_nonneg).symm⟩

/-- The underlying Weil divisor of the packaged positive part is `D⁺`. -/
@[simp]
lemma coe_posPart (D : WeilDivisor X) : (posPart D : WeilDivisor X) = D⁺ :=
  rfl

/-- The underlying Weil divisor of the packaged negative part is `D⁻`. -/
@[simp]
lemma coe_negPart (D : WeilDivisor X) : (negPart D : WeilDivisor X) = D⁻ :=
  rfl

/-- If a divisor is already effective, its packaged positive part is the divisor itself, up to
the degree-index cast. -/
lemma posPart_coe_of_isEffective (D : EffectiveDivisorOfDegree X d) :
    posPart (D : WeilDivisor X) =
      EffectiveDivisorOfDegree.cast (by
        rw [WeilDivisor.posPart_eq_self_iff_isEffective.mpr D.isEffective, D.degree_eq]
        simp) D := by
  ext
  simp [WeilDivisor.posPart_eq_self_iff_isEffective.mpr D.isEffective]

/-- If a divisor is effective, its packaged negative part is the zero divisor. -/
lemma negPart_coe_of_isEffective (D : EffectiveDivisorOfDegree X d) :
    negPart (D : WeilDivisor X) =
      EffectiveDivisorOfDegree.cast (by
        rw [WeilDivisor.negPart_eq_zero_iff_isEffective.mpr D.isEffective]
        simp) (zero X) := by
  ext
  simp [WeilDivisor.negPart_eq_zero_iff_isEffective.mpr D.isEffective]

/-! ### Point differences -/

/-- For distinct points, the packaged positive part of `[x] - [y]` is `[x]`. -/
lemma posPart_pointDifference {x y : X} (h : x ≠ y) :
    posPart (WeilDivisor.pointDifference x y) =
      EffectiveDivisorOfDegree.cast (by
        rw [WeilDivisor.posPart_pointDifference h, WeilDivisor.degree_ofPoint]
        simp) (ofSym (Sym.oneEquiv x)) := by
  ext z
  simp only [coe_cast, WeilDivisor.posPart_pointDifference h, coeff_ofSym]
  rcases eq_or_ne z x with rfl | hzx
  · simp
  · simp [hzx]

/-- For distinct points, the packaged negative part of `[x] - [y]` is `[y]`. -/
lemma negPart_pointDifference {x y : X} (h : x ≠ y) :
    negPart (WeilDivisor.pointDifference x y) =
      EffectiveDivisorOfDegree.cast (by
        rw [WeilDivisor.negPart_pointDifference h, WeilDivisor.degree_ofPoint]
        simp) (ofSym (Sym.oneEquiv y)) := by
  ext z
  simp only [coe_cast, WeilDivisor.negPart_pointDifference h, coeff_ofSym]
  rcases eq_or_ne z y with rfl | hzy
  · simp
  · simp [hzy]

end

end EffectiveDivisorOfDegree

end WeilDivisor

end AlgebraicGeometry

end TauCeti
