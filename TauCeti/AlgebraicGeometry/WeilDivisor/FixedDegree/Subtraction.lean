/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Degree.Order
public import TauCeti.AlgebraicGeometry.WeilDivisor.FixedDegree.Addition

/-!
# Subtraction of fixed-degree effective Weil divisors

This file records the residual effective divisor obtained by subtracting an effective
sub-divisor from a fixed-degree effective Weil divisor. If `E ≤ D`, with `D` of degree `e`
and `E` of degree `d`, then `D - E` is effective of degree `e - d`. The cancellation lemmas
show that adding the residual back recovers the original divisor, up to the unavoidable casts
in the natural-number degree index.

This is formal divisor bookkeeping for the Jacobian challenge roadmap's Layer C symmetric-power
lane (`TauCetiRoadmap/JacobianChallenge/README.md`, "Relative effective Cartier divisors and
symmetric powers `Symᵈ X`"). The scheme-level construction is later geometry; this file supplies
the elementary residual-divisor API used when separating a fixed effective base divisor from an
unordered collection of points. No external mathematics is vendored.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace EffectiveDivisorOfDegree

variable {X : Type*} {d e : ℕ}

noncomputable section

/-- The residual fixed-degree effective divisor `D - E`, defined when `E ≤ D`.

If `D` has degree `e` and `E` has degree `d`, the residual has degree `e - d`. -/
@[expose]
def subOfLe (D : EffectiveDivisorOfDegree X e) (E : EffectiveDivisorOfDegree X d)
    (hED : (E : WeilDivisor X) ≤ D) : EffectiveDivisorOfDegree X (e - d) :=
  ⟨(D : WeilDivisor X) - E, le_iff_isEffective_sub.mp hED, by
    have hde : d ≤ e := EffectiveDivisorOfDegree.degree_le_of_le hED
    rw [degree_sub, D.degree_eq, E.degree_eq]
    exact (Int.ofNat_sub hde).symm⟩

/-- The underlying Weil divisor of a residual fixed-degree divisor is the difference of the
underlying Weil divisors. -/
@[simp]
lemma coe_subOfLe (D : EffectiveDivisorOfDegree X e) (E : EffectiveDivisorOfDegree X d)
    (hED : (E : WeilDivisor X) ≤ D) : (subOfLe D E hED : WeilDivisor X) = (D : WeilDivisor X) - E :=
  rfl

/-- The coefficient of a residual fixed-degree divisor is the difference of coefficients. -/
@[simp]
lemma coeff_subOfLe (D : EffectiveDivisorOfDegree X e) (E : EffectiveDivisorOfDegree X d)
    (hED : (E : WeilDivisor X) ≤ D) (x : X) :
    coeff (subOfLe D E hED : WeilDivisor X) x =
      coeff (D : WeilDivisor X) x - coeff (E : WeilDivisor X) x := by
  rw [coe_subOfLe, WeilDivisor.coeff_sub]

/-- The multiplicity function of a residual divisor is the truncated difference of the
multiplicity functions. -/
@[simp]
lemma multiplicityFinsupp_subOfLe (D : EffectiveDivisorOfDegree X e)
    (E : EffectiveDivisorOfDegree X d) (hED : (E : WeilDivisor X) ≤ D) :
    (subOfLe D E hED).multiplicityFinsupp =
      D.multiplicityFinsupp - E.multiplicityFinsupp := by
  ext x
  rw [multiplicityFinsupp_apply, coe_subOfLe, WeilDivisor.coeff_sub, Finsupp.tsub_apply,
    multiplicityFinsupp_apply, multiplicityFinsupp_apply]
  have hcoeff : coeff (E : WeilDivisor X) x ≤ coeff (D : WeilDivisor X) x :=
    WeilDivisor.coeff_le_coeff hED x
  have hnat : (coeff (E : WeilDivisor X) x).toNat ≤ (coeff (D : WeilDivisor X) x).toNat :=
    Int.toNat_le_toNat hcoeff
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_sub_of_le hcoeff, Nat.cast_sub hnat]
  rw [Int.toNat_of_nonneg ((isEffective_iff (D : WeilDivisor X)).mp D.isEffective x),
    Int.toNat_of_nonneg ((isEffective_iff (E : WeilDivisor X)).mp E.isEffective x)]

/-- The finitely supported multiplicity representation of a residual divisor is the
truncated difference of the representations of the original divisors. -/
lemma equivFinsupp_subOfLe_coe (D : EffectiveDivisorOfDegree X e)
    (E : EffectiveDivisorOfDegree X d) (hED : (E : WeilDivisor X) ≤ D) :
    (equivFinsupp (subOfLe D E hED) : X →₀ ℕ) =
      (equivFinsupp D : X →₀ ℕ) - (equivFinsupp E : X →₀ ℕ) := by
  simp

/-- Under the symmetric-power equivalence, a residual divisor is represented by the truncated
difference of multiplicity functions. -/
@[simp]
lemma equivSym_subOfLe (D : EffectiveDivisorOfDegree X e) (E : EffectiveDivisorOfDegree X d)
    (hED : (E : WeilDivisor X) ≤ D) :
    equivSym (subOfLe D E hED) =
      (letI := Classical.decEq X;
        (Sym.equivNatSum X (e - d)).symm
          ⟨D.multiplicityFinsupp - E.multiplicityFinsupp, by
            rw [← multiplicityFinsupp_subOfLe D E hED]
            exact (subOfLe D E hED).sum_multiplicityFinsupp⟩) := by
  classical
  rw [equivSym_apply]
  congr 1
  ext x
  simp

/-- The degree of the residual divisor is the difference of the degree indices. -/
lemma degree_subOfLe (D : EffectiveDivisorOfDegree X e) (E : EffectiveDivisorOfDegree X d)
    (hED : (E : WeilDivisor X) ≤ D) :
    degree (subOfLe D E hED : WeilDivisor X) = ((e - d : ℕ) : ℤ) :=
  (subOfLe D E hED).degree_eq

/-- Adding a sub-divisor back to its residual recovers the original divisor, up to the cast
identifying `d + (e - d)` with `e`. -/
@[simp]
lemma add_subOfLe (D : EffectiveDivisorOfDegree X e) (E : EffectiveDivisorOfDegree X d)
    (hED : (E : WeilDivisor X) ≤ D) :
    add E (subOfLe D E hED) =
      EffectiveDivisorOfDegree.cast
        (Nat.add_sub_of_le (EffectiveDivisorOfDegree.degree_le_of_le hED)).symm D := by
  ext
  simp

/-- Adding the residual on the left also recovers the original divisor, up to the cast
identifying `(e - d) + d` with `e`. -/
@[simp]
lemma subOfLe_add (D : EffectiveDivisorOfDegree X e) (E : EffectiveDivisorOfDegree X d)
    (hED : (E : WeilDivisor X) ≤ D) :
    add (subOfLe D E hED) E =
      EffectiveDivisorOfDegree.cast
        (Nat.sub_add_cancel (EffectiveDivisorOfDegree.degree_le_of_le hED)).symm D := by
  ext
  simp [sub_add_cancel]

/-- Subtracting the zero fixed-degree divisor leaves the original divisor, up to the cast
identifying `d - 0` with `d`. -/
@[simp]
lemma subOfLe_zero (D : EffectiveDivisorOfDegree X d) :
    subOfLe D (zero X) (by
      rw [← WeilDivisor.isEffective_iff_zero_le]
      exact D.isEffective) =
      EffectiveDivisorOfDegree.cast (Nat.sub_zero d).symm D := by
  ext
  simp

/-- Subtracting a fixed-degree divisor from itself gives the zero residual divisor. -/
@[simp]
lemma subOfLe_self (D : EffectiveDivisorOfDegree X d) :
    subOfLe D D le_rfl = EffectiveDivisorOfDegree.cast (Nat.sub_self d).symm (zero X) := by
  ext
  simp

end

end EffectiveDivisorOfDegree

end WeilDivisor

end AlgebraicGeometry

end TauCeti
