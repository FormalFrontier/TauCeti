/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.FixedDegree.Subtraction

/-!
# Common parts of fixed-degree effective Weil divisors

This file packages the pointwise minimum of two effective fixed-degree Weil divisors as their
common effective part.  If `D` and `E` are effective divisors, `D ⊓ E` is the largest divisor
lying below both.  Removing it from `D` and from `E` gives two residual effective divisors with
disjoint support.

This is formal divisor bookkeeping for the Jacobian challenge roadmap's Layer C symmetric-power
lane (`TauCetiRoadmap/JacobianChallenge/README.md`, "Relative effective Cartier divisors and
symmetric powers `Symᵈ X`").  The later Abel-map and linear-system arguments need to split
unordered effective divisors into their common sub-divisor and the two remaining parts; this file
supplies that operation at the existing formal Weil-divisor level, before scheme-level symmetric
powers or relative Cartier divisors are available.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X : Type*}

namespace EffectiveDivisorOfDegree

variable {d e : ℕ}

noncomputable section

private lemma exists_inf (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    ∃ F : EffectiveDivisorOfDegree X (degree ((D : WeilDivisor X) ⊓ E)).toNat,
      (F : WeilDivisor X) = (D : WeilDivisor X) ⊓ E :=
  ⟨⟨(D : WeilDivisor X) ⊓ E, D.isEffective.inf E.isEffective,
    (Int.toNat_of_nonneg (D.isEffective.inf E.isEffective).degree_nonneg).symm⟩, rfl⟩

/-- The common effective part of two fixed-degree effective divisors.

Its underlying Weil divisor is the pointwise minimum `D ⊓ E`; its degree index is the actual
degree of that minimum. -/
def inf (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    EffectiveDivisorOfDegree X (degree ((D : WeilDivisor X) ⊓ E)).toNat :=
  Classical.choose (exists_inf D E)

@[simp]
lemma coe_inf (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    (inf D E : WeilDivisor X) = (D : WeilDivisor X) ⊓ E :=
  Classical.choose_spec (exists_inf D E)

/-- The coefficient of the common part is the minimum of the two coefficients. -/
lemma coeff_inf (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) (x : X) :
    coeff (inf D E : WeilDivisor X) x =
      coeff (D : WeilDivisor X) x ⊓ coeff (E : WeilDivisor X) x := by
  rw [coe_inf, WeilDivisor.coeff_inf]

/-- The multiplicity function of the common part is the pointwise minimum of multiplicities. -/
@[simp]
lemma multiplicityFinsupp_inf (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) :
    (inf D E).multiplicityFinsupp = D.multiplicityFinsupp ⊓ E.multiplicityFinsupp := by
  ext x
  rw [multiplicityFinsupp_apply, coeff_inf, Finsupp.inf_apply, multiplicityFinsupp_apply,
    multiplicityFinsupp_apply]
  have hD := (isEffective_iff (D : WeilDivisor X)).mp D.isEffective x
  have hE := (isEffective_iff (E : WeilDivisor X)).mp E.isEffective x
  omega

/-- The symmetric-power representative of the common part is the pointwise minimum of
multiplicity functions. -/
@[simp]
lemma equivSym_inf (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    equivSym (inf D E) =
      (letI := Classical.decEq X;
        (Sym.equivNatSum X (degree ((D : WeilDivisor X) ⊓ E)).toNat).symm
          ⟨D.multiplicityFinsupp ⊓ E.multiplicityFinsupp, by
            rw [← multiplicityFinsupp_inf D E]
            exact (inf D E).sum_multiplicityFinsupp⟩) := by
  classical
  rw [equivSym_apply]
  congr 1
  ext x
  simp

/-- The common part lies below the left input divisor. -/
lemma inf_le_left (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    (inf D E : WeilDivisor X) ≤ D := by
  rw [coe_inf]
  exact _root_.inf_le_left

/-- The common part lies below the right input divisor. -/
lemma inf_le_right (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    (inf D E : WeilDivisor X) ≤ E := by
  rw [coe_inf]
  exact _root_.inf_le_right

/-- Any Weil divisor below both inputs lies below their common part. -/
lemma le_inf {F : WeilDivisor X} {D : EffectiveDivisorOfDegree X d}
    {E : EffectiveDivisorOfDegree X e} (hFD : F ≤ D) (hFE : F ≤ E) :
    F ≤ inf D E := by
  rw [coe_inf]
  exact _root_.le_inf hFD hFE

/-- The common part is the left input exactly when the left input is below the right input. -/
lemma inf_eq_left {D : EffectiveDivisorOfDegree X d} {E : EffectiveDivisorOfDegree X e} :
    (inf D E : WeilDivisor X) = D ↔ (D : WeilDivisor X) ≤ E := by
  rw [coe_inf]
  exact _root_.inf_eq_left

/-- The common part is the right input exactly when the right input is below the left input. -/
lemma inf_eq_right {D : EffectiveDivisorOfDegree X d} {E : EffectiveDivisorOfDegree X e} :
    (inf D E : WeilDivisor X) = E ↔ (E : WeilDivisor X) ≤ D := by
  rw [coe_inf]
  exact _root_.inf_eq_right

/-- The degree of the common part is bounded by the left degree index. -/
lemma degree_inf_le_left (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    (degree ((D : WeilDivisor X) ⊓ E)).toNat ≤ d :=
  by
    simpa [coe_inf] using degree_le_of_le (inf_le_left D E)

/-- The degree of the common part is bounded by the right degree index. -/
lemma degree_inf_le_right (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    (degree ((D : WeilDivisor X) ⊓ E)).toNat ≤ e :=
  by
    simpa [coe_inf] using degree_le_of_le (inf_le_right D E)

/-- The residual part of the left divisor after removing the common part.

It is the fixed-degree difference `D - (D ⊓ E)`, available since the common part lies below `D`. -/
def leftResidual (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    EffectiveDivisorOfDegree X (d - (degree ((D : WeilDivisor X) ⊓ E)).toNat) :=
  subOfLe D (inf D E) (inf_le_left D E)

/-- The residual part of the right divisor after removing the common part.

It is the fixed-degree difference `E - (D ⊓ E)`, available since the common part lies below `E`. -/
def rightResidual (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    EffectiveDivisorOfDegree X (e - (degree ((D : WeilDivisor X) ⊓ E)).toNat) :=
  subOfLe E (inf D E) (inf_le_right D E)

@[simp]
lemma coe_leftResidual (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    (leftResidual D E : WeilDivisor X) = (D : WeilDivisor X) - inf D E :=
  coe_subOfLe D (inf D E) (inf_le_left D E)

@[simp]
lemma coe_rightResidual (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    (rightResidual D E : WeilDivisor X) = (E : WeilDivisor X) - inf D E :=
  coe_subOfLe E (inf D E) (inf_le_right D E)

/-- The coefficient of the left residual is `coeff D x - min (coeff D x) (coeff E x)`. -/
lemma coeff_leftResidual (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) (x : X) :
    coeff (leftResidual D E : WeilDivisor X) x =
      coeff (D : WeilDivisor X) x -
        (coeff (D : WeilDivisor X) x ⊓ coeff (E : WeilDivisor X) x) := by
  rw [coe_leftResidual, WeilDivisor.coeff_sub, coeff_inf]

/-- The coefficient of the right residual is `coeff E x - min (coeff D x) (coeff E x)`. -/
lemma coeff_rightResidual (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) (x : X) :
    coeff (rightResidual D E : WeilDivisor X) x =
      coeff (E : WeilDivisor X) x -
        (coeff (D : WeilDivisor X) x ⊓ coeff (E : WeilDivisor X) x) := by
  rw [coe_rightResidual, WeilDivisor.coeff_sub, coeff_inf]

/-- The multiplicity function of the left residual is the truncated multiplicity difference. -/
@[simp]
lemma multiplicityFinsupp_leftResidual (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) : (leftResidual D E).multiplicityFinsupp =
      D.multiplicityFinsupp - (inf D E).multiplicityFinsupp :=
  multiplicityFinsupp_subOfLe D (inf D E) (inf_le_left D E)

/-- The multiplicity function of the right residual is the truncated multiplicity difference. -/
@[simp]
lemma multiplicityFinsupp_rightResidual (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) : (rightResidual D E).multiplicityFinsupp =
      E.multiplicityFinsupp - (inf D E).multiplicityFinsupp :=
  multiplicityFinsupp_subOfLe E (inf D E) (inf_le_right D E)

/-- The symmetric-power representative of the left residual is the truncated multiplicity
difference from the left divisor. -/
@[simp]
lemma equivSym_leftResidual (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    equivSym (leftResidual D E) =
      (letI := Classical.decEq X;
        (Sym.equivNatSum X (d - (degree ((D : WeilDivisor X) ⊓ E)).toNat)).symm
          ⟨D.multiplicityFinsupp - (inf D E).multiplicityFinsupp, by
            rw [← multiplicityFinsupp_leftResidual D E]
            exact (leftResidual D E).sum_multiplicityFinsupp⟩) :=
  equivSym_subOfLe D (inf D E) (inf_le_left D E)

/-- The symmetric-power representative of the right residual is the truncated multiplicity
difference from the right divisor. -/
@[simp]
lemma equivSym_rightResidual (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    equivSym (rightResidual D E) =
      (letI := Classical.decEq X;
        (Sym.equivNatSum X (e - (degree ((D : WeilDivisor X) ⊓ E)).toNat)).symm
          ⟨E.multiplicityFinsupp - (inf D E).multiplicityFinsupp, by
            rw [← multiplicityFinsupp_rightResidual D E]
            exact (rightResidual D E).sum_multiplicityFinsupp⟩) :=
  equivSym_subOfLe E (inf D E) (inf_le_right D E)

/-- The two residual divisors left after removing the common part are coefficientwise
disjoint. -/
lemma leftResidual_inf_rightResidual_eq_zero (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) :
    ((leftResidual D E : WeilDivisor X) ⊓ rightResidual D E) = 0 := by
  rw [coe_leftResidual, coe_rightResidual, coe_inf]
  exact sub_inf_inf_sub_inf_eq_zero (D : WeilDivisor X) E

/-- Removing the common part from the left divisor and adding it back recovers the left
divisor, up to the natural degree-index cast. -/
@[simp]
lemma leftResidual_add_inf (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    add (leftResidual D E) (inf D E) =
      EffectiveDivisorOfDegree.cast
        (Nat.sub_add_cancel (degree_inf_le_left D E)).symm D :=
  subOfLe_add D (inf D E) (inf_le_left D E)

/-- Adding the common part before the left residual also recovers the left divisor, up to the
natural degree-index cast. -/
@[simp]
lemma inf_add_leftResidual (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    add (inf D E) (leftResidual D E) =
      EffectiveDivisorOfDegree.cast
        (Nat.add_sub_of_le (degree_inf_le_left D E)).symm D :=
  add_subOfLe D (inf D E) (inf_le_left D E)

/-- Removing the common part from the right divisor and adding it back recovers the right
divisor, up to the natural degree-index cast. -/
@[simp]
lemma rightResidual_add_inf (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    add (rightResidual D E) (inf D E) =
      EffectiveDivisorOfDegree.cast
        (Nat.sub_add_cancel (degree_inf_le_right D E)).symm E :=
  subOfLe_add E (inf D E) (inf_le_right D E)

/-- Adding the common part before the right residual also recovers the right divisor, up to the
natural degree-index cast. -/
@[simp]
lemma inf_add_rightResidual (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    add (inf D E) (rightResidual D E) =
      EffectiveDivisorOfDegree.cast
        (Nat.add_sub_of_le (degree_inf_le_right D E)).symm E :=
  add_subOfLe E (inf D E) (inf_le_right D E)

end

end EffectiveDivisorOfDegree

end WeilDivisor

end AlgebraicGeometry

end TauCeti
