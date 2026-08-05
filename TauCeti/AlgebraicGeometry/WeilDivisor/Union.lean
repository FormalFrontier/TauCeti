/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Common

/-!
# The union of two fixed-degree effective Weil divisors

This file packages the pointwise maximum of two effective fixed-degree Weil divisors as their
union.  If `D` and `E` are effective divisors, `D ⊔ E` is the smallest divisor lying above both;
its coefficient at a point is the larger of the two multiplicities.  This complements the common
part `D ⊓ E` from `TauCeti.AlgebraicGeometry.WeilDivisor.Common`: the two are linked by the
lattice-ordered-group inclusion–exclusion identity `(D ⊓ E) + (D ⊔ E) = D + E`, which at the
level of degrees reads `deg (D ⊓ E) + deg (D ⊔ E) = deg D + deg E`.

This is formal divisor bookkeeping for the Jacobian challenge roadmap's Layer C symmetric-power
lane (`TauCetiRoadmap/JacobianChallenge/README.md`, "Relative effective Cartier divisors and
symmetric powers `Symᵈ X`").  The Abel-map and linear-system arguments merge unordered effective
divisors; where the common part `D ⊓ E` isolates the shared points, the union `D ⊔ E` records the
combined support with the larger multiplicities, and the inclusion–exclusion identity converts
between the two.  This file supplies that operation at the existing formal Weil-divisor level,
before scheme-level symmetric powers or relative Cartier divisors are available.

This reuses Mathlib's lattice-ordered commutative group identity `inf_add_sup`
(`Mathlib.Algebra.Order.Group.Lattice`); no external mathematics is vendored.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X : Type*}

namespace EffectiveDivisorOfDegree

variable {d e : ℕ}

noncomputable section

private lemma exists_sup (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    ∃ F : EffectiveDivisorOfDegree X (degree ((D : WeilDivisor X) ⊔ E)).toNat,
      (F : WeilDivisor X) = (D : WeilDivisor X) ⊔ E :=
  ⟨⟨(D : WeilDivisor X) ⊔ E, D.isEffective.sup,
    (Int.toNat_of_nonneg D.isEffective.sup.degree_nonneg).symm⟩, rfl⟩

/-- The union of two fixed-degree effective divisors.

Its underlying Weil divisor is the pointwise maximum `D ⊔ E`; its degree index is the actual
degree of that maximum. -/
def sup (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    EffectiveDivisorOfDegree X (degree ((D : WeilDivisor X) ⊔ E)).toNat :=
  Classical.choose (exists_sup D E)

@[simp]
lemma coe_sup (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    (sup D E : WeilDivisor X) = (D : WeilDivisor X) ⊔ E :=
  Classical.choose_spec (exists_sup D E)

/-- The coefficient of the union is the maximum of the two coefficients. -/
lemma coeff_sup (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) (x : X) :
    coeff (sup D E : WeilDivisor X) x =
      coeff (D : WeilDivisor X) x ⊔ coeff (E : WeilDivisor X) x := by
  rw [coe_sup, WeilDivisor.coeff_sup]

/-- The multiplicity function of the union is the pointwise maximum of multiplicities. -/
@[simp]
lemma multiplicityFinsupp_sup (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) :
    (sup D E).multiplicityFinsupp = D.multiplicityFinsupp ⊔ E.multiplicityFinsupp := by
  ext x
  rw [multiplicityFinsupp_apply, coeff_sup, Finsupp.sup_apply, multiplicityFinsupp_apply,
    multiplicityFinsupp_apply]
  have hD := (isEffective_iff (D : WeilDivisor X)).mp D.isEffective x
  have hE := (isEffective_iff (E : WeilDivisor X)).mp E.isEffective x
  omega

/-- The symmetric-power representative of the union is the pointwise maximum of multiplicity
functions. -/
@[simp]
lemma equivSym_sup (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    equivSym (sup D E) =
      (letI := Classical.decEq X;
        (Sym.equivNatSum X (degree ((D : WeilDivisor X) ⊔ E)).toNat).symm
          ⟨D.multiplicityFinsupp ⊔ E.multiplicityFinsupp, by
            rw [← multiplicityFinsupp_sup D E]
            exact (sup D E).sum_multiplicityFinsupp⟩) := by
  classical
  rw [equivSym_apply]
  congr 1
  ext x
  simp

/-- The left input divisor lies below the union. -/
lemma le_sup_left (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    (D : WeilDivisor X) ≤ sup D E := by
  rw [coe_sup]
  exact _root_.le_sup_left

/-- The right input divisor lies below the union. -/
lemma le_sup_right (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    (E : WeilDivisor X) ≤ sup D E := by
  rw [coe_sup]
  exact _root_.le_sup_right

/-- Any Weil divisor above both inputs lies above their union. -/
lemma sup_le {F : WeilDivisor X} {D : EffectiveDivisorOfDegree X d}
    {E : EffectiveDivisorOfDegree X e} (hDF : (D : WeilDivisor X) ≤ F)
    (hEF : (E : WeilDivisor X) ≤ F) : (sup D E : WeilDivisor X) ≤ F := by
  rw [coe_sup]
  exact _root_.sup_le hDF hEF

/-- The union is the left input exactly when the right input is below the left input. -/
lemma sup_eq_left {D : EffectiveDivisorOfDegree X d} {E : EffectiveDivisorOfDegree X e} :
    (sup D E : WeilDivisor X) = D ↔ (E : WeilDivisor X) ≤ D := by
  rw [coe_sup]
  exact _root_.sup_eq_left

/-- The union is the right input exactly when the left input is below the right input. -/
lemma sup_eq_right {D : EffectiveDivisorOfDegree X d} {E : EffectiveDivisorOfDegree X e} :
    (sup D E : WeilDivisor X) = E ↔ (D : WeilDivisor X) ≤ E := by
  rw [coe_sup]
  exact _root_.sup_eq_right

/-- The union is symmetric in its inputs, up to the natural degree-index cast. -/
lemma sup_comm (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    sup D E =
      EffectiveDivisorOfDegree.cast (by rw [_root_.sup_comm]) (sup E D) := by
  apply Subtype.ext
  rw [coe_sup, coe_cast, coe_sup, _root_.sup_comm]

/-- The left degree index is bounded above by the degree of the union. -/
lemma left_le_degree_sup (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    d ≤ (degree ((D : WeilDivisor X) ⊔ E)).toNat :=
  EffectiveDivisorOfDegree.degree_le_of_le (le_sup_left D E)

/-- The right degree index is bounded above by the degree of the union. -/
lemma right_le_degree_sup (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    e ≤ (degree ((D : WeilDivisor X) ⊔ E)).toNat :=
  EffectiveDivisorOfDegree.degree_le_of_le (le_sup_right D E)

/-- Inclusion–exclusion on the degree indices: the degrees of the common part and the union
sum to `d + e`. -/
lemma degree_inf_toNat_add_degree_sup_toNat (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) :
    (degree ((D : WeilDivisor X) ⊓ E)).toNat + (degree ((D : WeilDivisor X) ⊔ E)).toNat =
      d + e := by
  have hinf : 0 ≤ degree ((D : WeilDivisor X) ⊓ E) :=
    (D.isEffective.inf E.isEffective).degree_nonneg
  have hsup : 0 ≤ degree ((D : WeilDivisor X) ⊔ E) := D.isEffective.sup.degree_nonneg
  have hkey : degree ((D : WeilDivisor X) ⊓ E) + degree ((D : WeilDivisor X) ⊔ E) =
      (d : ℤ) + e := by
    rw [WeilDivisor.degree_inf_add_degree_sup, D.degree_eq, E.degree_eq]
  omega

/-- The degree of the union is `d + e` minus the degree of the common part. -/
lemma degree_sup_toNat (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    (degree ((D : WeilDivisor X) ⊔ E)).toNat =
      d + e - (degree ((D : WeilDivisor X) ⊓ E)).toNat := by
  have := degree_inf_toNat_add_degree_sup_toNat D E
  omega

/-- Inclusion–exclusion for fixed-degree effective divisors: the common part plus the union
recover the sum of the two divisors, up to the natural degree-index cast. -/
lemma inf_add_sup (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    add (inf D E) (sup D E) =
      EffectiveDivisorOfDegree.cast
        (degree_inf_toNat_add_degree_sup_toNat D E).symm (add D E) := by
  apply Subtype.ext
  rw [coe_add, coe_cast, coe_add, coe_inf, coe_sup, _root_.inf_add_sup]

/-- The union plus the common part also recover the sum of the two divisors, up to the natural
degree-index cast. -/
lemma sup_add_inf (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    add (sup D E) (inf D E) =
      EffectiveDivisorOfDegree.cast
        (by have := degree_inf_toNat_add_degree_sup_toNat D E; omega)
        (add D E) := by
  apply Subtype.ext
  rw [coe_add, coe_cast, coe_add, coe_inf, coe_sup,
    _root_.add_comm ((D : WeilDivisor X) ⊔ E), _root_.inf_add_sup]

end

end EffectiveDivisorOfDegree

end WeilDivisor

end AlgebraicGeometry

end TauCeti
