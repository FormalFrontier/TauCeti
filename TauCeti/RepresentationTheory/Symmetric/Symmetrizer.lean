/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Perm.Sign
public import TauCeti.RepresentationTheory.Symmetric.RowColumnSubgroup

/-!
# Young symmetrizers

For a Young tableau `t`, this file defines the row symmetrizer `a_t`, the column
antisymmetrizer `b_t`, and the Young symmetrizer `c_t = a_t b_t` in the rational group
algebra of the symmetric group on the entries of `t`.

The defining coefficient formulas are accompanied by the translation laws that characterize
the two factors: the row group fixes `a_t`, while the column group acts on `b_t` through the
sign character.  In particular, each factor squares to its subgroup order times itself.
These are the elementary inputs to the essential-idempotence theorem for `c_t` and the
construction of Specht modules.

The symmetrizers are built over `ℚ`, which is what the essential-idempotence theorem and the
Specht-module constructions downstream of this file work over.  The coefficients of `c_t` are in
fact integral -- each is a sum of signs -- so nothing about `c_t` itself demands rational
coefficients; it is *this* definition, over `ℚ`, whose coefficients are transported when `c_t` is
made to act on a module over another ring, which is `youngSymmetrizerOver`.  That transport goes
along `algebraMap ℚ k`, so it asks the target ring to be a `ℚ`-algebra.  The restriction is one
of the present implementation, not of the mathematics: an integral `c_t`, over `ℤ` or over an
arbitrary commutative ring, would remove it, and is a separate construction.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 2.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 2.
-/

public section

namespace TauCeti

open scoped BigOperators

namespace YoungTableau

variable {μ : YoungDiagram}

noncomputable section

/-- Classical decidability of membership in the row group, used to form its finite sum. -/
local instance (t : YoungTableau μ) : DecidablePred (· ∈ rowSubgroup t) :=
  Classical.decPred _

/-- Classical decidability of membership in the column group, used to form its finite sum. -/
local instance (t : YoungTableau μ) : DecidablePred (· ∈ colSubgroup t) :=
  Classical.decPred _

@[simp]
private theorem permSign_cast_mul_self (σ : Equiv.Perm (Fin μ.card)) :
    ((Equiv.Perm.sign σ : ℤ) : ℚ) * ((Equiv.Perm.sign σ : ℤ) : ℚ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

/-- The **row symmetrizer** `a_t`, the sum of the permutations preserving the rows of `t`. -/
noncomputable def rowSymmetrizer (t : YoungTableau μ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)) :=
  ∑ p : rowSubgroup t, MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card)) p

/-- The **column antisymmetrizer** `b_t`, the signed sum of the permutations preserving the
columns of `t`. -/
noncomputable def columnAntisymmetrizer (t : YoungTableau μ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)) :=
  ∑ q : colSubgroup t,
    ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
      MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card)) q

/-- The **Young symmetrizer** of `t`, with the convention `c_t = a_t b_t`: first
row-symmetrize, then column-antisymmetrize. -/
noncomputable def youngSymmetrizer (t : YoungTableau μ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)) :=
  rowSymmetrizer t * columnAntisymmetrizer t

/-- The row symmetrizer is the sum of the basis elements indexed by the row group. -/
theorem rowSymmetrizer_def (t : YoungTableau μ) :
    rowSymmetrizer t =
      ∑ p : rowSubgroup t, MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card)) p :=
  (rfl)

/-- The column antisymmetrizer is the sign-weighted sum of the basis elements indexed by the
column group. -/
theorem columnAntisymmetrizer_def (t : YoungTableau μ) :
    columnAntisymmetrizer t =
      ∑ q : colSubgroup t,
        ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
          MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card)) q :=
  (rfl)

/-- The Young symmetrizer uses the row-then-column convention `c_t = a_t b_t`. -/
theorem youngSymmetrizer_def (t : YoungTableau μ) :
    youngSymmetrizer t = rowSymmetrizer t * columnAntisymmetrizer t :=
  (rfl)

/-- The coefficient of a permutation in the row symmetrizer is its row-group indicator. -/
@[simp]
theorem rowSymmetrizer_coeff (t : YoungTableau μ) (σ : Equiv.Perm (Fin μ.card)) :
    (rowSymmetrizer t).coeff σ = if σ ∈ rowSubgroup t then 1 else 0 := by
  classical
  rw [rowSymmetrizer_def, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hσ : σ ∈ rowSubgroup t
  · rw [if_pos hσ,
      Finset.sum_eq_single (⟨σ, hσ⟩ : rowSubgroup t)]
    · simp
    · exact fun p _ hp => if_neg fun h => hp (Subtype.ext h)
    · simp
  · rw [if_neg hσ]
    exact Finset.sum_eq_zero fun p _ =>
      if_neg fun h : (p : Equiv.Perm (Fin μ.card)) = σ => hσ (h ▸ p.property)

/-- The coefficient of a permutation in the column antisymmetrizer is its sign on the column
group and zero off that group. -/
@[simp]
theorem columnAntisymmetrizer_coeff (t : YoungTableau μ) (σ : Equiv.Perm (Fin μ.card)) :
    (columnAntisymmetrizer t).coeff σ =
      if σ ∈ colSubgroup t then ((Equiv.Perm.sign σ : ℤ) : ℚ) else 0 := by
  classical
  rw [columnAntisymmetrizer_def, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.of_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul]
  by_cases hσ : σ ∈ colSubgroup t
  · rw [if_pos hσ,
      Finset.sum_eq_single (⟨σ, hσ⟩ : colSubgroup t)]
    · simp
    · exact fun q _ hq => by
        rw [if_neg fun h => hq (Subtype.ext h), mul_zero]
    · simp
  · rw [if_neg hσ]
    exact Finset.sum_eq_zero fun q _ => by
      rw [if_neg fun h : (q : Equiv.Perm (Fin μ.card)) = σ => hσ (h ▸ q.property),
        mul_zero]

/-- Left multiplication by a member of the row group fixes the row symmetrizer. -/
@[simp]
theorem mul_rowSymmetrizer_left (t : YoungTableau μ) (p : rowSubgroup t) :
    MonoidAlgebra.single (p : Equiv.Perm (Fin μ.card)) 1 * rowSymmetrizer t =
      rowSymmetrizer t := by
  rw [← MonoidAlgebra.of_apply, rowSymmetrizer_def, Finset.mul_sum]
  simp_rw [← (MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card))).map_mul]
  apply Fintype.sum_equiv (Equiv.mulLeft p)
  intro q
  rfl

/-- Right multiplication by a member of the row group fixes the row symmetrizer. -/
@[simp]
theorem mul_rowSymmetrizer_right (t : YoungTableau μ) (p : rowSubgroup t) :
    rowSymmetrizer t * MonoidAlgebra.single (p : Equiv.Perm (Fin μ.card)) 1 =
      rowSymmetrizer t := by
  rw [← MonoidAlgebra.of_apply, rowSymmetrizer_def, Finset.sum_mul]
  simp_rw [← (MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card))).map_mul]
  apply Fintype.sum_equiv (Equiv.mulRight p)
  intro q
  rfl

/-- Left multiplication by a member of the column group scales the column antisymmetrizer by
the sign of that member. -/
@[simp]
theorem mul_columnAntisymmetrizer_left (t : YoungTableau μ) (q : colSubgroup t) :
    MonoidAlgebra.single (q : Equiv.Perm (Fin μ.card)) 1 * columnAntisymmetrizer t =
      ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
        columnAntisymmetrizer t := by
  rw [← MonoidAlgebra.of_apply, columnAntisymmetrizer_def, Finset.mul_sum, Finset.smul_sum]
  simp_rw [mul_smul_comm,
    ← (MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card))).map_mul]
  apply Fintype.sum_equiv (Equiv.mulLeft q)
  intro p
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, Equiv.Perm.sign_mul, Units.val_mul,
    Int.cast_mul, smul_smul]
  rw [← mul_assoc, permSign_cast_mul_self, one_mul]

/-- Right multiplication by a member of the column group scales the column antisymmetrizer by
the sign of that member. -/
@[simp]
theorem mul_columnAntisymmetrizer_right (t : YoungTableau μ) (q : colSubgroup t) :
    columnAntisymmetrizer t * MonoidAlgebra.single (q : Equiv.Perm (Fin μ.card)) 1 =
      ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
        columnAntisymmetrizer t := by
  rw [← MonoidAlgebra.of_apply, columnAntisymmetrizer_def, Finset.sum_mul, Finset.smul_sum]
  simp_rw [smul_mul_assoc,
    ← (MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card))).map_mul]
  apply Fintype.sum_equiv (Equiv.mulRight q)
  intro p
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, Equiv.Perm.sign_mul, Units.val_mul,
    Int.cast_mul, smul_smul]
  rw [mul_left_comm, permSign_cast_mul_self, mul_one]

/-- The row symmetrizer squares to the order of the row group times itself. -/
@[simp]
theorem rowSymmetrizer_sq (t : YoungTableau μ) :
    rowSymmetrizer t * rowSymmetrizer t =
      Nat.card (rowSubgroup t) • rowSymmetrizer t := by
  nth_rewrite 1 [rowSymmetrizer_def]
  rw [Finset.sum_mul]
  simp_rw [MonoidAlgebra.of_apply, mul_rowSymmetrizer_left]
  rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-- The column antisymmetrizer squares to the order of the column group times itself. -/
@[simp]
theorem columnAntisymmetrizer_sq (t : YoungTableau μ) :
    columnAntisymmetrizer t * columnAntisymmetrizer t =
      Nat.card (colSubgroup t) • columnAntisymmetrizer t := by
  nth_rewrite 1 [columnAntisymmetrizer_def]
  rw [Finset.sum_mul]
  simp_rw [smul_mul_assoc, MonoidAlgebra.of_apply, mul_columnAntisymmetrizer_left, smul_smul,
    permSign_cast_mul_self, one_smul]
  rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-- The row group fixes the Young symmetrizer on the left. -/
@[simp]
theorem mul_youngSymmetrizer_left (t : YoungTableau μ) (p : rowSubgroup t) :
    MonoidAlgebra.single (p : Equiv.Perm (Fin μ.card)) 1 * youngSymmetrizer t =
      youngSymmetrizer t := by
  rw [youngSymmetrizer_def, ← mul_assoc, mul_rowSymmetrizer_left]

/-- The column group acts on the Young symmetrizer on the right through its sign character. -/
@[simp]
theorem mul_youngSymmetrizer_right (t : YoungTableau μ) (q : colSubgroup t) :
    youngSymmetrizer t * MonoidAlgebra.single (q : Equiv.Perm (Fin μ.card)) 1 =
      ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
        youngSymmetrizer t := by
  rw [youngSymmetrizer_def, mul_assoc, mul_columnAntisymmetrizer_right, mul_smul_comm]

/-- The coefficient of the identity permutation in a Young symmetrizer is one. -/
@[simp]
theorem youngSymmetrizer_coeff_one (t : YoungTableau μ) :
    (youngSymmetrizer t).coeff 1 = 1 := by
  rw [youngSymmetrizer_def, rowSymmetrizer_def, columnAntisymmetrizer_def,
    Finset.sum_mul]
  simp only [Finset.mul_sum, MonoidAlgebra.coeff_sum, MonoidAlgebra.of_apply]
  simp only [Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, one_mul]
  have hmul (p : rowSubgroup t) (q : colSubgroup t) :
      (p : Equiv.Perm (Fin μ.card)) * q = 1 ↔ p = 1 ∧ q = 1 := by
    constructor
    · intro hpq
      have hpq' := Subgroup.disjoint_iff_mul_eq_one.mp
        (disjoint_rowSubgroup_colSubgroup t) p.property q.property hpq
      exact ⟨Subtype.ext hpq'.1, Subtype.ext hpq'.2⟩
    · rintro ⟨rfl, rfl⟩
      simp
  have heq (p : rowSubgroup t) (q : colSubgroup t) :
      (q : Equiv.Perm (Fin μ.card)) =
          (p : Equiv.Perm (Fin μ.card))⁻¹ * 1 ↔ p = 1 ∧ q = 1 := by
    simpa only [mul_one] using
      ((mul_eq_one_iff_eq_inv' :
        (p : Equiv.Perm (Fin μ.card)) * q = 1 ↔
          (q : Equiv.Perm (Fin μ.card)) =
            (p : Equiv.Perm (Fin μ.card))⁻¹).symm.trans (hmul p q))
  simp_rw [heq]
  rw [Finset.sum_eq_single (1 : rowSubgroup t)]
  · rw [Finset.sum_eq_single (1 : colSubgroup t)] <;> simp
  · exact fun p _ hp => by simp [hp]
  · simp

/-- The coefficient of a row-group permutation in a Young symmetrizer is one: the row group
translates `c_t` to itself, so all of its coefficients on the row group agree with the
coefficient at the identity. -/
theorem youngSymmetrizer_coeff_eq_one_of_mem_rowSubgroup (t : YoungTableau μ)
    {p : Equiv.Perm (Fin μ.card)} (hp : p ∈ rowSubgroup t) :
    (youngSymmetrizer t).coeff p = 1 := by
  have h := congrArg (fun x => MonoidAlgebra.coeff x p) (mul_youngSymmetrizer_left t ⟨p, hp⟩)
  simpa using h.symm

/-- A Young symmetrizer is nonzero. -/
@[simp]
theorem youngSymmetrizer_ne_zero (t : YoungTableau μ) :
    youngSymmetrizer t ≠ 0 := by
  intro h
  have := congrArg (fun x =>
    x.coeff (1 : Equiv.Perm (Fin μ.card))) h
  simp at this

section Transport

variable (k : Type*) [CommSemiring k] [Algebra ℚ k]

/-- The Young symmetrizer `c_t` with the coefficients of its rational form transported into a
`ℚ`-algebra `k`, so that it can act on a `k`-module.

The `ℚ`-algebra hypothesis comes from `youngSymmetrizer` being defined over `ℚ` here, not from
`c_t`, whose coefficients are integral. -/
noncomputable def youngSymmetrizerOver (t : YoungTableau μ) :
    MonoidAlgebra k (Equiv.Perm (Fin μ.card)) :=
  MonoidAlgebra.mapAlgHom _ (Algebra.ofId ℚ k) (youngSymmetrizer t)

/-- The transport of a Young symmetrizer applies the structure map of the algebra to every
coefficient. -/
theorem youngSymmetrizerOver_def (t : YoungTableau μ) :
    youngSymmetrizerOver k t =
      MonoidAlgebra.mapAlgHom _ (Algebra.ofId ℚ k) (youngSymmetrizer t) :=
  (rfl)

/-- The coefficients of the transported Young symmetrizer are the images of the rational
coefficients. -/
@[simp]
theorem youngSymmetrizerOver_coeff (t : YoungTableau μ) (σ : Equiv.Perm (Fin μ.card)) :
    (youngSymmetrizerOver k t).coeff σ = algebraMap ℚ k ((youngSymmetrizer t).coeff σ) := by
  rw [youngSymmetrizerOver_def, MonoidAlgebra.coeff_mapAlgHom, Algebra.ofId_apply]

end Transport

end

end YoungTableau

end TauCeti
