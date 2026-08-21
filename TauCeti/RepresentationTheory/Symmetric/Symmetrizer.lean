/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.RepresentationTheory.Basic
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
construction of Specht modules.  The two extreme shapes are also evaluated here: a trivial row or
column group collapses the corresponding factor to `1`, so on a shape with at most one row the
whole group fixes `c_t`, and on a shape with at most one column it scales `c_t` by the sign.  The
same two degeneracies evaluate the transported symmetrizer `youngSymmetrizerOver` outright, as the
full symmetrization `∑_σ σ` and the full antisymmetrization `∑_σ sgn(σ) σ` of the group algebra.
Finally, `b_t` acting on an arbitrary representation is unfolded into the signed sum over the
column group, which is how every downstream computation with the operator `b_t` begins.

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
  · rw [ite_eq_left hσ,
      Finset.sum_eq_single (⟨σ, hσ⟩ : rowSubgroup t)]
    · simp
    · exact fun p _ hp => ite_eq_right fun h => hp (Subtype.ext h)
    · simp
  · rw [ite_eq_right hσ]
    exact Finset.sum_eq_zero fun p _ =>
      ite_eq_right fun h : (p : Equiv.Perm (Fin μ.card)) = σ => hσ (h ▸ p.property)

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
  · rw [ite_eq_left hσ,
      Finset.sum_eq_single (⟨σ, hσ⟩ : colSubgroup t)]
    · simp
    · exact fun q _ hq => by
        rw [ite_eq_right fun h => hq (Subtype.ext h), mul_zero]
    · simp
  · rw [ite_eq_right hσ]
    exact Finset.sum_eq_zero fun q _ => by
      rw [ite_eq_right fun h : (q : Equiv.Perm (Fin μ.card)) = σ => hσ (h ▸ q.property),
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

/-! ### The symmetrizers of an extreme shape -/

/-- A trivial row group leaves the row symmetrizer as the empty symmetrization, `1`. -/
theorem rowSymmetrizer_eq_one (t : YoungTableau μ) (h : rowSubgroup t = ⊥) :
    rowSymmetrizer t = 1 := by
  ext σ
  by_cases hσ : σ = 1
  · simp [rowSymmetrizer_coeff, h, MonoidAlgebra.one_def, hσ]
  · simp [rowSymmetrizer_coeff, h, MonoidAlgebra.one_def, Subgroup.mem_bot, hσ]

/-- A trivial column group leaves the column antisymmetrizer as the empty antisymmetrization,
`1`. -/
theorem columnAntisymmetrizer_eq_one (t : YoungTableau μ) (h : colSubgroup t = ⊥) :
    columnAntisymmetrizer t = 1 := by
  ext σ
  by_cases hσ : σ = 1
  · simp [columnAntisymmetrizer_coeff, h, MonoidAlgebra.one_def, hσ]
  · simp [columnAntisymmetrizer_coeff, h, MonoidAlgebra.one_def, Subgroup.mem_bot, hσ]

/-- With a trivial column group the Young symmetrizer is the row symmetrizer. -/
theorem youngSymmetrizer_eq_rowSymmetrizer (t : YoungTableau μ) (h : colSubgroup t = ⊥) :
    youngSymmetrizer t = rowSymmetrizer t := by
  rw [youngSymmetrizer_def, columnAntisymmetrizer_eq_one t h, mul_one]

/-- With a trivial row group the Young symmetrizer is the column antisymmetrizer. -/
theorem youngSymmetrizer_eq_columnAntisymmetrizer (t : YoungTableau μ) (h : rowSubgroup t = ⊥) :
    youngSymmetrizer t = columnAntisymmetrizer t := by
  rw [youngSymmetrizer_def, rowSymmetrizer_eq_one t h, one_mul]

/-- On a shape with at most one row every group element fixes the Young symmetrizer. -/
theorem single_mul_youngSymmetrizer_of_rowSubgroup_eq_top (t : YoungTableau μ)
    (h : rowSubgroup t = ⊤) (g : Equiv.Perm (Fin μ.card)) :
    MonoidAlgebra.single g (1 : ℚ) * youngSymmetrizer t = youngSymmetrizer t :=
  mul_youngSymmetrizer_left t ⟨g, by rw [h]; exact Subgroup.mem_top g⟩

/-- On a shape with at most one column every group element scales the Young symmetrizer by its
sign. -/
theorem single_mul_youngSymmetrizer_of_colSubgroup_eq_top (t : YoungTableau μ)
    (h : colSubgroup t = ⊤) (g : Equiv.Perm (Fin μ.card)) :
    MonoidAlgebra.single g (1 : ℚ) * youngSymmetrizer t =
      ((Equiv.Perm.sign g : ℤ) : ℚ) • youngSymmetrizer t := by
  rw [youngSymmetrizer_eq_columnAntisymmetrizer t (rowSubgroup_eq_bot_of_colSubgroup_eq_top t h)]
  exact mul_columnAntisymmetrizer_left t ⟨g, by rw [h]; exact Subgroup.mem_top g⟩

/-! ### The column antisymmetrizer as an operator -/

/-- The column antisymmetrizer of `t` acts on any representation as the signed sum of the
permutations in the column group of `t`. -/
theorem asAlgebraHom_columnAntisymmetrizer_apply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ρ : Representation ℚ (Equiv.Perm (Fin μ.card)) V) (t : YoungTableau μ) (v : V) :
    ρ.asAlgebraHom (columnAntisymmetrizer t) v =
      ∑ q : colSubgroup t,
        ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) • ρ q v := by
  rw [columnAntisymmetrizer_def, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one,
    LinearMap.smul_apply]

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

/-- **The column group acts on the transported Young symmetrizer through its sign character.**
This is `TauCeti.mul_youngSymmetrizer_right` carried into `k`. The sign keeps acting as a rational
scalar, which is available because `k` is a `ℚ`-algebra; it cannot be phrased as a `ℤ`-action,
since a `CommSemiring` `k` need not have negation. -/
@[simp]
theorem mul_youngSymmetrizerOver_right (t : YoungTableau μ) (q : colSubgroup t) :
    youngSymmetrizerOver k t * MonoidAlgebra.single (q : Equiv.Perm (Fin μ.card)) 1 =
      ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) • youngSymmetrizerOver k t := by
  have h := congrArg (MonoidAlgebra.mapAlgHom (Equiv.Perm (Fin μ.card)) (Algebra.ofId ℚ k))
    (mul_youngSymmetrizer_right t q)
  rw [map_mul, MonoidAlgebra.mapAlgHom_single, map_one, map_smul] at h
  rwa [youngSymmetrizerOver_def]

/-- **The Young symmetrizer of a shape with at most one row is the full symmetrization**
`∑_σ σ`: the row group is everything and the column group is trivial. -/
theorem youngSymmetrizerOver_eq_sum_of_rowSubgroup_eq_top (t : YoungTableau μ)
    (h : rowSubgroup t = ⊤) :
    youngSymmetrizerOver k t =
      ∑ σ : Equiv.Perm (Fin μ.card), MonoidAlgebra.of k (Equiv.Perm (Fin μ.card)) σ := by
  rw [youngSymmetrizerOver_def,
    youngSymmetrizer_eq_rowSymmetrizer t (colSubgroup_eq_bot_of_rowSubgroup_eq_top t h),
    rowSymmetrizer_def, map_sum]
  refine Finset.sum_bij (fun p _ => (p : Equiv.Perm (Fin μ.card)))
    (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ hab => Subtype.ext hab)
    (fun σ _ => ?_) fun p _ => ?_
  · refine ⟨⟨σ, by rw [h]; exact Subgroup.mem_top σ⟩, ?_, rfl⟩
    simp
  · rw [MonoidAlgebra.of_apply, MonoidAlgebra.mapAlgHom_single, map_one, MonoidAlgebra.of_apply]

end Transport

section TransportRing

-- The signed sum below is a `ℤ`-linear combination, so it asks the target ring for negation; that
-- is the only difference from the `CommSemiring` hypothesis of the section above.
variable (k : Type*) [CommRing k] [Algebra ℚ k]

/-- **The Young symmetrizer of a shape with at most one column is the full antisymmetrization**
`∑_σ sgn(σ) σ`: the column group is everything and the row group is trivial. -/
theorem youngSymmetrizerOver_eq_sum_of_colSubgroup_eq_top (t : YoungTableau μ)
    (h : colSubgroup t = ⊤) :
    youngSymmetrizerOver k t =
      ∑ σ : Equiv.Perm (Fin μ.card),
        (Equiv.Perm.sign σ : ℤ) • MonoidAlgebra.of k (Equiv.Perm (Fin μ.card)) σ := by
  rw [youngSymmetrizerOver_def,
    youngSymmetrizer_eq_columnAntisymmetrizer t (rowSubgroup_eq_bot_of_colSubgroup_eq_top t h),
    columnAntisymmetrizer_def, map_sum]
  refine Finset.sum_bij (fun q _ => (q : Equiv.Perm (Fin μ.card)))
    (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ hab => Subtype.ext hab)
    (fun σ _ => ?_) fun q _ => ?_
  · refine ⟨⟨σ, by rw [h]; exact Subgroup.mem_top σ⟩, ?_, rfl⟩
    simp
  · rw [Int.cast_smul_eq_zsmul ℚ, map_zsmul, MonoidAlgebra.of_apply,
      MonoidAlgebra.mapAlgHom_single, map_one, MonoidAlgebra.of_apply]

end TransportRing

end

end YoungTableau

end TauCeti
