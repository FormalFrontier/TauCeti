/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.RepresentationTheory.SubgroupCharSum
public import TauCeti.RepresentationTheory.Symmetric.RowColumnSubgroup

/-!
# Young symmetrizers

For a Young tableau `t`, this file defines the row symmetrizer `a_t`, the column
antisymmetrizer `b_t`, and the Young symmetrizer `c_t = a_t b_t` in the rational group
algebra of the symmetric group on the entries of `t`.

The defining coefficient formulas are accompanied by the translation laws that characterize
the two factors: the row group fixes `a_t`, while the column group acts on `b_t` through the
sign character.  In particular, each factor squares to its subgroup order times itself.
Both factors are instances of a single construction: the character sum
`∑_{h ∈ H} χ(h) h` of a multiplicative character over a finite subgroup,
`TauCeti.subgroupCharSum`.  The row symmetrizer is the trivial character over the row group and
the column antisymmetrizer is the sign character over the column group, so the coefficient
formula, the two translation laws, the square, and the values on a trivial or full subgroup are
read off from that shared API instead of being proved once for each factor.
These are the elementary inputs to the essential-idempotence theorem for `c_t` and the
construction of Specht modules.  The two extreme shapes are also evaluated here: a trivial row or
column group collapses the corresponding factor to `1`, so on a shape with at most one row the
whole group fixes `c_t`, and on a shape with at most one column it scales `c_t` by the sign.  The
same two degeneracies evaluate the transported symmetrizer `youngSymmetrizerOver` outright, as the
full symmetrization `∑_σ σ` and the full antisymmetrization `∑_σ sgn(σ) σ` of the group algebra.
Finally, `b_t` acting on an arbitrary representation is unfolded into the signed sum over the
column group, which is how every downstream computation with the operator `b_t` begins.

The file closes with a third signed sum at the sign character, `TauCeti.antisymmetrizerOn X`: the
sum `∑ sgn(σ) σ` over the permutations of an arbitrary type fixing everything outside a finite set
`X`.  It is `b_t` with the column group replaced by the pointwise fixing subgroup of the
complement of `X`, so it shares the coefficient formula, the translation law and the vanishing
criterion with `b_t`, and it is the element the Garnir relations of
`TauCeti/RepresentationTheory/Symmetric/Specht/Garnir.lean` are stated for.  Nothing about it
refers to a tableau, only to the sign character defined here.

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

/-- The sign character of the symmetric group, valued in `ℚ`.  Together with the trivial
character it is one of the two characters whose character sums over a subgroup are the
symmetrizers of this file. -/
noncomputable def signChar {α : Type*} [DecidableEq α] [Fintype α] : Equiv.Perm α →* ℚ :=
  (Int.castRingHom ℚ).toMonoidHom.comp ((Units.coeHom ℤ).comp Equiv.Perm.sign)

@[simp]
theorem signChar_apply {α : Type*} [DecidableEq α] [Fintype α] (σ : Equiv.Perm α) :
    signChar σ = ((Equiv.Perm.sign σ : ℤ) : ℚ) :=
  (rfl)

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

/-- The row symmetrizer is the character sum of the trivial character over the row group. -/
theorem rowSymmetrizer_eq_subgroupCharSum (t : YoungTableau μ) :
    rowSymmetrizer t = subgroupCharSum 1 (rowSubgroup t) := by
  rw [rowSymmetrizer_def, subgroupCharSum_def]
  simp

/-- The column antisymmetrizer is the character sum of the sign character over the column
group. -/
theorem columnAntisymmetrizer_eq_subgroupCharSum (t : YoungTableau μ) :
    columnAntisymmetrizer t = subgroupCharSum signChar (colSubgroup t) := by
  rw [columnAntisymmetrizer_def, subgroupCharSum_def]
  simp

/-- The coefficient of a permutation in the row symmetrizer is its row-group indicator. -/
@[simp]
theorem rowSymmetrizer_coeff (t : YoungTableau μ) (σ : Equiv.Perm (Fin μ.card)) :
    (rowSymmetrizer t).coeff σ = if σ ∈ rowSubgroup t then 1 else 0 := by
  rw [rowSymmetrizer_eq_subgroupCharSum, subgroupCharSum_coeff]
  simp

/-- The coefficient of a permutation in the column antisymmetrizer is its sign on the column
group and zero off that group. -/
@[simp]
theorem columnAntisymmetrizer_coeff (t : YoungTableau μ) (σ : Equiv.Perm (Fin μ.card)) :
    (columnAntisymmetrizer t).coeff σ =
      if σ ∈ colSubgroup t then ((Equiv.Perm.sign σ : ℤ) : ℚ) else 0 := by
  rw [columnAntisymmetrizer_eq_subgroupCharSum, subgroupCharSum_coeff]
  simp

/-- Left multiplication by a member of the row group fixes the row symmetrizer. -/
@[simp]
theorem mul_rowSymmetrizer_left (t : YoungTableau μ) (p : rowSubgroup t) :
    MonoidAlgebra.single (p : Equiv.Perm (Fin μ.card)) 1 * rowSymmetrizer t =
      rowSymmetrizer t := by
  rw [rowSymmetrizer_eq_subgroupCharSum, single_mul_subgroupCharSum]
  simp

/-- Right multiplication by a member of the row group fixes the row symmetrizer. -/
@[simp]
theorem mul_rowSymmetrizer_right (t : YoungTableau μ) (p : rowSubgroup t) :
    rowSymmetrizer t * MonoidAlgebra.single (p : Equiv.Perm (Fin μ.card)) 1 =
      rowSymmetrizer t := by
  rw [rowSymmetrizer_eq_subgroupCharSum, subgroupCharSum_mul_single]
  simp

/-- Left multiplication by a member of the column group scales the column antisymmetrizer by
the sign of that member. -/
@[simp]
theorem mul_columnAntisymmetrizer_left (t : YoungTableau μ) (q : colSubgroup t) :
    MonoidAlgebra.single (q : Equiv.Perm (Fin μ.card)) 1 * columnAntisymmetrizer t =
      ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
        columnAntisymmetrizer t := by
  rw [columnAntisymmetrizer_eq_subgroupCharSum, single_mul_subgroupCharSum]
  simp

/-- Right multiplication by a member of the column group scales the column antisymmetrizer by
the sign of that member. -/
@[simp]
theorem mul_columnAntisymmetrizer_right (t : YoungTableau μ) (q : colSubgroup t) :
    columnAntisymmetrizer t * MonoidAlgebra.single (q : Equiv.Perm (Fin μ.card)) 1 =
      ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
        columnAntisymmetrizer t := by
  rw [columnAntisymmetrizer_eq_subgroupCharSum, subgroupCharSum_mul_single]
  simp

/-- The row symmetrizer squares to the order of the row group times itself. -/
@[simp]
theorem rowSymmetrizer_sq (t : YoungTableau μ) :
    rowSymmetrizer t * rowSymmetrizer t =
      Nat.card (rowSubgroup t) • rowSymmetrizer t := by
  rw [rowSymmetrizer_eq_subgroupCharSum, subgroupCharSum_mul_self]

/-- The column antisymmetrizer squares to the order of the column group times itself. -/
@[simp]
theorem columnAntisymmetrizer_sq (t : YoungTableau μ) :
    columnAntisymmetrizer t * columnAntisymmetrizer t =
      Nat.card (colSubgroup t) • columnAntisymmetrizer t := by
  rw [columnAntisymmetrizer_eq_subgroupCharSum, subgroupCharSum_mul_self]

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
  rw [rowSymmetrizer_eq_subgroupCharSum, subgroupCharSum_eq_one _ _ h]

/-- A trivial column group leaves the column antisymmetrizer as the empty antisymmetrization,
`1`. -/
theorem columnAntisymmetrizer_eq_one (t : YoungTableau μ) (h : colSubgroup t = ⊥) :
    columnAntisymmetrizer t = 1 := by
  rw [columnAntisymmetrizer_eq_subgroupCharSum, subgroupCharSum_eq_one _ _ h]

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
  rw [columnAntisymmetrizer_eq_subgroupCharSum, asAlgebraHom_subgroupCharSum_apply]
  simp only [signChar_apply]

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
    rowSymmetrizer_eq_subgroupCharSum, subgroupCharSum_eq_sum_of_eq_top _ _ h, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [MonoidHom.one_apply, one_smul, MonoidAlgebra.of_apply, MonoidAlgebra.mapAlgHom_single,
    map_one, MonoidAlgebra.of_apply]

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
    columnAntisymmetrizer_eq_subgroupCharSum, subgroupCharSum_eq_sum_of_eq_top _ _ h, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [signChar_apply, Int.cast_smul_eq_zsmul ℚ, map_zsmul, MonoidAlgebra.of_apply,
    MonoidAlgebra.mapAlgHom_single, map_one, MonoidAlgebra.of_apply]

end TransportRing

end

end YoungTableau

/-! ## The antisymmetrizer of a set of points

The signed sum over the permutations supported in a finite set is the character sum of the sign
character over the pointwise fixing subgroup of the complement.  Nothing below refers to a
tableau, only to `TauCeti.YoungTableau.signChar`. -/

section AntisymmetrizerOn

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Classical decidability of membership in the subgroup of permutations fixing everything outside
a finite set, used to form its finite sum. -/
noncomputable local instance decidablePredMemFixingSubgroupCompl (X : Finset α) :
    DecidablePred (· ∈ fixingSubgroup (Equiv.Perm α) ((X : Set α)ᶜ)) :=
  Classical.decPred _

/-- The **antisymmetrizer** of a finite set `X` of points: the signed sum `∑ sgn(σ) σ`, in the
rational group algebra of `Equiv.Perm α`, over the permutations `σ` fixing every point outside `X`.

For `X` the labels lying in one column of a Young tableau this is the factor of that tableau's
column antisymmetrizer belonging to that column; the relations it satisfies on the polytabloids of
a tableau are the Garnir relations. -/
noncomputable def antisymmetrizerOn (X : Finset α) : MonoidAlgebra ℚ (Equiv.Perm α) :=
  subgroupCharSum YoungTableau.signChar
    (fixingSubgroup (Equiv.Perm α) ((X : Set α)ᶜ))

theorem antisymmetrizerOn_def (X : Finset α) :
    antisymmetrizerOn X =
      subgroupCharSum YoungTableau.signChar
        (fixingSubgroup (Equiv.Perm α) ((X : Set α)ᶜ)) :=
  (rfl)

omit [DecidableEq α] [Fintype α] in
/-- A permutation fixing every point outside `X` belongs to the subgroup the antisymmetrizer of
`X` is summed over. -/
private theorem mem_fixingSubgroup_compl_of_forall_notMem {X : Finset α} {σ : Equiv.Perm α}
    (hσ : ∀ k ∉ X, σ k = k) : σ ∈ fixingSubgroup (Equiv.Perm α) ((X : Set α)ᶜ) :=
  (mem_fixingSubgroup_iff _).mpr fun k hk => hσ k (by simpa using hk)

/-- The coefficient of a permutation in `TauCeti.antisymmetrizerOn X` is its sign if it is
supported in `X`, and zero otherwise. -/
@[simp]
theorem antisymmetrizerOn_coeff (X : Finset α) (σ : Equiv.Perm α) :
    (antisymmetrizerOn X).coeff σ =
      if ∀ k ∉ X, σ k = k then ((Equiv.Perm.sign σ : ℤ) : ℚ) else 0 := by
  classical
  rw [antisymmetrizerOn_def, subgroupCharSum_coeff]
  simp [mem_fixingSubgroup_iff]

/-- The permutations summed over by `TauCeti.antisymmetrizerOn X`, as a `Finset`. -/
private theorem mem_filter_forall_notMem_iff (X : Finset α)
    [DecidablePred fun σ : Equiv.Perm α => ∀ k ∉ X, σ k = k] (σ : Equiv.Perm α) :
    σ ∈ ({σ : Equiv.Perm α | ∀ k ∉ X, σ k = k} : Finset (Equiv.Perm α)) ↔
      σ ∈ fixingSubgroup (Equiv.Perm α) ((X : Set α)ᶜ) := by
  simp [mem_fixingSubgroup_iff]

/-- The antisymmetrizer of a set, acting on a representation of the symmetric group, is the signed
sum of the actions of the permutations fixing everything outside that set.

The decidability of the summation range is an instance argument rather than a synthesized one, so
that the equation rewrites a sum however its own filter was built. -/
theorem asAlgebraHom_antisymmetrizerOn_apply {M : Type*} [AddCommGroup M] [Module ℚ M]
    (V : Representation ℚ (Equiv.Perm α) M) (X : Finset α)
    [DecidablePred fun σ : Equiv.Perm α => ∀ k ∉ X, σ k = k] (v : M) :
    V.asAlgebraHom (antisymmetrizerOn X) v =
      ∑ σ ∈ {σ : Equiv.Perm α | ∀ k ∉ X, σ k = k},
        ((Equiv.Perm.sign σ : ℤ) : ℚ) • V σ v := by
  rw [antisymmetrizerOn_def, asAlgebraHom_subgroupCharSum_apply,
    ← Finset.sum_subtype _ (mem_filter_forall_notMem_iff X)
      (fun σ => YoungTableau.signChar σ • V σ v)]
  simp only [YoungTableau.signChar_apply]

/-- **Right multiplication by a permutation supported in `X` scales the antisymmetrizer of `X` by
its sign**, since the antisymmetrizer absorbs it up to that sign. -/
@[simp]
theorem antisymmetrizerOn_mul_single {X : Finset α} {p : Equiv.Perm α} (hp : ∀ k ∉ X, p k = k) :
    antisymmetrizerOn X * MonoidAlgebra.single p (1 : ℚ) =
      ((Equiv.Perm.sign p : ℤ) : ℚ) • antisymmetrizerOn X := by
  rw [antisymmetrizerOn_def,
    subgroupCharSum_mul_single _ _ ⟨p, mem_fixingSubgroup_compl_of_forall_notMem hp⟩]
  simp

/-- **A signed sum annihilates whatever an odd permutation in it fixes.**  If an odd permutation
supported in `X` fixes `v`, then the antisymmetrizer of `X` kills `v`: absorbing that permutation
negates the sum while leaving `v` alone. -/
theorem asAlgebraHom_antisymmetrizerOn_apply_eq_zero {M : Type*} [AddCommGroup M] [Module ℚ M]
    (V : Representation ℚ (Equiv.Perm α) M) {X : Finset α} {p : Equiv.Perm α}
    (hp : ∀ k ∉ X, p k = k) (hsign : Equiv.Perm.sign p = -1) {v : M} (hv : V p v = v) :
    V.asAlgebraHom (antisymmetrizerOn X) v = 0 := by
  have : IsAddTorsionFree M := .of_module_rat _
  rw [antisymmetrizerOn_def]
  refine asAlgebraHom_subgroupCharSum_apply_eq_zero _ _ (nsmul_right_injective two_ne_zero) V
    (mem_fixingSubgroup_compl_of_forall_notMem hp) ?_ hv
  simp [hsign]

end AntisymmetrizerOn

end TauCeti
