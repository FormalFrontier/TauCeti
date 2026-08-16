/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Coxeter.Matrix
public import Mathlib.LinearAlgebra.Matrix.Cartan
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.RankTwo
public import TauCeti.LinearAlgebra.RootSystem.SimpleReflections

public section

open scoped Matrix

/-!
# The Coxeter matrix of a base

A base of a finite crystallographic root pairing has a Cartan matrix, and the Cartan matrix
determines a Coxeter matrix: the entry attached to a pair of distinct simple roots is read off
their Cartan product `⟨αᵢ, αⱼ^∨⟩⟨αⱼ, αᵢ^∨⟩` by `0 ↦ 2`, `1 ↦ 3`, `2 ↦ 4`, `3 ↦ 6`. This file
proves that the Cartan product of two distinct simple roots really does lie in `{0, 1, 2, 3}`, and
packages the resulting assignment as a genuine `CoxeterMatrix` indexed by the simple roots.

The numerical content is the exclusion of the value `4`. Mathlib bounds the Coxeter weight of a
finite crystallographic pairing by `4` and pins it to `{0, 1, 2, 3, 4}`
(`RootPairing.coxeterWeightIn_mem_set_of_isCrystallographic`), and the value `4` is attained
exactly by linearly dependent pairs of roots
(`RootPairing.linearIndependent_iff_coxeterWeightIn_ne_four`); distinct simple roots are
independent, so `4` is unavailable to them.

The translation `TauCeti.coxeterOrder` is defined on all of `ℤ` and takes the Cartan product `4` to
`1`, which is the mathematically correct value rather than a junk one: product `4` means the two
roots are proportional, so the two reflections coincide and their product is the identity. That
choice is what makes the diagonal of the matrix come out as `1` without a case split, since a
simple root has Cartan product `4` with itself. Products outside `{0, 1, 2, 3, 4}` do not occur
here and are sent to `0`, Mathlib's encoding of an infinite Coxeter order.

The final section checks the smallest of the intended braid relations, the one available before the
Coxeter presentation of the Weyl group is built: an entry is `2` exactly for orthogonal simple
roots, and there the two simple reflections commute
(`TauCeti.RootPairing.weylGroup.commute_ofIdx_of_isOrthogonal`) and their product has order exactly
`2`, as the entry asserts.

## Main definitions

* `TauCeti.coxeterOrder` translates a Cartan product into the order of the product of the two
  reflections.
* `TauCeti.coxeterMatrixOfCartanMatrix` performs that translation on an arbitrary matrix whose
  diagonal is `2` and whose off-diagonal Cartan products lie in `{0, 1, 2, 3}`.
* `TauCeti.coxeterMatrixOfBase` is the Coxeter matrix of a base, indexed by its simple roots.

## Main results

* `TauCeti.cartanMatrix_mul_cartanMatrix_mem_of_ne`: the Cartan product of two distinct simple
  roots lies in `{0, 1, 2, 3}`, so `TauCeti.coxeterOrder` reads a genuine Coxeter order off it.
* `TauCeti.coxeterMatrixOfBase_eq_two_iff`: an entry is `2` exactly for orthogonal simple roots.
  In particular the diagonal entries are not `2`, since no root is orthogonal to itself.
* `TauCeti.isSimplyLaced_iff_forall_coxeterMatrixOfBase_le_three`: the Cartan matrix is simply laced
  exactly when all entries are at most `3`.
* `TauCeti.coxeterMatrixOfBase_eq_three_of_hasCartanType_A_two` and its `B₂` and `G₂`
  companions evaluate the Coxeter entries of the three rank-two Cartan types.
* `TauCeti.RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_two_of_coxeterMatrixOfBase_eq_two`:
  where the matrix entry is `2`, the product of the two simple reflections does have order `2`.

## References

This file implements “The Coxeter matrix of a base” in Layer 2 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, following the target signature
`coxeterMatrixOfBase` in that roadmap's `Suggested.lean`. The classification of rank-two
crystallographic configurations behind it is Bourbaki, *Lie Groups and Lie Algebras*, Chapters
4--6, Ch. VI, §1.3.
-/

namespace TauCeti

open Set

universe u v w x

/-! ## Reading a Coxeter order off a Cartan product -/

/-- The order of the product of the reflections in two roots of Cartan product `c`.

For a finite crystallographic pairing the only products that occur are `0`, `1`, `2`, `3` and `4`.
The first four are the rank-two configurations `A₁ × A₁`, `A₂`, `B₂` and `G₂`, whose products of
reflections are rotations of order `2`, `3`, `4` and `6`. Product `4` means the two roots are
proportional, so the two reflections agree and their product is the identity, of order `1`; this is
in particular the value taken by a root against itself. Every other integer is sent to `0`,
Mathlib's encoding of an infinite order. -/
def coxeterOrder (c : ℤ) : ℕ :=
  if c = 0 then 2 else if c = 1 then 3 else if c = 2 then 4 else if c = 3 then 6 else
    if c = 4 then 1 else 0

@[simp] lemma coxeterOrder_zero : coxeterOrder 0 = 2 := by norm_num [coxeterOrder]

@[simp] lemma coxeterOrder_one : coxeterOrder 1 = 3 := by norm_num [coxeterOrder]

@[simp] lemma coxeterOrder_two : coxeterOrder 2 = 4 := by norm_num [coxeterOrder]

@[simp] lemma coxeterOrder_three : coxeterOrder 3 = 6 := by norm_num [coxeterOrder]

@[simp] lemma coxeterOrder_four : coxeterOrder 4 = 1 := by norm_num [coxeterOrder]

/-- Outside `{0, 1, 2, 3, 4}` the translation falls back to `0`, Mathlib's encoding of an infinite
order. No such Cartan product occurs for a finite crystallographic pairing; this lemma pins the
value down at the remaining integers, so the five equation lemmas above determine `coxeterOrder`
everywhere. -/
lemma coxeterOrder_eq_zero_iff {c : ℤ} : coxeterOrder c = 0 ↔ c ∉ ({0, 1, 2, 3, 4} : Set ℤ) := by
  simp only [mem_insert_iff, mem_singleton_iff, not_or, coxeterOrder]
  split_ifs with h₀ h₁ h₂ h₃ h₄ <;> simp_all

/-- On the products that occur for a pair of independent roots, `coxeterOrder` takes the four
dihedral values. -/
lemma coxeterOrder_mem {c : ℤ} (hc : c ∈ ({0, 1, 2, 3} : Set ℤ)) :
    coxeterOrder c ∈ ({2, 3, 4, 6} : Set ℕ) := by
  simp only [mem_insert_iff, mem_singleton_iff] at hc ⊢
  rcases hc with rfl | rfl | rfl | rfl <;> simp

/-- The dihedral values are all at least `2`; in particular none of them is `1`, which is what a
`CoxeterMatrix` demands off the diagonal. -/
lemma two_le_coxeterOrder {c : ℤ} (hc : c ∈ ({0, 1, 2, 3} : Set ℤ)) : 2 ≤ coxeterOrder c := by
  have := coxeterOrder_mem hc
  simp only [mem_insert_iff, mem_singleton_iff] at this
  omega

/-- The dihedral values are all at most `6`; in particular none of them is `0`, so no entry of the
Coxeter matrix of a base is infinite. -/
lemma coxeterOrder_le_six {c : ℤ} (hc : c ∈ ({0, 1, 2, 3} : Set ℤ)) : coxeterOrder c ≤ 6 := by
  have := coxeterOrder_mem hc
  simp only [mem_insert_iff, mem_singleton_iff] at this
  omega

/-- The products with at most one edge, namely `0` (no edge) and `1` (a single edge), are exactly
those of Coxeter order at most `3`. -/
lemma coxeterOrder_le_three_iff {c : ℤ} (hc : c ∈ ({0, 1, 2, 3} : Set ℤ)) :
    coxeterOrder c ≤ 3 ↔ c = 0 ∨ c = 1 := by
  simp only [mem_insert_iff, mem_singleton_iff] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp

/-- The product `0` is the only one of Coxeter order `2`. -/
lemma coxeterOrder_eq_two_iff {c : ℤ} (hc : c ∈ ({0, 1, 2, 3} : Set ℤ)) :
    coxeterOrder c = 2 ↔ c = 0 := by
  simp only [mem_insert_iff, mem_singleton_iff] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp

/-! ## The Coxeter matrix of a generalized Cartan matrix -/

section OfCartanMatrix

/-- **The Coxeter matrix read off a Cartan matrix.** The entry at a pair of nodes is the Coxeter
order `TauCeti.coxeterOrder` of their Cartan product; on the diagonal that is `1`, a node having
Cartan product `4` with itself.

Only two properties of the matrix are used, and both are hypotheses here: its diagonal entries are
`2`, and off the diagonal its Cartan products lie in `{0, 1, 2, 3}`, the four values that name a
dihedral order. It is the construction behind `TauCeti.coxeterMatrixOfBase`, applied to the Cartan
matrix of a base, and behind `TauCeti.DynkinType.coxeterMatrix`, applied to a standard Cartan
matrix in the Bourbaki numbering.

The body is not exposed: `TauCeti.coxeterMatrixOfCartanMatrix_apply` is the entry API. -/
def coxeterMatrixOfCartanMatrix {B : Type*} (A : Matrix B B ℤ) (hdiag : ∀ i, A i i = 2)
    (hmem : ∀ i j, i ≠ j → A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ)) : CoxeterMatrix B where
  M := .of fun i j ↦ coxeterOrder (A i j * A j i)
  isSymm := by
    ext i j
    simp [Matrix.transpose_apply, mul_comm]
  diagonal i := by simp [hdiag i]
  off_diagonal i j hij := by
    have := two_le_coxeterOrder (hmem i j hij)
    simp only [Matrix.of_apply]
    omega

-- `(rfl)`, not `rfl`: the body of `coxeterMatrixOfCartanMatrix` is deliberately left unexposed, and
-- the parenthesised form keeps this proof out of the exported definitional-equality check.
/-- The entry of the Coxeter matrix of a Cartan matrix at a pair of nodes is `coxeterOrder` applied
to the product of the two Cartan entries. -/
@[simp]
lemma coxeterMatrixOfCartanMatrix_apply {B : Type*} (A : Matrix B B ℤ) (hdiag : ∀ i, A i i = 2)
    (hmem : ∀ i j, i ≠ j → A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ)) (i j : B) :
    coxeterMatrixOfCartanMatrix A hdiag hmem i j = coxeterOrder (A i j * A j i) := (rfl)

/-- **Two distinct nodes carry the Coxeter entry `2` exactly when the Cartan entry between them
vanishes**, provided the zero pattern of the Cartan matrix is symmetric: the product of the two
entries then vanishes exactly when the first of them does. -/
lemma coxeterMatrixOfCartanMatrix_apply_eq_two_iff {B : Type*} (A : Matrix B B ℤ)
    (hdiag : ∀ i, A i i = 2) (hmem : ∀ i j, i ≠ j → A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ))
    (hsymm : ∀ i j, A i j = 0 → A j i = 0) {i j : B} (hij : i ≠ j) :
    coxeterMatrixOfCartanMatrix A hdiag hmem i j = 2 ↔ A i j = 0 := by
  rw [coxeterMatrixOfCartanMatrix_apply, coxeterOrder_eq_two_iff (hmem i j hij), mul_eq_zero]
  exact or_iff_left_iff_imp.mpr (hsymm j i)

end OfCartanMatrix

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-! ## The Cartan product of two simple roots -/

section CartanProduct

variable [P.IsCrystallographic] (b : P.Base)

/-- The Cartan product of a pair of simple roots is their Coxeter weight. -/
lemma cartanMatrix_mul_cartanMatrix_eq_coxeterWeightIn (i j : b.support) :
    b.cartanMatrix i j * b.cartanMatrix j i = P.coxeterWeightIn ℤ i j := rfl

variable [CharZero R] [IsDomain R]

/-- The Cartan product of two simple roots vanishes exactly when the first Cartan entry does: both
entries vanish together, since the zero pattern of a Cartan matrix is symmetric. -/
lemma cartanMatrix_mul_cartanMatrix_eq_zero_iff (i j : b.support) :
    b.cartanMatrix i j * b.cartanMatrix j i = 0 ↔ b.cartanMatrix i j = 0 := by
  rw [mul_eq_zero]
  exact or_iff_left_iff_imp.mpr fun h ↦ b.cartanMatrix_apply_eq_zero_iff_symm.mpr h

/-- The Cartan product of two simple roots vanishes exactly when they are orthogonal. -/
lemma cartanMatrix_mul_cartanMatrix_eq_zero_iff_isOrthogonal (i j : b.support) :
    b.cartanMatrix i j * b.cartanMatrix j i = 0 ↔ P.IsOrthogonal (i : ι) (j : ι) := by
  rw [cartanMatrix_mul_cartanMatrix_eq_zero_iff]
  refine ⟨fun h ↦ ⟨b.cartanMatrix_apply_eq_zero_iff_pairing.mp h,
    b.cartanMatrix_apply_eq_zero_iff_pairing.mp (b.cartanMatrix_apply_eq_zero_iff_symm.mp h)⟩,
    fun h ↦ b.cartanMatrix_apply_eq_zero_iff_pairing.mpr h.1⟩

variable [Finite ι]

/-- **The Cartan product of two distinct simple roots lies in `{0, 1, 2, 3}`**, so `coxeterOrder`
reads a genuine Coxeter order off it.

Mathlib confines the Coxeter weight of a finite crystallographic pairing to `{0, 1, 2, 3, 4}`, and
the value `4` is attained only by linearly dependent pairs of roots. Distinct simple roots are
linearly independent, which removes it. -/
theorem cartanMatrix_mul_cartanMatrix_mem_of_ne {i j : b.support} (hij : i ≠ j) :
    b.cartanMatrix i j * b.cartanMatrix j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have hne : P.coxeterWeightIn ℤ (i : ι) (j : ι) ≠ 4 :=
    (P.linearIndependent_iff_coxeterWeightIn_ne_four ℤ).mp (b.linearIndependent_pair_of_ne hij)
  have hmem := P.coxeterWeightIn_mem_set_of_isCrystallographic (i : ι) (j : ι)
  rw [cartanMatrix_mul_cartanMatrix_eq_coxeterWeightIn]
  simp only [mem_insert_iff, mem_singleton_iff] at hmem ⊢
  tauto

/-- The Cartan product of two distinct simple roots is `1` exactly when both Cartan entries are
`-1`, that is, exactly when the two simple roots are joined by a single edge. Off the diagonal the
entries are nonpositive, so the alternative factorisation `1 * 1` cannot occur. -/
lemma cartanMatrix_mul_cartanMatrix_eq_one_iff {i j : b.support} (hij : i ≠ j) :
    b.cartanMatrix i j * b.cartanMatrix j i = 1 ↔
      b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -1 := by
  have hi := b.cartanMatrix_le_zero_of_ne i j hij
  rw [Int.mul_eq_one_iff_eq_one_or_neg_one]
  refine ⟨fun h ↦ ?_, Or.inr⟩
  rcases h with ⟨h, -⟩ | h
  · omega
  · exact h

end CartanProduct

/-! ## The Coxeter matrix of a base -/

section CoxeterMatrixOfBase

variable [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic] (b : P.Base)

/-- **The Coxeter matrix of a base.** Its entry at a pair of distinct simple roots records the order
of the product of the two corresponding simple reflections, read off their Cartan product by
`0 ↦ 2`, `1 ↦ 3`, `2 ↦ 4`, `3 ↦ 6`; its diagonal entries are `1` because a simple root has Cartan
product `4` with itself.

That the entries really are those orders is the classical rank-two computation, and follows in
general from the Coxeter presentation of the Weyl group, which is not built here; the entry `2` is
checked directly in
`TauCeti.RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_two_of_coxeterMatrixOfBase_eq_two`.

The body is not exposed: `TauCeti.coxeterMatrixOfBase_apply` is the entry API. -/
noncomputable def coxeterMatrixOfBase : CoxeterMatrix b.support :=
  coxeterMatrixOfCartanMatrix b.cartanMatrix b.cartanMatrix_apply_same
    fun _ _ hij ↦ cartanMatrix_mul_cartanMatrix_mem_of_ne P b hij

/-- The entry of the Coxeter matrix of a base at a pair of simple roots is `coxeterOrder` applied
to the product of the two Cartan entries. -/
@[simp]
lemma coxeterMatrixOfBase_apply (i j : b.support) :
    coxeterMatrixOfBase P b i j = coxeterOrder (b.cartanMatrix i j * b.cartanMatrix j i) :=
  coxeterMatrixOfCartanMatrix_apply ..

/-- Off the diagonal the Coxeter matrix of a base takes only the four dihedral values. -/
lemma coxeterMatrixOfBase_mem_of_ne {i j : b.support} (hij : i ≠ j) :
    coxeterMatrixOfBase P b i j ∈ ({2, 3, 4, 6} : Set ℕ) :=
  coxeterOrder_mem (cartanMatrix_mul_cartanMatrix_mem_of_ne P b hij)

/-- No entry of the Coxeter matrix of a base is infinite: no pair of simple roots of a finite
crystallographic root pairing generates an infinite dihedral group. -/
lemma coxeterMatrixOfBase_ne_zero (i j : b.support) : coxeterMatrixOfBase P b i j ≠ 0 := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · have := coxeterMatrixOfBase_mem_of_ne P b hij
    simp only [mem_insert_iff, mem_singleton_iff] at this
    omega

/-- Every entry of the Coxeter matrix of a base is at most `6`, the order attained by the `G₂`
configuration. -/
lemma coxeterMatrixOfBase_le_six (i j : b.support) : coxeterMatrixOfBase P b i j ≤ 6 := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · exact coxeterOrder_le_six (cartanMatrix_mul_cartanMatrix_mem_of_ne P b hij)

/-- **Two simple roots carry the Coxeter entry `2` exactly when they are orthogonal.** On the
diagonal both sides fail: the entry there is `1`, and no root is orthogonal to itself. -/
theorem coxeterMatrixOfBase_eq_two_iff (i j : b.support) :
    coxeterMatrixOfBase P b i j = 2 ↔ P.IsOrthogonal (i : ι) (j : ι) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [← cartanMatrix_mul_cartanMatrix_eq_zero_iff_isOrthogonal P b]
    simp
  · rw [coxeterMatrixOfBase_apply,
      coxeterOrder_eq_two_iff (cartanMatrix_mul_cartanMatrix_mem_of_ne P b hij),
      cartanMatrix_mul_cartanMatrix_eq_zero_iff_isOrthogonal]

/-- **The Cartan matrix of a base is simply laced exactly when the Coxeter matrix of that base has
all entries at most `3`**, that is, exactly when no two simple roots are joined by a multiple
edge. -/
theorem isSimplyLaced_iff_forall_coxeterMatrixOfBase_le_three :
    b.cartanMatrix.IsSimplyLaced ↔ ∀ i j, coxeterMatrixOfBase P b i j ≤ 3 := by
  constructor
  · intro h i j
    rcases eq_or_ne i j with rfl | hij
    · simp
    · rw [coxeterMatrixOfBase_apply,
        coxeterOrder_le_three_iff (cartanMatrix_mul_cartanMatrix_mem_of_ne P b hij)]
      rcases h hij with h₁ | h₁ <;> rcases h hij.symm with h₂ | h₂ <;> rw [h₁, h₂] <;> norm_num
  · intro h i j hij
    rcases (coxeterOrder_le_three_iff (cartanMatrix_mul_cartanMatrix_mem_of_ne P b hij)).mp
      (by simpa using h i j) with h₀ | h₁
    · exact Or.inl ((cartanMatrix_mul_cartanMatrix_eq_zero_iff P b i j).mp h₀)
    · exact Or.inr ((cartanMatrix_mul_cartanMatrix_eq_one_iff P b hij).mp h₁).1

end CoxeterMatrixOfBase

/-! ## The Coxeter entries of the three rank-two Cartan types -/

section CartanType

variable [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic] (b : P.Base)

/-- A base of type `A₂` has Coxeter entry `3`: the two simple reflections have a product of
order `3`. -/
theorem coxeterMatrixOfBase_eq_three_of_hasCartanType_A_two (h : HasCartanType P b (.A 2))
    {i j : b.support} (hij : i ≠ j) : coxeterMatrixOfBase P b i j = 3 := by
  obtain ⟨e, he⟩ : ∃ e : b.support ≃ Fin 2, ∀ i j,
      b.cartanMatrix i j = (!![2, -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℤ) (e i) (e j) := by
    obtain ⟨e, he⟩ := (hasCartanType_iff b (.A 2)).mp h
    exact ⟨e, fun i j ↦ by rw [he i j, DynkinType.cartanMatrix_A_two_eq]; rfl⟩
  have hval : b.cartanMatrix i j * b.cartanMatrix j i = 1 :=
    (Matrix.mul_apply_mul_apply_eq_of_equiv_fin_two e he hij).trans (by decide)
  rw [coxeterMatrixOfBase_apply, hval, coxeterOrder_one]

/-- A base of type `B₂` has Coxeter entry `4`. -/
theorem coxeterMatrixOfBase_eq_four_of_hasCartanType_B_two (h : HasCartanType P b (.B 2))
    {i j : b.support} (hij : i ≠ j) : coxeterMatrixOfBase P b i j = 4 := by
  obtain ⟨e, he⟩ : ∃ e : b.support ≃ Fin 2, ∀ i j,
      b.cartanMatrix i j = (!![2, -2; -1, 2] : Matrix (Fin 2) (Fin 2) ℤ) (e i) (e j) := by
    obtain ⟨e, he⟩ := (hasCartanType_iff b (.B 2)).mp h
    exact ⟨e, fun i j ↦ by rw [he i j, DynkinType.cartanMatrix_B_two_eq]; rfl⟩
  have hval : b.cartanMatrix i j * b.cartanMatrix j i = 2 :=
    (Matrix.mul_apply_mul_apply_eq_of_equiv_fin_two e he hij).trans (by decide)
  rw [coxeterMatrixOfBase_apply, hval, coxeterOrder_two]

/-- A base of type `G₂` has Coxeter entry `6`: the two simple reflections have a product of
order `6`, the rotation by a sixth of a turn of the `G₂` hexagon. -/
theorem coxeterMatrixOfBase_eq_six_of_hasCartanType_G2 (h : HasCartanType P b .G2)
    {i j : b.support} (hij : i ≠ j) : coxeterMatrixOfBase P b i j = 6 := by
  obtain ⟨e, he⟩ : ∃ e : b.support ≃ Fin 2, ∀ i j,
      b.cartanMatrix i j = (!![2, -1; -3, 2] : Matrix (Fin 2) (Fin 2) ℤ) (e i) (e j) := by
    obtain ⟨e, he⟩ := (hasCartanType_iff b .G2).mp h
    exact ⟨e, fun i j ↦ by rw [he i j, DynkinType.cartanMatrix_G2_eq]; rfl⟩
  have hval : b.cartanMatrix i j * b.cartanMatrix j i = 3 :=
    (Matrix.mul_apply_mul_apply_eq_of_equiv_fin_two e he hij).trans (by decide)
  rw [coxeterMatrixOfBase_apply, hval, coxeterOrder_three]

end CartanType

/-! ## The orthogonal case: commuting simple reflections -/

namespace RootPairing.weylGroup

variable [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic]

/-- **Where the Coxeter matrix of a base has the entry `2`, the product of the two simple
reflections does have order `2`.** This is the one entry of `coxeterMatrixOfBase` that can be
checked before the Coxeter presentation of the Weyl group is available. -/
theorem orderOf_ofIdx_mul_ofIdx_eq_two_of_coxeterMatrixOfBase_eq_two
    (b : P.Base) {i j : b.support} (h : coxeterMatrixOfBase P b i j = 2) :
    orderOf (_root_.RootPairing.weylGroup.ofIdx P (i : ι) *
      _root_.RootPairing.weylGroup.ofIdx P (j : ι)) = 2 := by
  have hij : i ≠ j := by rintro rfl; simp at h
  have hij' : (i : ι) ≠ (j : ι) := fun h ↦ hij (Subtype.ext h)
  have hcomm := commute_ofIdx_of_isOrthogonal P ((coxeterMatrixOfBase_eq_two_iff P b i j).mp h)
  refine orderOf_eq_prime ?_ ?_
  · rw [hcomm.mul_pow, sq, sq, ofIdx_mul_self, ofIdx_mul_self, mul_one]
  · rw [Ne, mul_eq_one_iff_eq_inv, inv_eq_of_mul_eq_one_right (ofIdx_mul_self P (j : ι))]
    exact ofIdx_ne_ofIdx_of_ne P b i.property j.property hij'

end RootPairing.weylGroup

end TauCeti
