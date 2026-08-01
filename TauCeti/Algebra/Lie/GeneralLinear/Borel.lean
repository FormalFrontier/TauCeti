/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.RootSpace
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The standard Borel subalgebra of `gl n R` and its positive nilpotent ideal

Order the index type `n` linearly. The upper triangular matrices form a Lie subalgebra
`TauCeti.upperTriangular R n` of `gl n R = Matrix n n R`, and the strictly upper triangular
matrices form a Lie subalgebra `TauCeti.strictUpperTriangular R n` inside it. This is the *matrix
unit positive system* of `gl n R`: the raising operators are the matrix units `Eᵢⱼ` with `i < j`,
and `strictUpperTriangular R n` is the span of those. Over a domain away from characteristic two,
that span is the sum of the root spaces of the positive roots `εᵢ - εⱼ`, `i < j`, for the diagonal
Cartan subalgebra `TauCeti.diagonalCartan R n`; without those hypotheses the root spaces can be
larger (in characteristic two the root space of `εᵢ - εⱼ` also contains the lowering matrix unit
`Eⱼᵢ`), as explained in the implementation notes below.

The two subalgebras fit together in the usual way. The upper triangular matrices are the direct sum
of the diagonal ones and the strictly upper triangular ones
(`TauCeti.upperTriangular_toSubmodule_eq_sup` and
`TauCeti.disjoint_diagonalCartan_strictUpperTriangular`), which is the decomposition `𝔟 = 𝔥 ⊕ 𝔫⁺`.
The Borel subalgebra is self-normalizing (`TauCeti.upperTriangular_normalizer_eq_self`), and the
bracket of *any two* upper triangular matrices is already strictly upper triangular
(`TauCeti.lie_mem_strictUpperTriangular`), because the diagonal of a commutator of upper triangular
matrices is the commutator of the diagonals and `R` is commutative. In particular the strictly upper
triangular matrices are a Lie ideal of the Borel subalgebra,
`TauCeti.strictUpperTriangularIdeal`.

## Main definitions

* `TauCeti.upperTriangular R n`: the upper triangular matrices, as a
  `LieSubalgebra R (Matrix n n R)`. This is the standard Borel subalgebra of `gl n R`.
* `TauCeti.strictUpperTriangular R n`: the strictly upper triangular matrices, as a
  `LieSubalgebra R (Matrix n n R)`. This is the positive nilpotent ideal `𝔫⁺` of the standard
  Borel subalgebra.
* `TauCeti.strictUpperTriangularIdeal R n`: the same subalgebra, packaged as a Lie ideal of
  `upperTriangular R n`.

## Main results

* `TauCeti.mul_apply_diag_of_mem_upperTriangular`: the diagonal of a product of upper triangular
  matrices is the pointwise product of the diagonals.
* `TauCeti.lie_mem_strictUpperTriangular`: the bracket of two upper triangular matrices is strictly
  upper triangular.
* `TauCeti.upperTriangular_toSubmodule_eq_sup` and
  `TauCeti.disjoint_diagonalCartan_strictUpperTriangular`: the decomposition `𝔟 = 𝔥 ⊕ 𝔫⁺`.
* `TauCeti.upperTriangular_normalizer_eq_self`: the Borel subalgebra is self-normalizing.
* `TauCeti.strictUpperTriangular_toSubmodule_eq_iSup`: `𝔫⁺` is spanned by the matrix units `Eᵢⱼ`
  with `i < j`, and, over a domain away from characteristic two,
  `TauCeti.strictUpperTriangular_toSubmodule_eq_iSup_rootSpace` reads this as the sum of the root
  spaces of the positive roots.

## Implementation notes

`𝔫⁺` is called here the *positive nilpotent ideal* of the Borel subalgebra, never its nilradical:
for `gl n R` the two differ, because the scalar matrices are central in `gl n R` and so span a
further nilpotent ideal of `upperTriangular R n` outside `strictUpperTriangular R n`. For a
singleton index type this is the whole story: `upperTriangular R n` is then all of `gl n R`, which
is abelian and hence its own nilradical, while `strictUpperTriangular R n` is zero. It is in
`sl n R`, over a field whose characteristic does not divide the cardinality of `n`, that the strict
upper triangle is the nilradical of the Borel: only under such a hypothesis are the scalar matrices
really gone, since the trace of `r • 1` is `n • r`, so when the characteristic divides the
cardinality of `n` the nonzero scalar matrices are traceless and remain central in `sl n R`. What
makes `𝔫⁺` the right object here regardless is that it is the span of the raising matrix units
(`TauCeti.strictUpperTriangular_toSubmodule_eq_iSup`), which over a domain away from characteristic
two is the sum of the positive root spaces
(`TauCeti.strictUpperTriangular_toSubmodule_eq_iSup_rootSpace`), and which is what the highest
weight theory downstream uses.

The index type carries both `[DecidableEq n]`, for the matrix units, and `[LinearOrder n]`, which
is what "upper triangular" refers to; the two decidability structures are not identified, exactly as
in Mathlib's `Mathlib/LinearAlgebra/Matrix/Block.lean`. Upper triangularity is Mathlib's
`Matrix.BlockTriangular _ id`, and `TauCeti.upperTriangular` is literally Mathlib's associative
subalgebra `Matrix.blockTriangularSubalgebra` read as a Lie subalgebra along
`lieSubalgebraOfSubalgebra`. Strict upper triangularity is not a `Matrix.BlockTriangular` condition
for any block map, so `TauCeti.strictUpperTriangular` is spelled out. It is closed under the
associative product as well as under the bracket (that closure is the `key` step of its `lie_mem'`
field), and so is a nonunital associative subalgebra; but over a nontrivial `R` it does not contain
`1` unless `n` is empty (over the trivial ring `1 = 0` lies in it for every `n`), so it is not a
Mathlib `Subalgebra`, which is unital, and it cannot be read off one along
`lieSubalgebraOfSubalgebra` the way `TauCeti.upperTriangular` is.

Everything here holds over an arbitrary commutative ring. The single exception is
`TauCeti.strictUpperTriangular_toSubmodule_eq_iSup_rootSpace`, which identifies the individual
summands with root spaces and so inherits the `[IsDomain R]` and `(2 : R) ≠ 0` hypotheses of
`TauCeti.rootSpace_glWeightSub_eq_span`: in characteristic two `εᵢ - εⱼ = εⱼ - εᵢ`, so the root
space of a positive root also contains a lowering operator and is not contained in `𝔫⁺` at all.

As in `TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan`, none of Mathlib's
`LieAlgebra.IsKilling` machinery is available for `gl n R`, whose Killing form is degenerate; in
particular the positive system here is the matrix unit order rather than a
`LieAlgebra.IsKilling.rootSystem` base.

## References

This implements the matrix unit positive system of Layer 9 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, the standing convention that the
positive system of `gl n` is generated by the `Matrix.single i j 1` with `i < j`, which the
highest weight vectors of that layer are defined against.
-/

public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n] [LinearOrder n]

variable (R n)

/-- The upper triangular matrices, as a Lie subalgebra of `gl n R = Matrix n n R`.

This is the standard Borel subalgebra of `gl n R` attached to the matrix unit positive system: it
is the sum of the diagonal Cartan subalgebra and the span of the raising matrix units `Eᵢⱼ` with
`i < j`, which over a domain away from characteristic two is the sum of the root spaces of the
roots `εᵢ - εⱼ` with `i < j`. -/
def upperTriangular : LieSubalgebra R (Matrix n n R) :=
  lieSubalgebraOfSubalgebra R (Matrix n n R) (blockTriangularSubalgebra R R (id : n → n))

/-- The strictly upper triangular matrices, as a Lie subalgebra of `gl n R = Matrix n n R`.

This is the positive nilpotent ideal `𝔫⁺` of the standard Borel subalgebra
`TauCeti.upperTriangular R n`: it is the span of the raising matrix units `Eᵢⱼ` with `i < j`, with
no Cartan part, and over a domain away from characteristic two that is the sum of the root spaces
of the roots `εᵢ - εⱼ` with `i < j`. It is not the nilradical of `TauCeti.upperTriangular R n`,
which is in general larger; see the implementation notes of this file. -/
def strictUpperTriangular : LieSubalgebra R (Matrix n n R) where
  carrier := {A | ∀ i j, j ≤ i → A i j = 0}
  add_mem' hA hB := fun i j hij => by simp [hA i j hij, hB i j hij]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' c _ hA := fun i j hij => by simp [hA i j hij]
  lie_mem' {A B} hA hB := by
    intro i j hij
    have key : ∀ C D : Matrix n n R, (∀ i j, j ≤ i → C i j = 0) → (∀ i j, j ≤ i → D i j = 0) →
        (C * D) i j = 0 := by
      intro C D hC hD
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      rcases le_or_gt k i with hk | hk
      · rw [hC i k hk, zero_mul]
      · rw [hD k j (hij.trans hk.le), mul_zero]
    rw [LieRing.of_associative_ring_bracket, Matrix.sub_apply, key A B hA hB, key B A hB hA,
      sub_zero]

variable {R n}

/-- Membership in the Borel subalgebra is Mathlib's `Matrix.BlockTriangular` for the identity block
map. -/
theorem mem_upperTriangular_iff_blockTriangular {A : Matrix n n R} :
    A ∈ upperTriangular R n ↔ A.BlockTriangular id := Iff.rfl

/-- The entrywise description of the Borel subalgebra. -/
theorem mem_upperTriangular_iff {A : Matrix n n R} :
    A ∈ upperTriangular R n ↔ ∀ i j, j < i → A i j = 0 :=
  ⟨fun h _ _ hij => h hij, fun h _ _ hij => h _ _ hij⟩

/-- The entrywise description of `𝔫⁺`. -/
theorem mem_strictUpperTriangular_iff {A : Matrix n n R} :
    A ∈ strictUpperTriangular R n ↔ ∀ i j, j ≤ i → A i j = 0 := Iff.rfl

/-- A strictly upper triangular matrix has zero diagonal. -/
theorem diag_eq_zero_of_mem_strictUpperTriangular {A : Matrix n n R}
    (hA : A ∈ strictUpperTriangular R n) (i : n) : A i i = 0 :=
  hA i i le_rfl

/-- `𝔫⁺` is contained in the Borel subalgebra. -/
theorem strictUpperTriangular_le_upperTriangular :
    strictUpperTriangular R n ≤ upperTriangular R n :=
  fun _ hA _ _ hij => hA _ _ hij.le

/-- The diagonal Cartan subalgebra is contained in the Borel subalgebra. -/
theorem diagonalCartan_le_upperTriangular : diagonalCartan R n ≤ upperTriangular R n := by
  intro A hA
  rw [mem_upperTriangular_iff]
  exact fun i j hij => mem_diagonalCartan_iff.mp hA i j hij.ne'

/-! ### Matrix units -/

/-- The matrix unit `Eᵢⱼ` is upper triangular when `i ≤ j`. -/
theorem single_mem_upperTriangular {i j : n} (hij : i ≤ j) (c : R) :
    single i j c ∈ upperTriangular R n :=
  mem_upperTriangular_iff_blockTriangular.mpr
    (blockTriangular_single (b := (id : n → n)) hij c)

/-- The matrix unit `Eᵢⱼ` is strictly upper triangular when `i < j`; these are the raising
operators of the matrix unit positive system. -/
theorem single_mem_strictUpperTriangular {i j : n} (hij : i < j) (c : R) :
    single i j c ∈ strictUpperTriangular R n := by
  rw [mem_strictUpperTriangular_iff]
  intro a b hab
  rcases eq_or_ne i a with rfl | hia
  · rcases eq_or_ne j b with rfl | hjb
    · exact absurd hab hij.not_ge
    · simp [hjb]
  · simp [hia]

/-- A nonzero matrix unit `Eᵢⱼ` is upper triangular exactly when `i ≤ j`. -/
theorem single_mem_upperTriangular_iff {i j : n} {c : R} (hc : c ≠ 0) :
    single i j c ∈ upperTriangular R n ↔ i ≤ j := by
  refine ⟨fun h => ?_, fun h => single_mem_upperTriangular h c⟩
  by_contra hij
  rw [mem_upperTriangular_iff] at h
  exact hc (by simpa using h i j (not_le.mp hij))

/-- A nonzero matrix unit `Eᵢⱼ` is strictly upper triangular exactly when `i < j`. -/
theorem single_mem_strictUpperTriangular_iff {i j : n} {c : R} (hc : c ≠ 0) :
    single i j c ∈ strictUpperTriangular R n ↔ i < j := by
  refine ⟨fun h => ?_, fun h => single_mem_strictUpperTriangular h c⟩
  by_contra hij
  exact hc (by simpa using h i j (not_lt.mp hij))

/-! ### Products and brackets -/

/-- The diagonal of a product of upper triangular matrices is the pointwise product of the
diagonals: the only surviving term of `∑ k, A i k * B k i` is the one with `k = i`. -/
theorem mul_apply_diag_of_mem_upperTriangular {A B : Matrix n n R} (hA : A ∈ upperTriangular R n)
    (hB : B ∈ upperTriangular R n) (i : n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · exact fun h => absurd (Finset.mem_univ i) h

/-- **The bracket of two upper triangular matrices is strictly upper triangular.** Below the
diagonal both products vanish, and on the diagonal the two products agree, by
`TauCeti.mul_apply_diag_of_mem_upperTriangular` and commutativity of `R`. So the derived subalgebra
of the Borel subalgebra lies in `𝔫⁺`; in particular `𝔫⁺` is a Lie ideal of the Borel subalgebra,
`TauCeti.strictUpperTriangularIdeal`. -/
theorem lie_mem_strictUpperTriangular {A B : Matrix n n R} (hA : A ∈ upperTriangular R n)
    (hB : B ∈ upperTriangular R n) : ⁅A, B⁆ ∈ strictUpperTriangular R n := by
  intro i j hij
  rw [LieRing.of_associative_ring_bracket, Matrix.sub_apply]
  rcases hij.lt_or_eq with h | rfl
  · rw [hA.mul hB h, hB.mul hA h, sub_zero]
  · rw [mul_apply_diag_of_mem_upperTriangular hA hB,
      mul_apply_diag_of_mem_upperTriangular hB hA, mul_comm, sub_self]

variable (R n)

/-- The positive nilpotent ideal `𝔫⁺` of the standard Borel subalgebra of `gl n R`, as a Lie ideal
of that Borel subalgebra. Its underlying set is `TauCeti.strictUpperTriangular R n`. -/
def strictUpperTriangularIdeal : LieIdeal R (upperTriangular R n) where
  carrier := {A | (A : Matrix n n R) ∈ strictUpperTriangular R n}
  add_mem' hA hB := (strictUpperTriangular R n).add_mem hA hB
  zero_mem' := (strictUpperTriangular R n).zero_mem
  smul_mem' c _ hA := (strictUpperTriangular R n).smul_mem c hA
  lie_mem {A _B} hB :=
    lie_mem_strictUpperTriangular A.2 (strictUpperTriangular_le_upperTriangular hB)

variable {R n}

@[simp]
theorem mem_strictUpperTriangularIdeal_iff {A : upperTriangular R n} :
    A ∈ strictUpperTriangularIdeal R n ↔ (A : Matrix n n R) ∈ strictUpperTriangular R n :=
  Iff.rfl

/-! ### The decomposition `𝔟 = 𝔥 ⊕ 𝔫⁺` -/

/-- Subtracting its diagonal makes an upper triangular matrix strictly upper triangular. -/
theorem sub_diagonal_diag_mem_strictUpperTriangular {A : Matrix n n R}
    (hA : A ∈ upperTriangular R n) : A - diagonal A.diag ∈ strictUpperTriangular R n := by
  intro i j hij
  rcases hij.lt_or_eq with h | rfl
  · simp [hA h, diagonal_apply_ne' _ h.ne]
  · simp

/-- **The Borel subalgebra is the sum of the diagonal Cartan subalgebra and `𝔫⁺`**: every
upper triangular matrix is its diagonal plus a strictly upper triangular matrix. -/
theorem upperTriangular_toSubmodule_eq_sup :
    (upperTriangular R n).toSubmodule
      = (diagonalCartan R n).toSubmodule ⊔ (strictUpperTriangular R n).toSubmodule := by
  refine le_antisymm (fun A hA => ?_) (sup_le ?_ ?_)
  · rw [Submodule.mem_sup]
    exact ⟨diagonal A.diag, diagonal_mem_diagonalCartan _, A - diagonal A.diag,
      sub_diagonal_diag_mem_strictUpperTriangular hA, add_sub_cancel _ _⟩
  · exact diagonalCartan_le_upperTriangular
  · exact strictUpperTriangular_le_upperTriangular

/-- **The sum `𝔟 = 𝔥 ⊕ 𝔫⁺` is direct**: a diagonal matrix with zero diagonal is zero. -/
theorem disjoint_diagonalCartan_strictUpperTriangular :
    Disjoint (diagonalCartan R n).toSubmodule (strictUpperTriangular R n).toSubmodule := by
  rw [Submodule.disjoint_def]
  intro A hd hs
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simpa using diag_eq_zero_of_mem_strictUpperTriangular hs i
  · simpa using (mem_diagonalCartan_iff.mp hd) i j hij

/-! ### The Borel subalgebra is self-normalizing -/

variable (R n)

/-- **The standard Borel subalgebra of `gl n R` is self-normalizing.** If `X` normalizes the upper
triangular matrices then `⁅Eⱼⱼ, X⁆` is upper triangular for the diagonal matrix unit `Eⱼⱼ`, and
that bracket has `(i, j)` entry `-X i j` whenever `i ≠ j`; so `X i j` vanishes below the
diagonal. -/
@[simp]
theorem upperTriangular_normalizer_eq_self :
    (upperTriangular R n).normalizer = upperTriangular R n := by
  refine le_antisymm (fun X hX => mem_upperTriangular_iff.mpr fun i j hij => ?_)
    (upperTriangular R n).le_normalizer
  have hmem := diagonalCartan_le_upperTriangular (single_self_mem_diagonalCartan j (1 : R))
  have h := (LieSubalgebra.mem_normalizer_iff' _ X).mp hX _ hmem
  have hentry : ⁅single j j (1 : R), X⁆ i j = -X i j := by
    rw [lie_apply_of_mem_diagonalCartan (single_self_mem_diagonalCartan j 1)]
    simp [hij.ne]
  rw [mem_upperTriangular_iff] at h
  simpa [hentry] using h i j hij

/-! ### `𝔫⁺` as the span of the raising operators -/

/-- **`𝔫⁺` is spanned by the raising matrix units** `Eᵢⱼ`, `i < j`. -/
theorem strictUpperTriangular_toSubmodule_eq_iSup :
    (strictUpperTriangular R n).toSubmodule
      = ⨆ i : n, ⨆ j : n, ⨆ _ : i < j, R ∙ single i j (1 : R) := by
  refine le_antisymm (fun A hA => ?_) ?_
  · rw [Matrix.matrix_eq_sum_single A]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    rcases lt_or_ge i j with hij | hij
    · have hsmul : single i j (A i j) = A i j • single i j (1 : R) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hsmul]
      refine Submodule.smul_mem _ _ ?_
      have hle : (R ∙ single i j (1 : R))
          ≤ ⨆ i : n, ⨆ j : n, ⨆ _ : i < j, R ∙ single i j (1 : R) :=
        le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le hij le_rfl))
      exact hle (Submodule.mem_span_singleton_self _)
    · rw [mem_strictUpperTriangular_iff.mp hA i j hij, Matrix.single_zero]
      exact Submodule.zero_mem _
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact single_mem_strictUpperTriangular hij 1

/-- **`𝔫⁺` is the sum of the positive root spaces.** Over a domain, away from
characteristic two, the root space of `εᵢ - εⱼ` is the line spanned by `Eᵢⱼ`
(`TauCeti.rootSpace_glWeightSub_eq_span`), so
`TauCeti.strictUpperTriangular_toSubmodule_eq_iSup` says exactly that `𝔫⁺` is the sum of the root
spaces of the positive roots `εᵢ - εⱼ`, `i < j`. Both hypotheses are needed: in characteristic two
`εᵢ - εⱼ = εⱼ - εᵢ`, so that root space also contains the lowering operator `Eⱼᵢ`. -/
theorem strictUpperTriangular_toSubmodule_eq_iSup_rootSpace [IsDomain R] (h2 : (2 : R) ≠ 0) :
    (strictUpperTriangular R n).toSubmodule
      = ⨆ i : n, ⨆ j : n, ⨆ _ : i < j,
        (LieAlgebra.rootSpace (diagonalCartan R n) (glWeightSub R n i j)).toSubmodule := by
  rw [strictUpperTriangular_toSubmodule_eq_iSup]
  exact iSup_congr fun i => iSup_congr fun j => iSup_congr fun hij =>
    (rootSpace_glWeightSub_eq_span h2 hij.ne).symm

end TauCeti
