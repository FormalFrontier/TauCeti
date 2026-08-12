/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Matrix
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin

public section

/-!
# The Coxeter matrix of a Dynkin type

`TauCeti.coxeterMatrixOfBase` reads a Coxeter matrix off the Cartan matrix of a base, entry by
entry: the order of the product of two simple reflections is the Cartan product of the two simple
roots, translated by `0 ↦ 2`, `1 ↦ 3`, `2 ↦ 4`, `3 ↦ 6`. This file performs that translation on
the standard Cartan matrices of `TauCeti.DynkinType`, so that a base matched to a Dynkin type
carries a *named* Coxeter matrix, and identifies the outcome with the finite-type Coxeter matrices
`CoxeterMatrix.A`, `.B`, `.E₆`, `.E₇`, `.E₈`, `.F₄` and `.G₂` that Mathlib already pins.

The identifications are worth spelling out one type at a time because they are the acceptance
criteria of the classification: the Weyl group of a root system of type `Aₙ` is a Coxeter group on
`CoxeterMatrix.A n` and on no other matrix. The `Bₙ`/`Cₙ` pair collapses here: transposing a Cartan
matrix leaves every Cartan product fixed, so the two types, which are distinct root systems with
transposed Cartan matrices, share the single Coxeter matrix `CoxeterMatrix.B n`. That collapse is
exactly the information the Coxeter matrix drops — it records the diagram and its edge
multiplicities, but not the direction of a multiple edge.

Type `Dₙ` is the one type not matched to a Mathlib matrix, because `CoxeterMatrix.D n` is not the
Coxeter matrix of type `Dₙ`: alongside the fork edge between the nodes `n - 3` and `n - 1` it keeps
the chain edge between the two fork nodes `n - 2` and `n - 1`, so its diagram carries `n` edges on
`n` nodes and contains a triangle, while a Dynkin diagram is a tree.
`TauCeti.DynkinType.coxeterMatrix_D_apply` describes the type `Dₙ` entries directly instead, and
`TauCeti.DynkinType.coxeterMatrix_D_ne_coxeterMatrixD` records the difference.

## Main definitions

* `TauCeti.DynkinType.coxeterMatrix`: the standard Coxeter matrix of a Dynkin type, in the same
  Bourbaki node numbering as `TauCeti.DynkinType.cartanMatrix`.

## Main results

* `TauCeti.DynkinType.cartanMatrix_mul_cartanMatrix_mem_of_ne`: the Cartan product of two distinct
  nodes of a standard Cartan matrix lies in `{0, 1, 2, 3}`, each standard matrix being of finite
  type. This is what makes the Coxeter matrix above well defined.
* `TauCeti.DynkinType.coxeterMatrix_apply_of_isSimplyLaced`: on a simply-laced type the Coxeter
  entry is `2` at an orthogonal pair of nodes and `3` at an adjacent one, so the Coxeter matrix is
  the diagram itself.
* `TauCeti.DynkinType.coxeterMatrix_A`, `_B`, `_C`, `_E6`, `_E7`, `_E8`, `_F4`, `_G2`: the standard
  Coxeter matrix of each type, identified with Mathlib's, together with
  `TauCeti.DynkinType.coxeterMatrix_D_apply` for type `Dₙ`.
* `TauCeti.HasCartanType.exists_coxeterMatrixOfBase_eq`: **the Coxeter matrix of a base of Cartan
  type `t` is the standard Coxeter matrix of `t`**, after the same relabelling of the simple roots
  by the Bourbaki nodes. Its corollaries
  `TauCeti.HasCartanType.exists_coxeterMatrixOfBase_eq_A` and
  `TauCeti.HasCartanType.exists_coxeterMatrixOfBase_eq_G2` are the two the roadmap names.

## References

This file supplies the clause "recovering `CoxeterMatrix.A n` as `coxeterMatrixOfBase b`" of the
`Aₙ` worked example, and its `G₂` counterpart, in
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, bridging the `coxeterMatrixOfBase` of
Layer 2 and the `DynkinType` enumeration of Layer 5. The translation of a Cartan product into a
Coxeter order is Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI, §1.3, and
Humphreys, *Introduction to Lie Algebras and Representation Theory*, §9.4 and §11.4.
-/

open scoped Matrix

namespace TauCeti

namespace DynkinType

/-! ## The Cartan products of a standard Cartan matrix -/

/-- **The Cartan product of two distinct nodes of a Dynkin type lies in `{0, 1, 2, 3}`**, the four
values that name the orders `2, 3, 4, 6` of a product of two simple reflections. Validity of the
type is not needed: the degenerate members of the families are of finite type as well, and the
bound is the finite-type bound `TauCeti.IsFiniteType.apply_mul_apply_mem_of_ne`. -/
lemma cartanMatrix_mul_cartanMatrix_mem_of_ne (t : DynkinType) {i j : Fin t.rank} (hij : i ≠ j) :
    t.cartanMatrix i j * t.cartanMatrix j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
  cases t
  -- The classical families are of finite type as Mathlib's matrices; expose the reduction of the
  -- dependent index `Fin t.rank` to `Fin n` before rewriting to them.
  case A n =>
    change Fin n at i j
    simpa using (isFiniteType_cartanMatrix_A n).apply_mul_apply_mem_of_ne hij
  case B n =>
    change Fin n at i j
    simpa using (isFiniteType_cartanMatrix_B n).apply_mul_apply_mem_of_ne hij
  case C n =>
    change Fin n at i j
    simpa using (isFiniteType_cartanMatrix_C n).apply_mul_apply_mem_of_ne hij
  case D n =>
    change Fin n at i j
    simpa using (isFiniteType_cartanMatrix_D n).apply_mul_apply_mem_of_ne hij
  case E6 => exact isFiniteType_cartanMatrix_E6.apply_mul_apply_mem_of_ne hij
  case E7 => exact isFiniteType_cartanMatrix_E7.apply_mul_apply_mem_of_ne hij
  case E8 => exact isFiniteType_cartanMatrix_E8.apply_mul_apply_mem_of_ne hij
  case F4 => exact isFiniteType_cartanMatrix_F4.apply_mul_apply_mem_of_ne hij
  case G2 => exact isFiniteType_cartanMatrix_G2.apply_mul_apply_mem_of_ne hij

/-! ## The Coxeter matrix of a type -/

/-- **The standard Coxeter matrix of a Dynkin type**, indexed by `Fin t.rank` in the Bourbaki node
numbering of `TauCeti.DynkinType.cartanMatrix`: the entry at a pair of nodes is
`TauCeti.coxeterOrder` applied to their Cartan product, which is the order of the product of the two
simple reflections in the Weyl group of a root system of that type.

The body is not exposed: `TauCeti.DynkinType.coxeterMatrix_apply` is the entry API. -/
def coxeterMatrix (t : DynkinType) : CoxeterMatrix (Fin t.rank) where
  M := .of fun i j ↦ coxeterOrder (t.cartanMatrix i j * t.cartanMatrix j i)
  isSymm := by
    ext i j
    simp [Matrix.transpose_apply, mul_comm]
  diagonal i := by simp
  off_diagonal i j hij := by
    have := two_le_coxeterOrder (t.cartanMatrix_mul_cartanMatrix_mem_of_ne hij)
    simp only [Matrix.of_apply]
    omega

-- `(rfl)`, not `rfl`: the body of `coxeterMatrix` is deliberately left unexposed, and the
-- parenthesised form keeps this proof out of the exported definitional-equality check.
/-- The entry of the standard Coxeter matrix of a type at a pair of nodes is `TauCeti.coxeterOrder`
applied to the product of the two Cartan entries. -/
@[simp]
lemma coxeterMatrix_apply (t : DynkinType) (i j : Fin t.rank) :
    t.coxeterMatrix i j = coxeterOrder (t.cartanMatrix i j * t.cartanMatrix j i) := (rfl)

/-- The diagonal entries of a standard Coxeter matrix are `1`. -/
lemma coxeterMatrix_apply_self (t : DynkinType) (i : Fin t.rank) : t.coxeterMatrix i i = 1 :=
  t.coxeterMatrix.diagonal i

/-- **Two nodes carry the Coxeter entry `2` exactly when they are not joined**: the two simple
reflections commute exactly when the two simple roots are orthogonal. -/
lemma coxeterMatrix_apply_eq_two_iff (t : DynkinType) {i j : Fin t.rank} (hij : i ≠ j) :
    t.coxeterMatrix i j = 2 ↔ t.cartanMatrix i j = 0 := by
  rw [coxeterMatrix_apply,
    coxeterOrder_eq_two_iff (t.cartanMatrix_mul_cartanMatrix_mem_of_ne hij), mul_eq_zero]
  exact or_iff_left_iff_imp.mpr fun h ↦ (t.cartanMatrix_apply_eq_zero_iff_symm i j).mpr h

/-- **On a simply-laced type the Coxeter matrix is the diagram**: distinct nodes carry the entry `2`
when they are not joined and `3` when they are, there being no multiple edge to raise an entry to
`4` or `6`. -/
lemma coxeterMatrix_apply_of_isSimplyLaced {t : DynkinType} (ht : t.cartanMatrix.IsSimplyLaced)
    {i j : Fin t.rank} (hij : i ≠ j) :
    t.coxeterMatrix i j = if t.cartanMatrix i j = 0 then 2 else 3 := by
  rcases eq_or_ne (t.cartanMatrix i j) 0 with h | h
  · rw [ite_eq_left h]
    exact (t.coxeterMatrix_apply_eq_two_iff hij).mpr h
  · rw [ite_eq_right h, coxeterMatrix_apply, (ht hij).resolve_left h,
      (ht hij.symm).resolve_left fun hc ↦ h ((t.cartanMatrix_apply_eq_zero_iff_symm i j).mpr hc)]
    norm_num

/-- A simply-laced type has the Coxeter matrix its diagram prescribes, entry by entry. This is the
form in which the simply-laced identifications below are checked. -/
private lemma coxeterMatrix_eq_of_isSimplyLaced {t : DynkinType}
    (ht : t.cartanMatrix.IsSimplyLaced) {M : CoxeterMatrix (Fin t.rank)}
    (h : ∀ i j, (if i = j then 1 else if t.cartanMatrix i j = 0 then 2 else 3) = M i j) :
    t.coxeterMatrix = M := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · rw [coxeterMatrix_apply_self, ← h i i]
    simp
  · rw [coxeterMatrix_apply_of_isSimplyLaced ht hij, ← h i j, ite_eq_right hij]

/-! ## The Coxeter matrix of each type -/

/-- The Coxeter entry of a pair of nodes of type `Aₙ`: `3` along the chain and `2` off it. -/
private lemma coxeterOrder_cartanMatrix_A (n : ℕ) (i j : Fin n) :
    coxeterOrder (CartanMatrix.A n i j * CartanMatrix.A n j i) = CoxeterMatrix.A n i j := by
  simp only [CartanMatrix.A, CoxeterMatrix.A, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- **Type `Aₙ` has Coxeter matrix `CoxeterMatrix.A n`**, the chain of `n` nodes with every edge
labelled `3`: its Weyl group is the Coxeter group of the regular `n`-simplex. -/
@[simp] theorem coxeterMatrix_A (n : ℕ) : (A n).coxeterMatrix = CoxeterMatrix.A n := by
  ext i j
  simp only [coxeterMatrix_apply, cartanMatrix_A]
  exact coxeterOrder_cartanMatrix_A n i j

/-- The Coxeter entry of a pair of nodes of type `Bₙ`. The double edge, at the two last nodes, is
the one entry `4`; every other edge of the chain has entry `3`.

Stated for Mathlib's `CartanMatrix.B` rather than for `TauCeti.DynkinType.cartanMatrix`, so that
type `Cₙ`, whose standard Cartan matrix is the transpose, can consume it as well. -/
private lemma coxeterOrder_cartanMatrix_B (n : ℕ) (i j : Fin n) :
    coxeterOrder (CartanMatrix.B n i j * CartanMatrix.B n j i) = CoxeterMatrix.B n i j := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [CartanMatrix.B, CoxeterMatrix.B, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- **Type `Bₙ` has Coxeter matrix `CoxeterMatrix.B n`**, the chain of `n` nodes whose last edge is
labelled `4`: its Weyl group is the Coxeter group of the `n`-hypercube. -/
@[simp] theorem coxeterMatrix_B (n : ℕ) : (B n).coxeterMatrix = CoxeterMatrix.B n := by
  ext i j
  simp only [coxeterMatrix_apply, cartanMatrix_B]
  exact coxeterOrder_cartanMatrix_B n i j

/-- **Type `Cₙ` has the same Coxeter matrix as type `Bₙ`.** The two standard Cartan matrices are
transposes of one another, and a Cartan product is invariant under transposition, so the Coxeter
matrix cannot separate them: it records the double edge but not its direction. The two types are
nonetheless distinct root systems, dual to one another. -/
@[simp] theorem coxeterMatrix_C (n : ℕ) : (C n).coxeterMatrix = CoxeterMatrix.B n := by
  have hC : CartanMatrix.C n = (CartanMatrix.B n)ᵀ := (CartanMatrix.B_transpose n).symm
  ext i j
  simp only [coxeterMatrix_apply, cartanMatrix_C, hC]
  rw [mul_comm]
  exact coxeterOrder_cartanMatrix_B n i j

/-- The two fork nodes of type `Dₙ` are not joined: the Cartan entry between the nodes `n - 2` and
`n - 1` vanishes, both of them being joined instead to the branch node `n - 3`. -/
private lemma cartanMatrix_D_apply_fork {n : ℕ} (hn : 4 ≤ n) {i j : Fin n}
    (hi : (i : ℕ) = n - 2) (hj : (j : ℕ) = n - 1) : CartanMatrix.D n i j = 0 := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, hi, hj]
  split_ifs <;> omega

/-- Mathlib's `CoxeterMatrix.D n` labels the pair of fork nodes `n - 2`, `n - 1` with a `3`, that
pair being consecutive. -/
private lemma coxeterMatrixD_apply_fork {n : ℕ} (hn : 4 ≤ n) {i j : Fin n}
    (hi : (i : ℕ) = n - 2) (hj : (j : ℕ) = n - 1) : CoxeterMatrix.D n i j = 3 := by
  simp only [CoxeterMatrix.D, Matrix.of_apply, Fin.ext_iff, hi, hj]
  split_ifs <;> omega

/-- **The Coxeter entries of type `Dₙ`**: `3` between two nodes joined in the diagram and `2`
between two nodes that are not, type `Dₙ` being simply laced.

Mathlib's `CoxeterMatrix.D n` is not this matrix; see
`TauCeti.DynkinType.coxeterMatrix_D_ne_coxeterMatrixD`. -/
theorem coxeterMatrix_D_apply (n : ℕ) {i j : Fin (D n).rank} (hij : i ≠ j) :
    (D n).coxeterMatrix i j = if CartanMatrix.D n i j = 0 then 2 else 3 := by
  rw [coxeterMatrix_apply_of_isSimplyLaced (by simpa using CartanMatrix.isSimplyLaced_D n) hij,
    cartanMatrix_D]

/-- **Mathlib's `CoxeterMatrix.D n` is not the Coxeter matrix of type `Dₙ`.** On top of the fork
edge it adds between the nodes `n - 3` and `n - 1`, it labels the pair `n - 2`, `n - 1` of fork
nodes with a `3` as well, that pair being consecutive; the resulting diagram has `n` edges on `n`
nodes, so it is not a tree, while the diagram of `Dₙ` is. The two matrices differ at exactly that
pair of nodes, where the Cartan entry of type `Dₙ` vanishes. -/
theorem coxeterMatrix_D_ne_coxeterMatrixD {n : ℕ} (hn : 4 ≤ n) :
    (D n).coxeterMatrix ≠ CoxeterMatrix.D n := by
  intro hcontra
  have h2 : n - 2 < (D n).rank := by simp only [rank_D]; omega
  have h1 : n - 1 < (D n).rank := by simp only [rank_D]; omega
  have hij : (⟨n - 2, h2⟩ : Fin (D n).rank) ≠ ⟨n - 1, h1⟩ := by
    simp only [ne_eq, Fin.mk.injEq]
    omega
  have hzero : CartanMatrix.D n (⟨n - 2, h2⟩ : Fin (D n).rank) ⟨n - 1, h1⟩ = 0 :=
    cartanMatrix_D_apply_fork hn rfl rfl
  have hleft : (D n).coxeterMatrix ⟨n - 2, h2⟩ ⟨n - 1, h1⟩ = 2 :=
    (coxeterMatrix_D_apply n hij).trans (ite_eq_left hzero)
  have hright : CoxeterMatrix.D n (⟨n - 2, h2⟩ : Fin (D n).rank) ⟨n - 1, h1⟩ = 3 :=
    coxeterMatrixD_apply_fork hn rfl rfl
  have key : (D n).coxeterMatrix ⟨n - 2, h2⟩ ⟨n - 1, h1⟩
      = CoxeterMatrix.D n (⟨n - 2, h2⟩ : Fin (D n).rank) ⟨n - 1, h1⟩ :=
    congrFun₂ (congrArg CoxeterMatrix.M hcontra) _ _
  rw [hleft, hright] at key
  omega

/-- **Type `E₆` has Coxeter matrix `CoxeterMatrix.E₆`.** -/
@[simp] theorem coxeterMatrix_E6 : E6.coxeterMatrix = CoxeterMatrix.E₆ := by
  refine coxeterMatrix_eq_of_isSimplyLaced (by simpa using CartanMatrix.isSimplyLaced_E₆) ?_
  simp only [cartanMatrix_E6]
  intro i j
  fin_cases i <;> fin_cases j <;> decide

/-- **Type `E₇` has Coxeter matrix `CoxeterMatrix.E₇`.** -/
@[simp] theorem coxeterMatrix_E7 : E7.coxeterMatrix = CoxeterMatrix.E₇ := by
  refine coxeterMatrix_eq_of_isSimplyLaced (by simpa using CartanMatrix.isSimplyLaced_E₇) ?_
  simp only [cartanMatrix_E7]
  intro i j
  fin_cases i <;> fin_cases j <;> decide

/-- **Type `E₈` has Coxeter matrix `CoxeterMatrix.E₈`.** -/
@[simp] theorem coxeterMatrix_E8 : E8.coxeterMatrix = CoxeterMatrix.E₈ := by
  refine coxeterMatrix_eq_of_isSimplyLaced (by simpa using CartanMatrix.isSimplyLaced_E₈) ?_
  simp only [cartanMatrix_E8]
  intro i j
  fin_cases i <;> fin_cases j <;> decide

/-- The five values a Cartan product can take, paired with the Coxeter order it names. This is the
form in which the two multiply-laced exceptional types are checked, `TauCeti.coxeterOrder` itself
having no `Decidable` instance to hand a decision procedure. -/
private lemma coxeterOrder_eq_of_pair {c : ℤ} {m : ℕ}
    (h : c = 0 ∧ m = 2 ∨ c = 1 ∧ m = 3 ∨ c = 2 ∧ m = 4 ∨ c = 3 ∧ m = 6 ∨ c = 4 ∧ m = 1) :
    coxeterOrder c = m := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- **Type `F₄` has Coxeter matrix `CoxeterMatrix.F₄`**, the chain of four nodes with the middle
edge labelled `4`: its Weyl group is the Coxeter group of the 24-cell. -/
@[simp] theorem coxeterMatrix_F4 : F4.coxeterMatrix = CoxeterMatrix.F₄ := by
  ext i j
  simp only [coxeterMatrix_apply, cartanMatrix_F4]
  refine coxeterOrder_eq_of_pair ?_
  fin_cases i <;> fin_cases j <;> decide

/-- **Type `G₂` has Coxeter matrix `CoxeterMatrix.G₂`**, the single edge labelled `6`: its Weyl
group is the Coxeter group of the regular hexagon. The standard Cartan matrix of `G₂` is the
transpose of Mathlib's, a difference the Cartan product does not see. -/
@[simp] theorem coxeterMatrix_G2 : G2.coxeterMatrix = CoxeterMatrix.G₂ := by
  ext i j
  simp only [coxeterMatrix_apply, cartanMatrix_G2]
  refine coxeterOrder_eq_of_pair ?_
  fin_cases i <;> fin_cases j <;> decide

end DynkinType

/-! ## The Coxeter matrix of a base of a given Cartan type -/

section RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic]
  {b : P.Base} {t : DynkinType}

/-- **The Coxeter matrix of a base of Cartan type `t` is the standard Coxeter matrix of `t`**, under
the very relabelling of the simple roots by the Bourbaki nodes that matches the two Cartan matrices.

This is what makes the Coxeter presentation of a Weyl group a presentation on a *named* matrix:
combined with the identifications above, a base of type `Aₙ` carries `CoxeterMatrix.A n`, one of
type `Bₙ` or `Cₙ` carries `CoxeterMatrix.B n`, and so on. -/
theorem HasCartanType.exists_coxeterMatrixOfBase_eq (h : HasCartanType P b t) :
    ∃ e : b.support ≃ Fin t.rank, coxeterMatrixOfBase P b = t.coxeterMatrix.reindex e.symm := by
  obtain ⟨e, he⟩ := (hasCartanType_iff b t).mp h
  refine ⟨e, ?_⟩
  ext i j
  rw [coxeterMatrixOfBase_apply, CoxeterMatrix.reindex_apply, Equiv.symm_symm,
    DynkinType.coxeterMatrix_apply, he i j, he j i]

/-- **A base of type `Aₙ` carries the Coxeter matrix `CoxeterMatrix.A n`**, so that its Weyl group
is presented on the Coxeter matrix of the regular `n`-simplex, with the simple reflections as the
Coxeter generators. -/
theorem HasCartanType.exists_coxeterMatrixOfBase_eq_A {n : ℕ} (h : HasCartanType P b (.A n)) :
    ∃ e : b.support ≃ Fin n, coxeterMatrixOfBase P b = (CoxeterMatrix.A n).reindex e.symm := by
  obtain ⟨e, he⟩ := h.exists_coxeterMatrixOfBase_eq
  exact ⟨e, by rwa [DynkinType.coxeterMatrix_A] at he⟩

/-- **A base of type `G₂` carries the Coxeter matrix `CoxeterMatrix.G₂`**, the single edge labelled
`6`. -/
theorem HasCartanType.exists_coxeterMatrixOfBase_eq_G2 (h : HasCartanType P b .G2) :
    ∃ e : b.support ≃ Fin 2, coxeterMatrixOfBase P b = CoxeterMatrix.G₂.reindex e.symm := by
  obtain ⟨e, he⟩ := h.exists_coxeterMatrixOfBase_eq
  exact ⟨e, by rwa [DynkinType.coxeterMatrix_G2] at he⟩

end RootPairing

end TauCeti
