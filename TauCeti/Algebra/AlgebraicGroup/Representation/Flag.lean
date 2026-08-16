/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Basis.Flag
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
public import TauCeti.Algebra.Coalgebra.Subcomodule.Quotient
public import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# Flags of upper-unitriangular comodules

Let `M` be a finite free comodule with basis `b₀, ..., bₙ₋₁`. Its coefficient matrix is upper
unitriangular exactly when, for every `i`, the coaction of `bᵢ` is congruent to `bᵢ ⊗ 1` modulo
the span of the preceding basis vectors. Thus the standard basis flag is comodule-stable and its
successive one-dimensional factors are trivial.

This is the flag interface needed for the Kolchin induction in Layer 5, "Unipotent groups", of
the ReductiveGroups roadmap. Once that induction supplies successive fixed vectors, the criterion
here produces the upper-unitriangular coefficient matrix used to embed a faithful representation
into `Uₙ`.

## Main declarations

* `TauCeti.Comodule.coefficientMatrix_isUpperUnitriangular_iff`: the quotient-by-preceding-span
  criterion for an upper-unitriangular coefficient matrix.
* `TauCeti.Comodule.flagSubcomodule`: the standard flag of an upper-triangular comodule, bundled as
  subcomodules.
* `TauCeti.Comodule.quotient_mk_basis_ne_zero`: each successive basis class is nonzero in the
  quotient by the preceding flag term.
* `TauCeti.Comodule.quotientCoact_flagSubcomodule_mk_basis`: each successive basis class has
  trivial coaction in that quotient.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

open Module

universe u

noncomputable section

variable {k H M : Type u} {n : ℕ}
variable [CommRing k] [Semiring H] [Bialgebra k H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]

/-- A coefficient matrix is upper unitriangular exactly when each basis vector is fixed by the
coaction modulo the span of the preceding basis vectors. -/
theorem coefficientMatrix_isUpperUnitriangular_iff (b : Basis (Fin n) k M) :
    (coefficientMatrix (C := H) b).IsUpperUnitriangular ↔
      ∀ i : Fin n,
        TensorProduct.map (b.flag i.castSucc).mkQ (LinearMap.id : H →ₗ[k] H)
            (coact (C := H) (b i)) =
          Submodule.Quotient.mk (b i) ⊗ₜ[k] (1 : H) := by
  constructor
  · intro h i
    rw [coact_basis_eq_sum_coefficientMatrix, map_sum]
    classical
    rw [Finset.sum_eq_single i]
    · simp [h.apply_diag i]
    · intro j _ hji
      rcases lt_trichotomy j i with hji' | hji' | hij
      · rw [TensorProduct.map_tmul, LinearMap.id_apply]
        have hjflag : b j ∈ b.flag i.castSucc :=
          b.self_mem_flag (Fin.castSucc_lt_castSucc_iff.mpr hji')
        simp [(Submodule.Quotient.mk_eq_zero _).mpr hjflag]
      · exact (hji hji').elim
      · simp [h.isUpperTriangular hij]
    · simp
  · intro h
    have hcoeff (i j : Fin n) (hji : j ≤ i) :
        coefficientMatrix (C := H) b i j = if i = j then 1 else 0 := by
      let q := (b.flag j.castSucc).mkQ
      let phi : (M ⧸ b.flag j.castSucc) →ₗ[k] k :=
        (b.flag j.castSucc).liftQ (b.coord i)
          (b.flag_le_ker_coord (Fin.castSucc_le_castSucc_iff.mpr hji))
      have heq := congrArg
        (fun z ↦ TensorProduct.lid k H
          (TensorProduct.map phi (LinearMap.id : H →ₗ[k] H) z)) (h j)
      rw [TensorProduct.map_map] at heq
      have hcomp : phi.comp q = b.coord i := by
        exact (b.flag j.castSucc).liftQ_mkQ (b.coord i) _
      rw [hcomp, LinearMap.id_comp] at heq
      rw [← matrixCoefficient_def] at heq
      rw [coefficientMatrix_apply]
      by_cases hij : i = j
      · subst i
        simpa [phi, q, Submodule.liftQ_apply, Basis.coord_apply] using heq
      · simpa [phi, q, Submodule.liftQ_apply, Basis.coord_apply, hij] using heq
    rw [Matrix.isUpperUnitriangular_def]
    refine ⟨?_, ?_⟩
    · intro i j hji
      have hji' : j < i := by simpa only [id_eq] using hji
      simpa [hji'.ne'] using hcoeff i j hji'.le
    · intro i
      rw [hcoeff i i le_rfl]
      simp

/-- The coaction of a basis vector in a stable initial segment belongs to the tensor product of
that initial segment with the coalgebra. -/
theorem coact_basis_mem_flag (b : Basis (Fin n) k M)
    (h : (coefficientMatrix (C := H) b).IsUpperTriangular)
    {i : Fin n} {r : Fin (n + 1)} (hir : i.castSucc < r) :
    coact (C := H) (b i) ∈
      LinearMap.range
        (TensorProduct.map (b.flag r).subtype (LinearMap.id : H →ₗ[k] H)) := by
  classical
  refine ⟨∑ j, if hjr : j.castSucc < r then
      (⟨b j, b.self_mem_flag hjr⟩ : b.flag r) ⊗ₜ[k]
        coefficientMatrix (C := H) b j i else 0, ?_⟩
  rw [coact_basis_eq_sum_coefficientMatrix, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hjr : j.castSucc < r
  · simp [hjr]
  · have hij : i < j := Fin.castSucc_lt_castSucc_iff.mp
      (lt_of_lt_of_le hir (le_of_not_gt hjr))
    simp [hjr, h hij]

/-- The initial spans of a basis with upper-triangular coefficient matrix, bundled as
subcomodules. -/
def flagSubcomodule (b : Basis (Fin n) k M)
    (h : (coefficientMatrix (C := H) b).IsUpperTriangular) (r : Fin (n + 1)) :
    Subcomodule k H M :=
  Subcomodule.ofSubmodule (b.flag r) fun m hm ↦ by
    have hle : b.flag r ≤
        (LinearMap.range
          (TensorProduct.map (b.flag r).subtype (LinearMap.id : H →ₗ[k] H))).comap
            (coact (C := H) (M := M)) := by
      rw [b.flag_le_iff]
      intro i hir
      exact coact_basis_mem_flag b h hir
    exact hle hm

/-- The underlying submodule of `flagSubcomodule` is the corresponding basis flag. -/
@[simp]
theorem flagSubcomodule_toSubmodule (b : Basis (Fin n) k M)
    (h : (coefficientMatrix (C := H) b).IsUpperTriangular) (r : Fin (n + 1)) :
    (flagSubcomodule (H := H) b h r).toSubmodule = b.flag r := by
  rw [flagSubcomodule, Subcomodule.toSubmodule_carrier]
  exact Subcomodule.ofSubmodule_carrier _ _

/-- The first term of the bundled basis flag is the zero subcomodule. -/
@[simp]
theorem flagSubcomodule_zero (b : Basis (Fin n) k M)
    (h : (coefficientMatrix (C := H) b).IsUpperTriangular) :
    flagSubcomodule (H := H) b h 0 = ⊥ := by
  ext m
  simp only [← Subcomodule.mem_toSubmodule, flagSubcomodule_toSubmodule,
    Basis.flag_zero, Subcomodule.bot_toSubmodule, Submodule.mem_bot]

/-- The last term of the bundled basis flag is the full comodule. -/
@[simp]
theorem flagSubcomodule_last (b : Basis (Fin n) k M)
    (h : (coefficientMatrix (C := H) b).IsUpperTriangular) :
    flagSubcomodule (H := H) b h (.last n) = ⊤ := by
  ext m
  simp only [← Subcomodule.mem_toSubmodule, flagSubcomodule_toSubmodule,
    Basis.flag_last, Subcomodule.top_toSubmodule, Submodule.mem_top]

/-- The bundled basis flag is monotone. -/
theorem flagSubcomodule_monotone (b : Basis (Fin n) k M)
    (h : (coefficientMatrix (C := H) b).IsUpperTriangular) :
    Monotone (flagSubcomodule (H := H) b h) := by
  intro r s hrs m hm
  rw [← Subcomodule.mem_toSubmodule, flagSubcomodule_toSubmodule] at hm ⊢
  exact b.flag_mono hrs hm

/-- The bundled basis flag is strictly monotone. -/
theorem flagSubcomodule_strictMono (b : Basis (Fin n) k M)
    [Nontrivial k] (h : (coefficientMatrix (C := H) b).IsUpperTriangular) :
    StrictMono (flagSubcomodule (H := H) b h) := by
  intro r s hrs
  refine lt_of_le_of_ne (flagSubcomodule_monotone b h hrs.le) ?_
  intro hrs'
  have hflags := congrArg Subcomodule.toSubmodule hrs'
  rw [flagSubcomodule_toSubmodule, flagSubcomodule_toSubmodule] at hflags
  exact (b.flag_strictMono hrs).ne hflags

/-- A basis vector does not vanish in the quotient by the span of its predecessors. -/
theorem quotient_mk_basis_ne_zero [Nontrivial k] (b : Basis (Fin n) k M) (i : Fin n) :
    (Submodule.Quotient.mk (b i) : M ⧸ b.flag i.castSucc) ≠ 0 := by
  rw [ne_eq, Submodule.Quotient.mk_eq_zero, b.self_mem_flag_iff]
  exact lt_irrefl i.castSucc

/-- In the quotient by the preceding term of an upper-unitriangular basis flag, the class of the
next basis vector has trivial coaction. -/
theorem quotientCoact_flagSubcomodule_mk_basis
    (b : Basis (Fin n) k M)
    (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) (i : Fin n) :
    let N := flagSubcomodule (H := H) b h.isUpperTriangular i.castSucc
    N.quotientCoact (Submodule.Quotient.mk (b i)) =
      Submodule.Quotient.mk (b i) ⊗ₜ[k] (1 : H) := by
  dsimp only
  rw [Subcomodule.quotientCoact_mk, flagSubcomodule_toSubmodule]
  exact (coefficientMatrix_isUpperUnitriangular_iff b).mp h i

end

end TauCeti.Comodule
