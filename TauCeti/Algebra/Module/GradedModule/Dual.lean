/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Duals of internally graded modules

This file gives the linear dual of a finitely generated internally graded module its canonical
grading. A functional has degree `p` when it is supported on the original degree `-p` piece.
Consequently, evaluation can be nonzero only on degrees summing to zero.

Finite generation ensures that the algebraic dual is a direct *sum* of its homogeneous pieces:
an internally graded finitely generated module has only finitely many nonzero degrees.
No projectivity is needed for this decomposition. Later tensor-duality comparisons may add the
finite-projectivity hypotheses needed to identify duals of tensor products.

The construction follows the graded-dual convention used for DG and `A∞` objects in B. Keller,
*Introduction to A-infinity algebras and modules*, Sections 3 and 7.

## Main definitions

* `InternalGrading.dualPiece`: the degree-`p` submodule of the linear dual.
* `InternalGrading.dual`: the internal grading of the linear dual of a finitely generated module.

## Main results

* `InternalGrading.finite_setOf_piece_ne_bot`: a finitely generated internally graded module has
  only finitely many nonzero homogeneous pieces.
* `InternalGrading.mem_dualPiece_iff`: a degree-`p` functional vanishes on every original degree
  other than `-p`.
* `InternalGrading.apply_eq_zero_of_mem_dualPiece_of_add_ne_zero`: evaluation vanishes unless the
  degrees of the functional and vector sum to zero.

This completes the finite-dual compatibility in Layer 0 of the `DGAInfinity` roadmap.
-/

public section

open scoped DirectSum

namespace TauCeti

universe u v

namespace InternalGrading

section FiniteSupport

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A finitely generated internally graded module has only finitely many nonzero homogeneous
pieces. -/
theorem finite_setOf_piece_ne_bot (G : InternalGrading R M) [Module.Finite R M] :
    {p | G.piece p ≠ ⊥}.Finite := by
  have hcompact : IsCompactElement (⊤ : Submodule R M) :=
    (Submodule.fg_iff_compact _).mp Module.Finite.fg_top
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup
    (Submodule R M) hcompact G.piece (by rw [G.isInternal.submodule_iSup_eq_top])
  refine s.finite_toSet.subset fun p hp ↦ ?_
  by_contra hps
  apply hp
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ ⨆ i ∈ s, G.piece i := hs Submodule.mem_top
  have hle : (⨆ i ∈ s, G.piece i) ≤ ⨆ i, ⨆ (_ : i ≠ p), G.piece i := by
    refine iSup_le fun i ↦ iSup_le fun hi ↦ le_iSup_of_le i ?_
    exact le_iSup_of_le (fun hip ↦ hps (hip ▸ hi)) le_rfl
  have hxother := hle hx'
  have hxbot := (G.isInternal.submodule_iSupIndep p).le_bot ⟨hx, hxother⟩
  simpa only [Submodule.mem_bot] using hxbot

end FiniteSupport

section Dual

variable {R : Type u} {M : Type v}

section DualPiece

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The degree-`p` part of the graded dual consists of the functionals vanishing on every
homogeneous piece except degree `-p`. -/
def dualPiece (G : InternalGrading R M) (p : ℤ) : Submodule R (Module.Dual R M) :=
  ⨅ q, ⨅ (_ : q ≠ -p), (G.piece q).dualAnnihilator

/-- A functional belongs to degree `p` of the graded dual exactly when it vanishes on every
original degree other than `-p`. -/
@[simp]
theorem mem_dualPiece_iff (G : InternalGrading R M) (p : ℤ) (φ : Module.Dual R M) :
    φ ∈ G.dualPiece p ↔ ∀ q (x : M), x ∈ G.piece q → q ≠ -p → φ x = 0 := by
  simp only [dualPiece, Submodule.mem_iInf, Submodule.mem_dualAnnihilator]
  aesop

/-- A functional in dual degree `p` vanishes on an original homogeneous vector of degree `q`
unless `p + q = 0`. -/
@[grind]
theorem apply_eq_zero_of_mem_dualPiece_of_add_ne_zero (G : InternalGrading R M) {p q : ℤ}
    {φ : Module.Dual R M} {x : M} (hφ : φ ∈ G.dualPiece p) (hx : x ∈ G.piece q)
    (hpq : p + q ≠ 0) : φ x = 0 :=
  (mem_dualPiece_iff G p φ).mp hφ q x hx (by omega)

end DualPiece

section Construction

variable [CommRing R] [AddCommGroup M] [Module R M]

private noncomputable def projection (G : InternalGrading R M) (p : ℤ) : M →ₗ[R] M :=
  (G.piece p).subtype ∘ₗ
    DirectSum.component R ℤ (fun q ↦ G.piece q) p ∘ₗ
      (DirectSum.decomposeLinearEquiv G.piece).toLinearMap

private theorem projection_apply_of_mem (G : InternalGrading R M) {p : ℤ} {x : M}
    (hx : x ∈ G.piece p) : projection G p x = x := by
  -- Expose the subtype component so the direct-sum inclusion formula applies.
  change (G.piece p).subtype
    (DirectSum.component R ℤ (fun q ↦ G.piece q) p
      (DirectSum.decomposeLinearEquiv G.piece (⟨x, hx⟩ : G.piece p))) = x
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.component.lof_self]
  rfl

private theorem projection_apply_eq_zero_of_mem_of_ne (G : InternalGrading R M) {p q : ℤ}
    (hpq : p ≠ q) {x : M} (hx : x ∈ G.piece p) : projection G q x = 0 := by
  -- Expose the subtype component so the off-diagonal direct-sum formula applies.
  change (G.piece q).subtype
    (DirectSum.component R ℤ (fun r ↦ G.piece r) q
      (DirectSum.decomposeLinearEquiv G.piece (⟨x, hx⟩ : G.piece p))) = 0
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.component.of]
  simp [hpq]

private theorem dualMap_projection_mem_dualPiece (G : InternalGrading R M) (p : ℤ)
    (φ : Module.Dual R M) : (projection G (-p)).dualMap φ ∈ G.dualPiece p := by
  rw [mem_dualPiece_iff]
  intro q x hx hq
  simp only [LinearMap.dualMap_apply]
  rw [projection_apply_eq_zero_of_mem_of_ne G hq hx]
  exact map_zero φ

private noncomputable def supportFinset (G : InternalGrading R M) [Module.Finite R M] :
    Finset ℤ :=
  G.finite_setOf_piece_ne_bot.toFinset

private theorem mem_supportFinset_iff (G : InternalGrading R M) [Module.Finite R M] (p : ℤ) :
    p ∈ supportFinset G ↔ G.piece p ≠ ⊥ := by
  simp [supportFinset]

private theorem sum_projection_eq_id (G : InternalGrading R M) [Module.Finite R M] :
    ∑ p ∈ supportFinset G, projection G p = LinearMap.id := by
  refine DirectSum.decompose_lhom_ext (ℳ := G.piece) fun p ↦ ?_
  apply LinearMap.ext
  intro x
  by_cases hp : G.piece p = ⊥
  · have hx : (x : M) = 0 := by simpa only [hp, Submodule.mem_bot] using x.property
    simp [hx]
  · simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.sum_apply]
    rw [Finset.sum_eq_single_of_mem p ((mem_supportFinset_iff G p).2 hp)]
    · exact projection_apply_of_mem G x.property
    · intro q hq hqp
      exact projection_apply_eq_zero_of_mem_of_ne G (p := p) (q := q) hqp.symm x.property

private theorem iSup_dualPiece_eq_top (G : InternalGrading R M) [Module.Finite R M] :
    ⨆ p, G.dualPiece p = ⊤ := by
  apply top_unique
  intro φ _
  have hsum : ∑ p ∈ supportFinset G, (projection G p).dualMap φ = φ := by
    apply LinearMap.ext
    intro x
    have hproj := DFunLike.congr_fun (sum_projection_eq_id G) x
    simp only [LinearMap.sum_apply, LinearMap.id_apply] at hproj
    simp only [LinearMap.sum_apply, LinearMap.dualMap_apply]
    -- Read the bundled dual-map sum pointwise before applying linearity of `φ`.
    change (∑ p ∈ supportFinset G, φ (projection G p x)) = φ x
    simpa only [map_sum] using congrArg φ hproj
  rw [← hsum]
  exact Submodule.sum_mem _ fun p _ ↦
    (le_iSup (fun q ↦ G.dualPiece q) (-p)) (by
      simpa only [neg_neg] using dualMap_projection_mem_dualPiece G (-p) φ)

private theorem iSupIndep_dualPiece (G : InternalGrading R M) :
    iSupIndep G.dualPiece := by
  intro p
  rw [Submodule.disjoint_def]
  intro φ hφ hφother
  have hφp := (mem_dualPiece_iff G p φ).mp hφ
  have hother_le : (⨆ q, ⨆ (_ : q ≠ p), G.dualPiece q) ≤
      (G.piece (-p)).dualAnnihilator := by
    refine iSup_le fun q ↦ iSup_le fun hqp ψ hψ ↦ ?_
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    exact (mem_dualPiece_iff G q ψ).mp hψ (-p) x hx (by omega)
  have hφ_on_p := (Submodule.mem_dualAnnihilator φ).mp (hother_le hφother)
  refine DirectSum.decompose_lhom_ext (ℳ := G.piece) fun q ↦ ?_
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.zero_comp, LinearMap.zero_apply]
  by_cases hq : q = -p
  · subst q
    exact hφ_on_p x x.property
  · exact hφp q x x.property hq

/-- The internal grading on the linear dual of a finitely generated internally graded module.

The degree is reversed: a functional of degree `p` is supported on the original degree `-p`
piece. -/
noncomputable def dual (G : InternalGrading R M) [Module.Finite R M] :
    InternalGrading R (Module.Dual R M) where
  piece := G.dualPiece
  isInternal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    G.iSupIndep_dualPiece G.iSup_dualPiece_eq_top

/-- The degree-`p` piece of the dual grading is `dualPiece G p`. -/
@[simp]
theorem dual_piece (G : InternalGrading R M) [Module.Finite R M] (p : ℤ) :
    G.dual.piece p = G.dualPiece p :=
  (rfl)

end Construction

end Dual

end InternalGrading

end TauCeti
