/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.LinearAlgebra.Projection

/-!
# Duals of internally graded modules

This file gives the linear dual of an internally graded module its canonical grading. A functional
has degree `p` when it is supported on the original degree `-p` piece, and restriction identifies
that degree with the linear dual of `G.piece (-p)`. Consequently, evaluation can be nonzero only on
degrees summing to zero.

The homogeneous pieces exhaust the dual as soon as the grading has only finitely many nonzero
pieces, and no projectivity is needed for that. Finite generation of the module is one source of
the hypothesis, through `InternalGrading.finite_setOfPred_piece_ne_bot`. Later tensor-duality
comparisons may add the finite-projectivity hypotheses needed to identify duals of tensor products.

The construction follows the graded-dual convention used for DG and `A∞` objects in B. Keller,
*Introduction to A-infinity algebras and modules*, Sections 3 and 7.

## Main definitions

* `InternalGrading.dualPiece`: the degree-`p` submodule of the linear dual.
* `InternalGrading.dualPieceEquiv`: the identification of that submodule with the linear dual of the
  original degree-`-p` piece, by restriction.
* `InternalGrading.dual`: the internal grading of the linear dual of a module whose grading has
  finitely many nonzero pieces.

## Main results

* `InternalGrading.mem_dualPiece_iff`: a degree-`p` functional vanishes on every original degree
  other than `-p`.
* `InternalGrading.dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero`: evaluation vanishes unless
  the degrees of the functional and vector sum to zero.
* `InternalGrading.dual_decompose_apply_of_mem_piece`: on the degree-`q` piece, a functional agrees
  with its own degree-`-q` homogeneous component.

This supplies the dual grading for Layer 0 of the `DGAInfinity` roadmap; the finite-projective
identifications of duals of tensor products remain.
-/

public section

open scoped DirectSum

namespace TauCeti

universe u v

namespace InternalGrading

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
@[grind →]
theorem dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero (G : InternalGrading R M) {p q : ℤ}
    {φ : Module.Dual R M} {x : M} (hφ : φ ∈ G.dualPiece p) (hx : x ∈ G.piece q)
    (hpq : p + q ≠ 0) : φ x = 0 :=
  (mem_dualPiece_iff G p φ).mp hφ q x hx (by omega)

end DualPiece

section Construction

variable [CommRing R] [AddCommGroup M] [Module R M]

private noncomputable def projection (G : InternalGrading R M) (p : ℤ) : M →ₗ[R] M :=
  (G.piece p).subtype ∘ₗ
    internalProjection G.isInternal.submodule_iSupIndep G.isInternal.submodule_iSup_eq_top p

private theorem projection_apply_of_mem (G : InternalGrading R M) {p : ℤ} {x : M}
    (hx : x ∈ G.piece p) : projection G p x = x :=
  congrArg Subtype.val (internalProjection_apply_of_mem _ _ hx)

private theorem projection_apply_eq_zero_of_mem_of_ne (G : InternalGrading R M) {p q : ℤ}
    (hpq : p ≠ q) {x : M} (hx : x ∈ G.piece p) : projection G q x = 0 :=
  congrArg Subtype.val (internalProjection_apply_eq_zero_of_mem_of_ne _ _ hpq hx)

private theorem projection_mem (G : InternalGrading R M) (p : ℤ) (x : M) :
    projection G p x ∈ G.piece p :=
  (internalProjection G.isInternal.submodule_iSupIndep G.isInternal.submodule_iSup_eq_top p x).2

/-- A functional of dual degree `p` is unchanged by projecting its argument to the degree-`-p`
piece: it annihilates the supremum of the other pieces, which is the kernel of that projection. -/
private theorem apply_projection_neg (G : InternalGrading R M) {p : ℤ} {φ : Module.Dual R M}
    (hφ : φ ∈ G.dualPiece p) (x : M) : φ (projection G (-p) x) = φ x := by
  have hker : (⨆ q, ⨆ (_ : q ≠ -p), G.piece q) ≤ LinearMap.ker φ :=
    iSup_le fun q ↦ iSup_le fun hq ↦ fun z hz ↦
      LinearMap.mem_ker.mpr ((mem_dualPiece_iff G p φ).mp hφ q z hz hq)
  have hmem : x - projection G (-p) x ∈ LinearMap.ker φ := by
    refine hker ?_
    rw [← ker_internalProjection G.isInternal.submodule_iSupIndep
      G.isInternal.submodule_iSup_eq_top (-p), LinearMap.mem_ker, map_sub, sub_eq_zero,
      internalProjection_apply_of_mem _ _ (projection_mem G (-p) x)]
    -- `projection G (-p) x` is the underlying element of `internalProjection … (-p) x`.
    exact Subtype.ext rfl
  have := LinearMap.mem_ker.mp hmem
  rw [map_sub, sub_eq_zero] at this
  exact this.symm

/-- Restricting a functional of dual degree `p` to the degree-`-p` piece identifies `G.dualPiece p`
with the linear dual of that piece: the restriction determines the functional, and every functional
on the piece extends along the projection. -/
noncomputable def dualPieceEquiv (G : InternalGrading R M) (p : ℤ) :
    G.dualPiece p ≃ₗ[R] Module.Dual R (G.piece (-p)) where
  toFun φ := (φ : Module.Dual R M) ∘ₗ (G.piece (-p)).subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun ψ :=
    ⟨ψ ∘ₗ internalProjection G.isInternal.submodule_iSupIndep
        G.isInternal.submodule_iSup_eq_top (-p), by
      rw [mem_dualPiece_iff]
      intro q x hx hq
      rw [LinearMap.comp_apply,
        internalProjection_apply_eq_zero_of_mem_of_ne _ _ hq hx, map_zero]⟩
  left_inv φ := Subtype.ext (LinearMap.ext fun x ↦ apply_projection_neg G φ.2 x)
  right_inv ψ := LinearMap.ext fun y ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      internalProjection_apply]

/-- A functional of dual degree `p` restricts to the degree-`-p` piece by evaluation. -/
@[simp]
theorem dualPieceEquiv_apply (G : InternalGrading R M) (p : ℤ) (φ : G.dualPiece p)
    (y : G.piece (-p)) : G.dualPieceEquiv p φ y = (φ : Module.Dual R M) y :=
  (rfl)

/-- The functional of dual degree `p` extending `ψ` restricts to `ψ` on the degree-`-p` piece. -/
@[simp]
theorem dualPieceEquiv_symm_apply_coe (G : InternalGrading R M) (p : ℤ)
    (ψ : Module.Dual R (G.piece (-p))) (y : G.piece (-p)) :
    ((G.dualPieceEquiv p).symm ψ : Module.Dual R M) (y : M) = ψ y :=
  DFunLike.congr_fun ((G.dualPieceEquiv p).apply_symm_apply ψ) y

private noncomputable def supportFinset (G : InternalGrading R M)
    (hG : {p | G.piece p ≠ ⊥}.Finite) : Finset ℤ :=
  hG.toFinset

private theorem mem_supportFinset_iff (G : InternalGrading R M)
    (hG : {p | G.piece p ≠ ⊥}.Finite) (p : ℤ) :
    p ∈ supportFinset G hG ↔ G.piece p ≠ ⊥ := by
  simp [supportFinset]

private theorem sum_projection_eq_id (G : InternalGrading R M)
    (hG : {p | G.piece p ≠ ⊥}.Finite) :
    ∑ p ∈ supportFinset G hG, projection G p = LinearMap.id := by
  refine DirectSum.decompose_lhom_ext (ℳ := G.piece) fun p ↦ ?_
  apply LinearMap.ext
  intro x
  by_cases hp : G.piece p = ⊥
  · have hx : (x : M) = 0 := by simpa only [hp, Submodule.mem_bot] using x.property
    simp [hx]
  · simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.sum_apply]
    rw [Finset.sum_eq_single_of_mem p ((mem_supportFinset_iff G hG p).2 hp)]
    · exact projection_apply_of_mem G x.property
    · intro q hq hqp
      exact projection_apply_eq_zero_of_mem_of_ne G (p := p) (q := q) hqp.symm x.property

private theorem iSup_dualPiece_eq_top (G : InternalGrading R M)
    (hG : {p | G.piece p ≠ ⊥}.Finite) : ⨆ p, G.dualPiece p = ⊤ := by
  apply top_unique
  intro φ _
  have hsum : ∑ p ∈ supportFinset G hG, (projection G p).dualMap φ = φ := by
    apply LinearMap.ext
    intro x
    have hproj := DFunLike.congr_fun (sum_projection_eq_id G hG) x
    simp only [LinearMap.sum_apply, LinearMap.id_apply] at hproj
    simp only [LinearMap.sum_apply, LinearMap.dualMap_apply]
    simpa only [map_sum] using congrArg φ hproj
  rw [← hsum]
  refine Submodule.sum_mem _ fun p _ ↦ (le_iSup (fun q ↦ G.dualPiece q) (-p)) ?_
  rw [mem_dualPiece_iff]
  intro q x hx hq
  rw [LinearMap.dualMap_apply, projection_apply_eq_zero_of_mem_of_ne G (by simpa using hq) hx,
    map_zero]

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

/-- The internal grading on the linear dual of a module whose grading has only finitely many
nonzero pieces.

The degree is reversed: a functional of degree `p` is supported on the original degree `-p`
piece. -/
noncomputable def dual (G : InternalGrading R M) (hG : {p | G.piece p ≠ ⊥}.Finite) :
    InternalGrading R (Module.Dual R M) where
  piece := G.dualPiece
  isInternal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    G.iSupIndep_dualPiece (G.iSup_dualPiece_eq_top hG)

/-- The degree-`p` piece of the dual grading is `dualPiece G p`. -/
@[simp]
theorem dual_piece (G : InternalGrading R M) (hG : {p | G.piece p ≠ ⊥}.Finite) (p : ℤ) :
    (G.dual hG).piece p = G.dualPiece p :=
  (rfl)

/-- On the degree-`q` piece a functional agrees with its own degree-`-q` homogeneous component for
the dual grading: all the other components vanish there. -/
theorem dual_decompose_apply_of_mem_piece (G : InternalGrading R M)
    (hG : {p | G.piece p ≠ ⊥}.Finite) (φ : Module.Dual R M) {q : ℤ} {x : M}
    (hx : x ∈ G.piece q) :
    ((DirectSum.decompose (G.dual hG).piece φ (-q) : (G.dual hG).piece (-q)) :
      Module.Dual R M) x = φ x := by
  classical
  have hsum := DirectSum.sum_support_decompose (G.dual hG).piece φ
  have happ := congrArg (fun ψ : Module.Dual R M ↦ ψ x) hsum
  simp only [LinearMap.sum_apply] at happ
  rw [← happ]
  by_cases hmem : -q ∈ (DirectSum.decompose (G.dual hG).piece φ).support
  · symm
    refine Finset.sum_eq_single_of_mem (-q) hmem ?_
    intro p _ hpq
    exact dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero G
      (DirectSum.decompose (G.dual hG).piece φ p).2 hx (by omega)
  · have hzero : DirectSum.decompose (G.dual hG).piece φ (-q) = 0 :=
      DFinsupp.notMem_support_iff.mp hmem
    have hall : ∀ p ∈ (DirectSum.decompose (G.dual hG).piece φ).support,
        ((DirectSum.decompose (G.dual hG).piece φ p : (G.dual hG).piece p) :
          Module.Dual R M) x = 0 := by
      intro p hp
      refine dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero G
        (DirectSum.decompose (G.dual hG).piece φ p).2 hx fun hpq ↦ ?_
      exact hmem (by rwa [show (-q : ℤ) = p by omega])
    rw [hzero, Finset.sum_eq_zero hall]
    simp

end Construction

end InternalGrading

end TauCeti
