/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Duals of internally graded modules

This file gives the linear dual of an internally graded module its canonical grading. A functional
has degree `p` when it is supported on the original degree `-p` piece, and restriction identifies
that degree with the linear dual of `G.piece (-p)`. Consequently, evaluation can be nonzero only on
degrees summing to zero.

The homogeneous pieces exhaust the dual as soon as the grading has only finitely many nonzero
pieces, and no projectivity is needed for that. Finite generation of the module is one source of
the hypothesis, through `InternalGrading.finite_piece_ne_bot`, and the dual grading inherits it
through `InternalGrading.finite_dualPiece_ne_bot`. Later tensor-duality comparisons may add the
finite-projectivity hypotheses needed to identify duals of tensor products.

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
* `InternalGrading.dualPiece_apply_eq_apply_decompose`: a degree-`p` functional sees only the
  degree-`-p` homogeneous component of its argument.
* `InternalGrading.finite_dualPiece_ne_bot`: the dual grading has finitely many nonzero pieces as
  soon as the original one does.
* `InternalGrading.iSupIndep_dualPiece`: the dual pieces are independent, without a finiteness
  hypothesis.
* `InternalGrading.dual_decompose_apply`: the degree-`p` component of a functional evaluates an
  arbitrary vector through its original degree-`-p` component.
* `InternalGrading.dual_decompose_apply_of_mem_piece`: on the degree-`q` piece, a functional agrees
  with its own degree-`-q` homogeneous component.

## Implementation notes

The construction lives over a commutative semiring. Although independence and spanning do not in
general assemble an internal direct sum without additive inverses, injectivity of the canonical map
for these dual pieces follows directly by evaluating each summand on its matching primal piece.

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

/-- The homogeneous component of degree `p`, as a linear map to that piece. -/
private noncomputable def projection (G : InternalGrading R M) (p : ℤ) : M →ₗ[R] G.piece p :=
  DirectSum.component R ℤ (fun q ↦ G.piece q) p ∘ₗ
    (DirectSum.decomposeLinearEquiv G.piece).toLinearMap

@[simp]
private theorem projection_apply (G : InternalGrading R M) (p : ℤ) (x : M) :
    projection G p x = DirectSum.decompose G.piece x p :=
  rfl

/-- A functional of dual degree `p` sees only the degree-`-p` homogeneous component of its
argument: it annihilates every other component of the decomposition. -/
theorem dualPiece_apply_eq_apply_decompose (G : InternalGrading R M) {p : ℤ}
    {φ : Module.Dual R M} (hφ : φ ∈ G.dualPiece p) (x : M) :
    φ x = φ (DirectSum.decompose G.piece x (-p) : M) :=
  G.map_eq_map_decompose φ.toAddMonoidHom
    (fun q y hy hq ↦ (mem_dualPiece_iff G p φ).mp hφ q y hy hq) x

/-- Restricting a functional of dual degree `p` to the degree-`-p` piece identifies `G.dualPiece p`
with the linear dual of that piece: the restriction determines the functional, and every functional
on the piece extends along the homogeneous component of degree `-p`. -/
noncomputable def dualPieceEquiv (G : InternalGrading R M) (p : ℤ) :
    G.dualPiece p ≃ₗ[R] Module.Dual R (G.piece (-p)) where
  toFun φ := (φ : Module.Dual R M) ∘ₗ (G.piece (-p)).subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun ψ :=
    ⟨ψ ∘ₗ projection G (-p), by
      rw [mem_dualPiece_iff]
      intro q x hx hq
      rw [LinearMap.comp_apply, projection_apply,
        Submodule.coe_eq_zero.mp (DirectSum.decompose_of_mem_ne G.piece hx hq), map_zero]⟩
  left_inv φ :=
    Subtype.ext (LinearMap.ext fun x ↦ (dualPiece_apply_eq_apply_decompose G φ.2 x).symm)
  right_inv ψ := LinearMap.ext fun y ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply, projection_apply,
      Subtype.ext (DirectSum.decompose_of_mem_same G.piece y.2)]

/-- A functional of dual degree `p` restricts to the degree-`-p` piece by evaluation. -/
@[simp]
theorem dualPieceEquiv_apply (G : InternalGrading R M) (p : ℤ) (φ : G.dualPiece p)
    (y : G.piece (-p)) : G.dualPieceEquiv p φ y = (φ : Module.Dual R M) y :=
  (rfl)

/-- The functional of dual degree `p` extending `ψ` evaluates an arbitrary vector on its degree-`-p`
homogeneous component. -/
theorem dualPieceEquiv_symm_apply (G : InternalGrading R M) (p : ℤ)
    (ψ : Module.Dual R (G.piece (-p))) (x : M) :
    ((G.dualPieceEquiv p).symm ψ : Module.Dual R M) x =
      ψ (DirectSum.decompose G.piece x (-p)) :=
  (rfl)

/-- The functional of dual degree `p` extending `ψ` restricts to `ψ` on the degree-`-p` piece. -/
@[simp]
theorem dualPieceEquiv_symm_apply_coe (G : InternalGrading R M) (p : ℤ)
    (ψ : Module.Dual R (G.piece (-p))) (y : G.piece (-p)) :
    ((G.dualPieceEquiv p).symm ψ : Module.Dual R M) (y : M) = ψ y :=
  DFunLike.congr_fun ((G.dualPieceEquiv p).apply_symm_apply ψ) y

/-- Dual degree `p` is zero as soon as the original degree `-p` is: a functional of dual degree `p`
sees only that piece of its argument. -/
theorem dualPiece_eq_bot_of_piece_eq_bot (G : InternalGrading R M) {p : ℤ}
    (h : G.piece (-p) = ⊥) : G.dualPiece p = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun φ hφ ↦ LinearMap.ext fun x ↦ ?_
  have hx : (DirectSum.decompose G.piece x (-p) : M) = 0 :=
    (Submodule.eq_bot_iff _).mp h _ (DirectSum.decompose G.piece x (-p)).2
  rw [dualPiece_apply_eq_apply_decompose G hφ x, hx, map_zero, LinearMap.zero_apply]

/-- The dual grading has only finitely many nonzero pieces as soon as the original one does, the
degree-`p` piece of the dual being carried by the original degree `-p`. -/
theorem finite_dualPiece_ne_bot (G : InternalGrading R M) (hG : {p | G.piece p ≠ ⊥}.Finite) :
    {p | G.dualPiece p ≠ ⊥}.Finite :=
  (hG.image fun q ↦ -q).subset fun p hp ↦
    ⟨-p, fun h ↦ hp (G.dualPiece_eq_bot_of_piece_eq_bot h), neg_neg p⟩

private theorem iSup_dualPiece_eq_top (G : InternalGrading R M)
    (hG : {p | G.piece p ≠ ⊥}.Finite) : ⨆ p, G.dualPiece p = ⊤ := by
  classical
  refine top_unique fun φ _ ↦ ?_
  have hφ : ∑ p ∈ hG.toFinset,
      LinearMap.comp φ ((G.piece p).subtype ∘ₗ projection G p) = φ := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      projection_apply]
    rw [← map_sum, G.sum_decompose_toFinset hG x]
  rw [← hφ]
  refine Submodule.sum_mem _ fun p _ ↦ le_iSup (fun q ↦ G.dualPiece q) (-p) ?_
  rw [mem_dualPiece_iff]
  intro q x hx hq
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, projection_apply]
  rw [DirectSum.decompose_of_mem_ne G.piece hx (by simpa using hq), map_zero]

/-- The pieces of the graded dual are independent, even when the original grading has infinitely
many nonzero pieces. -/
theorem iSupIndep_dualPiece (G : InternalGrading R M) :
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
  isInternal := by
    -- Mathlib defines `IsInternal` using the additive canonical map; `coeLinearMap` below has the
    -- same underlying function and lets the module-level range API prove surjectivity.
    constructor
    · intro a b hab
      have hab' : DirectSum.coeLinearMap G.dualPiece a =
          DirectSum.coeLinearMap G.dualPiece b := hab
      apply DirectSum.ext
      intro p
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      rw [dualPiece_apply_eq_apply_decompose G (a p).2,
        dualPiece_apply_eq_apply_decompose G (b p).2]
      have hcomponent : ∀ c : ⨁ p, G.dualPiece p,
          DirectSum.coeLinearMap G.dualPiece c
            (DirectSum.decompose G.piece x (-p) : M) =
            (c p : Module.Dual R M) (DirectSum.decompose G.piece x (-p) : M) := by
        classical
        intro c
        rw [DirectSum.coeLinearMap_eq_dfinsuppSum, DFinsupp.sum, LinearMap.sum_apply]
        refine Finset.sum_eq_single p (fun q _ hpq ↦ ?_) fun hp ↦ ?_
        · exact dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero G (c q).2
            (DirectSum.decompose G.piece x (-p)).2 (by omega)
        · rw [DFinsupp.notMem_support_iff.mp hp]
          simp
      rw [← hcomponent a, hab', hcomponent b]
    · have hsurj : Function.Surjective (DirectSum.coeLinearMap G.dualPiece) := by
        rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap,
          G.iSup_dualPiece_eq_top hG]
      exact hsurj

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
  symm
  exact (G.dual hG).map_eq_map_decompose (LinearMap.applyₗ x).toAddMonoidHom
    (fun p ψ hψ hp ↦ dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero G
      (by simpa only [dual_piece] using hψ) hx (by omega)) φ

/-- The degree-`p` component of a functional evaluates an arbitrary vector by first taking its
original degree-`-p` homogeneous component. -/
@[simp]
theorem dual_decompose_apply (G : InternalGrading R M)
    (hG : {p | G.piece p ≠ ⊥}.Finite) (φ : Module.Dual R M) (p : ℤ) (x : M) :
    ((DirectSum.decompose (G.dual hG).piece φ p : (G.dual hG).piece p) :
      Module.Dual R M) x = φ (DirectSum.decompose G.piece x (-p) : M) := by
  rw [dualPiece_apply_eq_apply_decompose G
    (by exact (DirectSum.decompose (G.dual hG).piece φ p).2)]
  have h := dual_decompose_apply_of_mem_piece G hG φ
    (DirectSum.decompose G.piece x (-p)).2
  have hp : - -p = p := by omega
  rw [hp] at h
  exact h

end DualPiece

end InternalGrading

end TauCeti
