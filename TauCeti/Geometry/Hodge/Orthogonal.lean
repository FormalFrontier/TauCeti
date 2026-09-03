/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import TauCeti.Geometry.Hodge.Polarization
public import TauCeti.Geometry.Hodge.RationalSubstructure

/-!
# Orthogonal complements of rational Hodge substructures

A polarization of a pure Hodge structure splits off every rational Hodge substructure: the
orthogonal complement of the substructure for the rationalified polarizing form is again a rational
Hodge substructure, and the two are complementary both over `ℚ` and after complexification. This is
the semisimplicity statement for polarizable rational Hodge structures in the form the theory uses
it — a subobject of a polarizable Hodge structure is a direct summand.

Two facts about the polarizing form drive the argument, and neither of them needs the Hermitian
Hodge metric. First, the Hodge–Riemann orthogonality of the components says the form pairs `H^{p,q}`
only against `H^{q,p}`, so the orthogonal complement of a component-spanned subspace is again
component-spanned: `TauCeti.Hodge.IsPolarization.orthogonal_le_iSup_inf_piece`, proved through the
Hodge projections `TauCeti.Hodge.HodgeStructureOn.proj`. Second, on a component the Hodge–Riemann
positivity makes the pairing of a vector with its conjugate nonzero; since the complexification of
a rational subspace is conjugation-stable, no nonzero vector of it is orthogonal to all of it,
which is `TauCeti.Hodge.IsPolarization.disjoint_orthogonal`.

Rationality of the complement is not an extra hypothesis but a computation: the complexification of
the rational orthogonal complement *is* the complex orthogonal complement
(`TauCeti.Hodge.RationalHodgeSubstructure.rationalToComplexSubmodule_orthogonal`). One inclusion is
the compatibility of the two scalar extensions of the integral form; the reverse holds because both
subspaces complement the substructure, the rational one by Mathlib's
`LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint` applied over `ℚ`.

This is Layer L1 of `TauCetiRoadmap/HodgeStructures/README.md`, following Voisin, *Hodge Theory and
Complex Algebraic Geometry I*, §7.1.2, and Peters–Steenbrink, *Mixed Hodge Structures*, §2.

## Main declarations

* `TauCeti.Hodge.IsPolarization.orthogonal_le_iSup_inf_piece`: the orthogonal complement of a
  component-spanned subspace is component-spanned.
* `TauCeti.Hodge.IsPolarization.disjoint_orthogonal`: a conjugation-stable component-spanned
  subspace meets its orthogonal complement trivially.
* `TauCeti.Hodge.RationalHodgeSubstructure.orthogonal`: the orthogonal complement of a rational
  Hodge substructure, again a rational Hodge substructure.
* `TauCeti.Hodge.RationalHodgeSubstructure.isCompl_orthogonal` and
  `TauCeti.Hodge.RationalHodgeSubstructure.isCompl_WC_orthogonal_WC`: it is a complement, both
  rationally and after complexification.
* `TauCeti.Hodge.RationalHodgeSubstructure.integralFormBaseChange_orthogonal_top_eq_bot`: the
  rationalified polarizing form is nondegenerate.
* `TauCeti.Hodge.exists_isCompl_of_isPolarizable`: every rational Hodge substructure of a
  polarizable pure Hodge structure has an orthogonal direct-sum complement.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ]
variable [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {n : ℤ} {hs : HodgeStructure hℂ n} {Qint : LinearMap.BilinForm ℤ Vℤ}

namespace IsPolarization

/-- A Hodge projection of a vector orthogonal to a component-spanned subspace is again orthogonal
to it: the polarizing form pairs a Hodge component only against the complementary one, so the
orthogonality conditions decouple along the Hodge decomposition. -/
theorem proj_mem_orthogonal (hQ : IsPolarization hℂ hs Qint) {A : Submodule ℂ Vℂ}
    (hA : A ≤ ⨆ q, A ⊓ hs.piece q) {x : Vℂ}
    (hx : x ∈ LinearMap.BilinForm.orthogonal (integralFormBaseChange hℂ Qint) A) (p : ℤ) :
    hs.proj p x ∈ LinearMap.BilinForm.orthogonal (integralFormBaseChange hℂ Qint) A := by
  have hker : A ≤
      LinearMap.ker (LinearMap.flip (integralFormBaseChange hℂ Qint) (hs.proj p x)) := by
    refine hA.trans (iSup_le fun q w hw ↦ ?_)
    simp only [LinearMap.mem_ker, LinearMap.flip_apply]
    rcases eq_or_ne (q + p) n with hqp | hqp
    · have hcomp : (integralFormBaseChange hℂ Qint w) ∘ₗ hs.proj p =
          integralFormBaseChange hℂ Qint w := by
        refine hs.linearMap_ext_of_piece fun p' y hy ↦ ?_
        rcases eq_or_ne p' p with rfl | hp'
        · simp [hs.proj_apply_of_mem hy]
        · rw [LinearMap.comp_apply, hs.proj_apply_eq_zero_of_mem_of_ne hy hp', map_zero]
          exact (hQ.orthogonal_piece (by omega) hw.2 hy).symm
      have heval := congrArg (fun f : Vℂ →ₗ[ℂ] ℂ ↦ f x) hcomp
      simp only [LinearMap.comp_apply] at heval
      rw [heval]
      exact hx w hw.1
    · exact hQ.orthogonal_piece hqp hw.2 (hs.proj_mem p x)
  intro w hw
  simpa using hker hw

/-- **The orthogonal complement of a sub-Hodge structure is a sub-Hodge structure.** The orthogonal
complement of a subspace spanned by its intersections with the Hodge components is again spanned by
its intersections with the Hodge components. -/
theorem orthogonal_le_iSup_inf_piece (hQ : IsPolarization hℂ hs Qint) {A : Submodule ℂ Vℂ}
    (hA : A ≤ ⨆ q, A ⊓ hs.piece q) :
    LinearMap.BilinForm.orthogonal (integralFormBaseChange hℂ Qint) A ≤
      ⨆ p, LinearMap.BilinForm.orthogonal (integralFormBaseChange hℂ Qint) A ⊓ hs.piece p :=
  fun x hx ↦ hs.mem_iSup_of_proj_mem fun p ↦ ⟨hQ.proj_mem_orthogonal hA hx p, hs.proj_mem p x⟩

/-- **A polarization is nondegenerate on a sub-Hodge structure.** A conjugation-stable subspace
spanned by its intersections with the Hodge components meets its orthogonal complement trivially:
a nonzero vector of a Hodge component pairs nontrivially with its conjugate, which conjugation
stability keeps inside the subspace. -/
theorem disjoint_orthogonal (hQ : IsPolarization hℂ hs Qint) {A : Submodule ℂ Vℂ}
    (hA : A ≤ ⨆ q, A ⊓ hs.piece q) (hAconj : ∀ x ∈ A, latticeConj hℂ x ∈ A) :
    Disjoint A (LinearMap.BilinForm.orthogonal (integralFormBaseChange hℂ Qint) A) := by
  rw [Submodule.disjoint_def]
  intro x hxA hxO
  refine hs.eq_zero_of_proj_eq_zero fun p ↦ ?_
  by_contra hne
  have hvA : hs.proj p x ∈ A := hs.proj_mem_of_le_iSup_inf hA hxA p
  have hconj : integralFormBaseChange hℂ Qint (latticeConj hℂ (hs.proj p x)) (hs.proj p x) = 0 :=
    hQ.proj_mem_orthogonal hA hxO p _ (hAconj _ hvA)
  have hsymm := hQ.complex_symm_weight (hs.proj p x) (latticeConj hℂ (hs.proj p x))
  rw [hconj] at hsymm
  have hunit : ((n.negOnePow : ℤ) : ℂ) ≠ 0 := by
    rcases Int.units_eq_one_or n.negOnePow with h | h <;> simp [h]
  exact hQ.pairing_conj_ne_zero (hs.proj_mem p x) hne
    ((mul_eq_zero.1 hsymm.symm).resolve_left hunit)

end IsPolarization

namespace RationalHodgeSubstructure

variable (P : Polarization hℂ hs) (W : RationalHodgeSubstructure hℚ hs)

/-- A polarization is nondegenerate on the complexification of a rational Hodge substructure. -/
theorem disjoint_WC_orthogonal :
    Disjoint W.WC (LinearMap.BilinForm.orthogonal P.Q W.WC) := by
  rw [Polarization.Q_def]
  refine P.isPolarization.disjoint_orthogonal W.WC_eq_iSup_inf_piece.le fun x hx ↦ ?_
  simpa using W.conj_mem_WC hx

/-- The rationalified polarizing form is reflexive: it is symmetric or antisymmetric according to
the parity of the weight. -/
theorem isRefl_integralFormBaseChange : (integralFormBaseChange hℚ P.Qint).IsRefl := by
  intro x y hxy
  have hzero : integralFormBaseChange hℂ P.Qint
      (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] x))
      (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] y)) = 0 := by
    rw [integralFormBaseChange_rationalToComplexLinearEquiv_one_tmul, hxy]
    simp
  have hflip := P.isPolarization.complex_symm_weight
    (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] x))
    (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] y))
  rw [hzero, mul_zero, integralFormBaseChange_rationalToComplexLinearEquiv_one_tmul] at hflip
  exact_mod_cast hflip

/-- The complexification of the rational orthogonal complement is contained in the complex
orthogonal complement. -/
theorem rationalToComplexSubmodule_orthogonal_le :
    rationalToComplexSubmodule hℚ hℂ
        (LinearMap.BilinForm.orthogonal (integralFormBaseChange hℚ P.Qint) W.WQ) ≤
      LinearMap.BilinForm.orthogonal P.Q W.WC := by
  rw [rationalToComplexSubmodule_eq_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u, hu, rfl⟩
  have hker : W.WC ≤ LinearMap.ker
      (LinearMap.flip P.Q (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] u))) := by
    rw [WC_def, rationalToComplexSubmodule_eq_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply, Polarization.Q_def,
      integralFormBaseChange_rationalToComplexLinearEquiv_one_tmul]
    rw [hu v hv]
    simp
  intro w hw
  simpa using hker hw

variable [Module.Finite ℚ Vℚ]

/-- **A polarization splits a rational Hodge substructure off over `ℚ`.** Stated for the
orthogonal complement as a plain subspace; `isCompl_orthogonal` is the same statement for the
rational Hodge substructure `orthogonal P W`, which is only available once the complement has been
shown to be one. -/
private theorem isCompl_orthogonal_WQ :
    IsCompl W.WQ (LinearMap.BilinForm.orthogonal (integralFormBaseChange hℚ P.Qint) W.WQ) := by
  refine (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
    (isRefl_integralFormBaseChange P)).2 ?_
  rw [disjoint_iff]
  have hbot : rationalToComplexSubmodule hℚ hℂ (W.WQ ⊓
      LinearMap.BilinForm.orthogonal (integralFormBaseChange hℚ P.Qint) W.WQ) = ⊥ := by
    refine le_bot_iff.1 ((le_inf ?_ ?_).trans (disjoint_WC_orthogonal P W).le_bot)
    · rw [WC_def]
      exact rationalToComplexSubmodule_mono hℚ hℂ inf_le_left
    · exact (rationalToComplexSubmodule_mono hℚ hℂ inf_le_right).trans
        (rationalToComplexSubmodule_orthogonal_le P W)
  exact (rationalToComplexSubmodule_eq_bot_iff hℚ hℂ _).1 hbot

/-- The complexification of the rational orthogonal complement is a complement of the
complexified substructure. -/
private theorem isCompl_WC_rationalToComplexSubmodule_orthogonal :
    IsCompl W.WC (rationalToComplexSubmodule hℚ hℂ
      (LinearMap.BilinForm.orthogonal (integralFormBaseChange hℚ P.Qint) W.WQ)) := by
  refine ⟨(disjoint_WC_orthogonal P W).mono_right
    (rationalToComplexSubmodule_orthogonal_le P W), ?_⟩
  rw [codisjoint_iff, WC_def, ← rationalToComplexSubmodule_sup,
    (isCompl_orthogonal_WQ P W).sup_eq_top, rationalToComplexSubmodule_top]

/-- **The orthogonal complement of a rational Hodge substructure is defined over `ℚ`:** the
complexification of the rational orthogonal complement is the complex orthogonal complement. Both
subspaces complement the complexified substructure and one contains the other, so they agree. -/
theorem rationalToComplexSubmodule_orthogonal :
    rationalToComplexSubmodule hℚ hℂ
        (LinearMap.BilinForm.orthogonal (integralFormBaseChange hℚ P.Qint) W.WQ) =
      LinearMap.BilinForm.orthogonal P.Q W.WC :=
  (le_iff_eq_of_codisjoint_of_disjoint
    (isCompl_WC_rationalToComplexSubmodule_orthogonal P W).symm.codisjoint
    (disjoint_WC_orthogonal P W)).1 (rationalToComplexSubmodule_orthogonal_le P W)

/-- **The orthogonal complement of a rational Hodge substructure** for a chosen polarization: the
orthogonal complement of its rational subspace. It is again a rational Hodge substructure, because
its complexification is the complex orthogonal complement, and that is spanned by its intersections
with the Hodge components. -/
noncomputable def orthogonal : RationalHodgeSubstructure hℚ hs where
  WQ := LinearMap.BilinForm.orthogonal (integralFormBaseChange hℚ P.Qint) W.WQ
  hodge_spanning := by
    rw [rationalToComplexSubmodule_orthogonal P W, Polarization.Q_def]
    exact le_antisymm
      (P.isPolarization.orthogonal_le_iSup_inf_piece W.WC_eq_iSup_inf_piece.le)
      (iSup_le fun _ ↦ inf_le_left)

@[simp]
theorem orthogonal_WQ : (orthogonal P W).WQ =
    LinearMap.BilinForm.orthogonal (integralFormBaseChange hℚ P.Qint) W.WQ :=
  (rfl)

@[simp]
theorem orthogonal_WC : (orthogonal P W).WC = LinearMap.BilinForm.orthogonal P.Q W.WC := by
  rw [WC_def, orthogonal_WQ]
  exact rationalToComplexSubmodule_orthogonal P W

/-- **A polarization splits a rational Hodge substructure off**, over `ℚ`. -/
theorem isCompl_orthogonal : IsCompl W.WQ (orthogonal P W).WQ :=
  isCompl_orthogonal_WQ P W

/-- **A polarization splits a rational Hodge substructure off**, after complexification. -/
theorem isCompl_WC_orthogonal_WC : IsCompl W.WC (orthogonal P W).WC := by
  rw [orthogonal_WC, ← rationalToComplexSubmodule_orthogonal P W]
  exact isCompl_WC_rationalToComplexSubmodule_orthogonal P W

/-- The rationalified polarizing form is nondegenerate: only zero is orthogonal to the whole
rational space. -/
theorem integralFormBaseChange_orthogonal_top_eq_bot :
    LinearMap.BilinForm.orthogonal (integralFormBaseChange hℚ P.Qint)
      (⊤ : Submodule ℚ Vℚ) = ⊥ := by
  have h := (isCompl_orthogonal_WQ P (top : RationalHodgeSubstructure hℚ hs)).disjoint
  rw [top_WQ] at h
  exact disjoint_top.1 h.symm

end RationalHodgeSubstructure

/-- **Semisimplicity of polarizable rational Hodge structures.** Every rational Hodge substructure
of a polarizable pure Hodge structure has a complement, both over `ℚ` and after complexification,
orthogonal to it for some polarization. -/
theorem exists_isCompl_of_isPolarizable [Module.Finite ℚ Vℚ] (h : IsPolarizable hℂ hs)
    (W : RationalHodgeSubstructure hℚ hs) :
    ∃ P : Polarization hℂ hs, ∃ W' : RationalHodgeSubstructure hℚ hs,
      IsCompl W.WQ W'.WQ ∧ IsCompl W.WC W'.WC ∧
        ∀ v ∈ W.WC, ∀ w ∈ W'.WC, P.Q v w = 0 := by
  obtain ⟨P⟩ := isPolarizable_iff_nonempty.1 h
  refine ⟨P, RationalHodgeSubstructure.orthogonal P W,
    RationalHodgeSubstructure.isCompl_orthogonal P W,
    RationalHodgeSubstructure.isCompl_WC_orthogonal_WC P W, ?_⟩
  intro v hv w hw
  rw [RationalHodgeSubstructure.orthogonal_WC] at hw
  exact hw v hv

end TauCeti.Hodge
