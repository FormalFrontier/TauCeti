/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.BaseChange
public import TauCeti.Geometry.Hodge.Decomposition

/-!
# Rational substructures of pure Hodge structures

A rational Hodge substructure is a rational subspace whose complexification is the direct sum of
its intersections with the Hodge components. This file packages that condition and derives the
componentwise decomposition of the complexified subspace.

Rationality also makes the complexification stable under the lattice-induced conjugation. This is
proved for every rational subspace before imposing the Hodge condition; a rational Hodge
substructure therefore carries no redundant conjugation-stability field.

The definition and its base-change interface are those specified in Layer L1 of
`TauCetiRoadmap/HodgeStructures/README.md`, following Voisin, *Hodge Theory and Complex Algebraic
Geometry I*, §7.1.2.

The signatures of `rationalToComplexSubmodule_conj`, `RationalHodgeSubstructure`, and `WC` are
adapted from the roadmap's formal companion
[`HodgeStructures/Suggested.lean`](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/HodgeStructures/Suggested.lean).

## Main declarations

* `TauCeti.Hodge.rationalToComplexSubmodule_conj`: complexifications of rational subspaces are
  stable under lattice-induced conjugation.
* `TauCeti.Hodge.RationalHodgeSubstructure`: a rational subspace split by the Hodge components.
* `TauCeti.Hodge.RationalHodgeSubstructure.isInternal_piece`: the induced componentwise direct-sum
  decomposition.
-/

public section

namespace TauCeti.Hodge

open scoped DirectSum TensorProduct

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ]
variable [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}

/-- Conjugation commutes with the canonical map from the rationalification into the
complexification. -/
private theorem latticeConj_rationalToComplexLinearEquiv_one_tmul (x : Vℚ) :
    latticeConj hℂ (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] x)) =
      rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] x) := by
  induction x using hℚ.inductionOn with
  | zero => simp
  | tmul x => simp
  | smul q x hx =>
      have h_tmul : (1 ⊗ₜ[ℚ] (q • x) : ℂ ⊗[ℚ] Vℚ) =
          (q : ℂ) • (1 ⊗ₜ[ℚ] x) := by
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        congr 1
        simp
      calc
        latticeConj hℂ (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] (q • x))) =
            latticeConj hℂ ((q : ℂ) •
              rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] x)) := by
          rw [h_tmul, map_smul]
        _ = starRingEnd ℂ (q : ℂ) • latticeConj hℂ
              (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] x)) := by
          rw [map_smulₛₗ]
        _ = (q : ℂ) • rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] x) := by
          rw [hx]
          simp
        _ = rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] (q • x)) := by
          rw [h_tmul, map_smul]
  | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (fun a b ↦ a + b) hx hy

/-- The complexification of a rational subspace is stable under lattice-induced conjugation. -/
@[simp]
theorem rationalToComplexSubmodule_conj (W : Submodule ℚ Vℚ) :
    (rationalToComplexSubmodule hℚ hℂ W).map (latticeConj hℂ) =
      rationalToComplexSubmodule hℚ hℂ W := by
  have hle : (rationalToComplexSubmodule hℚ hℂ W).map (latticeConj hℂ) ≤
      rationalToComplexSubmodule hℚ hℂ W := by
    rw [rationalToComplexSubmodule_eq_span, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨x, hx, rfl⟩
    rw [latticeConj_rationalToComplexLinearEquiv_one_tmul]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  apply le_antisymm hle
  intro x hx
  refine ⟨latticeConj hℂ x, hle ⟨x, hx, rfl⟩, ?_⟩
  simp

variable {n : ℤ} (hs : HodgeStructure hℂ n)

/-- A rational Hodge substructure of a pure Hodge structure.

Its rational subspace `WQ` complexifies to the sum of its intersections with the Hodge
components. Stability under conjugation is not a field: it follows from rationality via
`rationalToComplexSubmodule_conj`. -/
@[ext]
structure RationalHodgeSubstructure where
  /-- The underlying rational subspace. -/
  WQ : Submodule ℚ Vℚ
  /-- The complexification is spanned by its intersections with the Hodge components. -/
  hodge_spanning : rationalToComplexSubmodule hℚ hℂ WQ =
    ⨆ p, rationalToComplexSubmodule hℚ hℂ WQ ⊓ hs.piece p

namespace RationalHodgeSubstructure

variable {hs}

/-- The complexification of a rational Hodge substructure inside the ambient complexification. -/
noncomputable def WC (W : RationalHodgeSubstructure (hℚ := hℚ) hs) : Submodule ℂ Vℂ :=
  rationalToComplexSubmodule hℚ hℂ W.WQ

/-- The `p`-th Hodge component of a rational Hodge substructure, as a subspace of its
complexification. -/
noncomputable def piece (W : RationalHodgeSubstructure (hℚ := hℚ) hs) (p : ℤ) :
    Submodule ℂ W.WC :=
  (hs.piece p).comap W.WC.subtype

/-- The complexification is the supremum of its intersections with the ambient Hodge
components. -/
theorem WC_eq_iSup_inf_piece (W : RationalHodgeSubstructure (hℚ := hℚ) hs) :
    W.WC = ⨆ p, W.WC ⊓ hs.piece p :=
  W.hodge_spanning

/-- Membership in an induced Hodge component is detected in the ambient space. -/
@[simp]
theorem mem_piece_iff (W : RationalHodgeSubstructure (hℚ := hℚ) hs) (p : ℤ) (x : W.WC) :
    x ∈ W.piece p ↔ (x : Vℂ) ∈ hs.piece p :=
  Iff.rfl

/-- Mapping an induced Hodge component into the ambient space gives the intersection of the
complexification with the corresponding ambient Hodge component. -/
@[simp]
theorem map_piece_subtype (W : RationalHodgeSubstructure (hℚ := hℚ) hs) (p : ℤ) :
    (W.piece p).map W.WC.subtype = W.WC ⊓ hs.piece p := by
  exact Submodule.map_comap_subtype W.WC (hs.piece p)

/-- The complexification of a rational Hodge substructure is stable under conjugation. -/
@[simp]
theorem map_WC_conj (W : RationalHodgeSubstructure (hℚ := hℚ) hs) :
    W.WC.map (latticeConj hℂ) = W.WC :=
  rationalToComplexSubmodule_conj W.WQ

/-- Conjugation carries every vector of a rational Hodge substructure back into its
complexification. -/
theorem conj_mem_WC (W : RationalHodgeSubstructure (hℚ := hℚ) hs) {x : Vℂ} (hx : x ∈ W.WC) :
    latticeConj hℂ x ∈ W.WC := by
  rw [← W.map_WC_conj]
  exact Submodule.mem_map_of_mem hx

/-- Conjugation exchanges the induced Hodge components in complementary degrees. -/
theorem conj_mem_piece (W : RationalHodgeSubstructure (hℚ := hℚ) hs) {p : ℤ} {x : W.WC}
    (hx : x ∈ W.piece p) :
    (⟨latticeConj hℂ x, W.conj_mem_WC x.property⟩ : W.WC) ∈ W.piece (n - p) := by
  rw [W.mem_piece_iff]
  simpa only [latticeConjugation_toEquiv_apply] using
    hs.conj_mem_piece ((W.mem_piece_iff p x).mp hx)

/-- The induced Hodge components span the complexification of a rational Hodge substructure. -/
theorem iSup_piece_eq_top (W : RationalHodgeSubstructure (hℚ := hℚ) hs) :
    ⨆ p, W.piece p = ⊤ := by
  apply Submodule.map_injective_of_injective W.WC.subtype_injective
  rw [Submodule.map_iSup, Submodule.map_subtype_top]
  simp_rw [W.map_piece_subtype]
  exact W.WC_eq_iSup_inf_piece.symm

/-- The induced Hodge components of a rational Hodge substructure are independent. -/
theorem piece_iSupIndep (W : RationalHodgeSubstructure (hℚ := hℚ) hs) : iSupIndep W.piece := by
  have hambient : iSupIndep (fun p ↦ W.WC ⊓ hs.piece p) :=
    hs.piece_iSupIndep.mono fun _ ↦ inf_le_right
  let e : Submodule ℂ W.WC ≃o Set.Iic W.WC := W.WC.mapIic
  let B : ℤ → Set.Iic W.WC := fun p ↦
    ⟨W.WC ⊓ hs.piece p, (inf_le_left : W.WC ⊓ hs.piece p ≤ W.WC)⟩
  have hB : iSupIndep B := by
    apply iSupIndep.of_coe_Iic_comp
    -- `of_coe_Iic_comp` leaves the coercion from the interval visible in the goal.
    change iSupIndep (fun p ↦ W.WC ⊓ hs.piece p)
    exact hambient
  suffices (e ∘ W.piece) = B by
    rw [← iSupIndep_map_orderIso_iff e, this]
    exact hB
  ext p x
  -- `mapIic` represents a submodule of `W.WC` by its image under the subtype map.
  change x ∈ (W.piece p).map W.WC.subtype ↔ x ∈ W.WC ⊓ hs.piece p
  rw [W.map_piece_subtype]

/-- The induced Hodge components form an internal direct sum of the complexification. -/
theorem isInternal_piece (W : RationalHodgeSubstructure (hℚ := hℚ) hs) :
    DirectSum.IsInternal W.piece := by
  classical
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    W.piece_iSupIndep W.iSup_piece_eq_top

/-- The Hodge decomposition of a rational Hodge substructure as a linear equivalence. -/
noncomputable def decomposition (W : RationalHodgeSubstructure (hℚ := hℚ) hs) :
    W.WC ≃ₗ[ℂ] ⨁ p, W.piece p :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap W.piece) W.isInternal_piece).symm

/-- The inverse of the Hodge decomposition sums the induced components. -/
@[simp]
theorem decomposition_symm_apply (W : RationalHodgeSubstructure (hℚ := hℚ) hs)
    (x : ⨁ p, W.piece p) :
    W.decomposition.symm x = DirectSum.coeLinearMap W.piece x := by
  rw [decomposition, LinearEquiv.symm_symm]
  rfl

/-- A vector in one induced Hodge component decomposes as that component alone. -/
theorem decomposition_apply_of_mem
    (W : RationalHodgeSubstructure (hℚ := hℚ) hs) {p : ℤ} {x : W.WC}
    (hx : x ∈ W.piece p) :
    W.decomposition x = DirectSum.lof ℂ ℤ (fun q ↦ W.piece q) p ⟨x, hx⟩ :=
  W.decomposition.symm.injective (by simp)

/-- The zero rational subspace is a rational Hodge substructure. -/
noncomputable def bot : RationalHodgeSubstructure (hℚ := hℚ) hs where
  WQ := ⊥
  hodge_spanning := by simp

/-- The whole rational space is a rational Hodge substructure. -/
noncomputable def top : RationalHodgeSubstructure (hℚ := hℚ) hs where
  WQ := ⊤
  hodge_spanning := by
    simp only [rationalToComplexSubmodule_top, top_inf_eq]
    exact hs.iSup_piece_eq_top.symm

@[simp]
theorem bot_WQ : (bot : RationalHodgeSubstructure (hℚ := hℚ) hs).WQ = ⊥ :=
  by rw [bot]

@[simp]
theorem bot_WC : (bot : RationalHodgeSubstructure (hℚ := hℚ) hs).WC = ⊥ := by
  rw [WC, bot_WQ, rationalToComplexSubmodule_bot]

@[simp]
theorem top_WQ : (top : RationalHodgeSubstructure (hℚ := hℚ) hs).WQ = ⊤ :=
  by rw [top]

@[simp]
theorem top_WC : (top : RationalHodgeSubstructure (hℚ := hℚ) hs).WC = ⊤ := by
  rw [WC, top_WQ, rationalToComplexSubmodule_top]

end RationalHodgeSubstructure

end TauCeti.Hodge
