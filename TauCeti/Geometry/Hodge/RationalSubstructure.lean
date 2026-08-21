/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.BaseChange
public import TauCeti.Geometry.Hodge.Decomposition
public import TauCeti.LinearAlgebra.Submodule.Compl

/-!
# Rational substructures of pure Hodge structures

A rational Hodge substructure is a rational subspace whose complexification is spanned by its
intersections with the Hodge components. This file packages that condition and equips the
complexified subspace with the pure Hodge structure it inherits from the ambient one, so that the
whole `HodgeStructureOn` API applies to it — in particular the Hodge decomposition of the
complexified subspace into its own components is `HodgeStructureOn.isInternal_piece`, not a second
copy of that argument.

Conjugation stability of the complexification is not a field of the structure: it holds for every
rational subspace, by `rationalToComplexSubmodule_conj`, so the ambient conjugation restricts to
the complexification and supplies the conjugation of the induced structure.

The definition and its base-change interface are those specified in Layer L1 of
`TauCetiRoadmap/HodgeStructures/README.md`, following Voisin, *Hodge Theory and Complex Algebraic
Geometry I*, §7.1.2. The induced structure is what makes a rational Hodge substructure a subobject
of a Hodge structure, as the semisimplicity milestone of that layer requires.

The signatures of `RationalHodgeSubstructure` and `RationalHodgeSubstructure.WC` are adapted from
the roadmap's formal companion
[`HodgeStructures/Suggested.lean`](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/HodgeStructures/Suggested.lean).

## Main declarations

* `TauCeti.Hodge.RationalHodgeSubstructure`: a rational subspace split by the Hodge components.
* `TauCeti.Hodge.RationalHodgeSubstructure.conjugation`: the conjugation induced on its
  complexification.
* `TauCeti.Hodge.RationalHodgeSubstructure.hodgeStructure`: the pure Hodge structure induced on its
  complexification, whose Hodge components are the intersections with the ambient ones.
-/

public section

namespace TauCeti.Hodge

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ]
variable [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {n : ℤ} {hs : HodgeStructure hℂ n}

/-- A rational Hodge substructure of a pure Hodge structure.

Its rational subspace `WQ` complexifies to the sum of its intersections with the Hodge
components. Stability under conjugation is not a field: it follows from rationality via
`rationalToComplexSubmodule_conj`. -/
@[ext]
structure RationalHodgeSubstructure (hℚ : IsBaseChange ℚ ιℚ) (hs : HodgeStructure hℂ n) where
  /-- The underlying rational subspace. -/
  WQ : Submodule ℚ Vℚ
  /-- The complexification is spanned by its intersections with the Hodge components. -/
  hodge_spanning : rationalToComplexSubmodule hℚ hℂ WQ =
    ⨆ p, rationalToComplexSubmodule hℚ hℂ WQ ⊓ hs.piece p

namespace RationalHodgeSubstructure

/-- The complexification of a rational Hodge substructure inside the ambient complexification. -/
noncomputable def WC (W : RationalHodgeSubstructure hℚ hs) : Submodule ℂ Vℂ :=
  rationalToComplexSubmodule hℚ hℂ W.WQ

/-- The complexification of a rational Hodge substructure is the complexification of its rational
subspace. -/
theorem WC_def (W : RationalHodgeSubstructure hℚ hs) :
    W.WC = rationalToComplexSubmodule hℚ hℂ W.WQ :=
  (rfl)

/-- The complexification is the supremum of its intersections with the ambient Hodge
components. -/
theorem WC_eq_iSup_inf_piece (W : RationalHodgeSubstructure hℚ hs) :
    W.WC = ⨆ p, W.WC ⊓ hs.piece p :=
  W.hodge_spanning

/-- The complexification of a rational Hodge substructure is stable under conjugation. -/
@[simp]
theorem map_WC_conj (W : RationalHodgeSubstructure hℚ hs) :
    W.WC.map (latticeConjugation hℂ).toEquiv.toLinearMap = W.WC := by
  rw [latticeConjugation_toLinearMap, WC_def]
  exact rationalToComplexSubmodule_conj hℚ hℂ W.WQ

/-- Conjugation carries every vector of a rational Hodge substructure back into its
complexification. -/
theorem conj_mem_WC (W : RationalHodgeSubstructure hℚ hs) {x : Vℂ} (hx : x ∈ W.WC) :
    (latticeConjugation hℂ).toEquiv x ∈ W.WC := by
  rw [← W.map_WC_conj]
  exact Submodule.mem_map_of_mem hx

/-- The conjugation induced on the complexification of a rational Hodge substructure. -/
noncomputable def conjugation (W : RationalHodgeSubstructure hℚ hs) : Conjugation W.WC :=
  (latticeConjugation hℂ).restrict fun _ hx ↦ W.conj_mem_WC hx

/-- The induced conjugation acts as the ambient lattice conjugation. -/
@[simp]
theorem conjugation_toEquiv_apply (W : RationalHodgeSubstructure hℚ hs) (x : W.WC) :
    (W.conjugation.toEquiv x : Vℂ) = latticeConj hℂ x := by
  simp [conjugation]

/-- Conjugating inside the complexification is conjugating in the ambient complexification. -/
@[simp]
theorem map_comap_subtype_conjugation (W : RationalHodgeSubstructure hℚ hs)
    (A : Submodule ℂ Vℂ) :
    (A.comap W.WC.subtype).map W.conjugation.toEquiv.toLinearMap =
      (A.map (latticeConjugation hℂ).toEquiv.toLinearMap).comap W.WC.subtype :=
  Conjugation.map_restrict_comap_subtype _ _ _

/-- A filtration step and the complementary conjugate step together cover the complexification:
every ambient Hodge component lies in one of the two. -/
theorem WC_le_inf_F_sup_inf_conjF (W : RationalHodgeSubstructure hℚ hs) (p : ℤ) :
    W.WC ≤ W.WC ⊓ hs.F p ⊔ W.WC ⊓ hs.conjF (n + 1 - p) := by
  conv_lhs => rw [W.WC_eq_iSup_inf_piece]
  refine iSup_le fun q ↦ ?_
  rcases lt_or_ge q p with hq | hq
  · exact le_sup_of_le_right (inf_le_inf_left _ (hs.piece_le_conjF_of_lt hq))
  · exact le_sup_of_le_left (inf_le_inf_left _ ((hs.piece_le_F q).trans (hs.F_antitone hq)))

/-- The pure Hodge structure induced on the complexification of a rational Hodge substructure: its
filtration is the ambient filtration intersected with the complexification, and it is opposed
because the ambient components cover the complexification. -/
noncomputable def hodgeStructure (W : RationalHodgeSubstructure hℚ hs) :
    HodgeStructureOn W.WC W.conjugation n where
  F p := (hs.F p).comap W.WC.subtype
  F_antitone _ _ hpq := Submodule.comap_mono (hs.F_antitone hpq)
  F_top := by
    obtain ⟨p, hp⟩ := hs.F_top
    exact ⟨p, by rw [hp]; exact Submodule.comap_subtype_eq_top.2 le_top⟩
  opposed p := by
    rw [W.map_comap_subtype_conjugation, ← hs.conjF_def]
    exact TauCeti.Submodule.isCompl_comap_subtype (hs.isCompl_F_conjF p).disjoint
      (W.WC_le_inf_F_sup_inf_conjF p)

/-- The induced Hodge filtration is the ambient filtration intersected with the
complexification. -/
@[simp]
theorem hodgeStructure_F (W : RationalHodgeSubstructure hℚ hs) (p : ℤ) :
    W.hodgeStructure.F p = (hs.F p).comap W.WC.subtype :=
  (rfl)

/-- The induced conjugate filtration is the ambient conjugate filtration intersected with the
complexification. -/
@[simp]
theorem hodgeStructure_conjF (W : RationalHodgeSubstructure hℚ hs) (p : ℤ) :
    W.hodgeStructure.conjF p = (hs.conjF p).comap W.WC.subtype := by
  rw [HodgeStructureOn.conjF_def, hodgeStructure_F, W.map_comap_subtype_conjugation,
    ← hs.conjF_def]

/-- An induced Hodge component is the ambient Hodge component of the same degree intersected with
the complexification. -/
@[simp]
theorem hodgeStructure_piece (W : RationalHodgeSubstructure hℚ hs) (p : ℤ) :
    W.hodgeStructure.piece p = (hs.piece p).comap W.WC.subtype := by
  rw [HodgeStructureOn.piece_def, hodgeStructure_F, hodgeStructure_conjF, hs.piece_def,
    Submodule.comap_inf]

/-- The zero rational subspace is a rational Hodge substructure. -/
noncomputable def bot : RationalHodgeSubstructure hℚ hs where
  WQ := ⊥
  hodge_spanning := by simp

/-- The whole rational space is a rational Hodge substructure. -/
noncomputable def top : RationalHodgeSubstructure hℚ hs where
  WQ := ⊤
  hodge_spanning := by
    simp only [rationalToComplexSubmodule_top, top_inf_eq]
    exact hs.iSup_piece_eq_top.symm

@[simp]
theorem bot_WQ : (bot : RationalHodgeSubstructure hℚ hs).WQ = ⊥ :=
  by rw [bot]

@[simp]
theorem bot_WC : (bot : RationalHodgeSubstructure hℚ hs).WC = ⊥ := by
  rw [WC_def, bot_WQ, rationalToComplexSubmodule_bot]

@[simp]
theorem top_WQ : (top : RationalHodgeSubstructure hℚ hs).WQ = ⊤ :=
  by rw [top]

@[simp]
theorem top_WC : (top : RationalHodgeSubstructure hℚ hs).WC = ⊤ := by
  rw [WC_def, top_WQ, rationalToComplexSubmodule_top]

end RationalHodgeSubstructure

end TauCeti.Hodge
