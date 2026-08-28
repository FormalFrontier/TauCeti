/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.BaseChange
public import TauCeti.Geometry.Hodge.Substructure

/-!
# Rational substructures of pure Hodge structures

A rational Hodge substructure is a rational subspace whose complexification is spanned by its
intersections with the Hodge components. This file packages that condition and equips the
complexified subspace with the pure Hodge structure it inherits from the ambient one, so that the
whole `HodgeStructureOn` API applies to it — in particular the Hodge decomposition of the
complexified subspace into its own components is `HodgeStructureOn.isInternal_piece`, not a second
copy of that argument.

Conjugation stability of the complexification is not a field of the structure: it holds for every
rational subspace, by `rationalToComplexSubmodule_conj`. Together with the spanning condition this
exhibits the complexification as a sub-Hodge structure in the sense of
`TauCeti.Hodge.HodgeStructureOn.IsSubstructure`, and the induced conjugation, filtration and
components are read off from that general construction.

The definition and its base-change interface are those specified in Layer L1 of
`TauCetiRoadmap/HodgeStructures/README.md`, following Voisin, *Hodge Theory and Complex Algebraic
Geometry I*, §7.1.2. The induced structure is what makes a rational Hodge substructure a subobject
of a Hodge structure, as the semisimplicity milestone of that layer requires.

The signatures of `RationalHodgeSubstructure` and `RationalHodgeSubstructure.WC` are adapted from
the roadmap's formal companion
[`HodgeStructures/Suggested.lean`](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/HodgeStructures/Suggested.lean).

## Main declarations

* `TauCeti.Hodge.RationalHodgeSubstructure`: a rational subspace split by the Hodge components.
* `TauCeti.Hodge.RationalHodgeSubstructure.isSubstructure`: its complexification is a sub-Hodge
  structure of the ambient pure Hodge structure, so
  `TauCeti.Hodge.HodgeStructureOn.IsSubstructure.hodgeStructure` equips it with the induced pure
  Hodge structure, whose Hodge components are the intersections with the ambient ones.
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

/-- The complexification of a rational Hodge substructure is a sub-Hodge structure of the ambient
pure Hodge structure: it is conjugation stable because it is rational, and spanned by its
intersections with the Hodge components by definition. The induced pure Hodge structure is
`TauCeti.Hodge.HodgeStructureOn.IsSubstructure.hodgeStructure`. -/
theorem isSubstructure (W : RationalHodgeSubstructure hℚ hs) : hs.IsSubstructure W.WC :=
  ⟨fun _ hx ↦ by
    simpa only [latticeConjugation_toEquiv_apply] using W.conj_mem_WC hx,
    le_of_eq W.WC_eq_iSup_inf_piece⟩

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
