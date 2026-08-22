/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Decomposition
public import TauCeti.LinearAlgebra.Dimension.BaseChange
public import TauCeti.LinearAlgebra.Dimension.DirectSum
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Hodge numbers

The `p`-th **Hodge number** of a weight-`n` Hodge structure is the dimension
`h^{p,n-p} = dim_ℂ H^{p,n-p}` of its `p`-th Hodge component. This file records the two facts that
make the family of Hodge numbers a numerical invariant of the structure:

* **Hodge symmetry**, `h^{p,q} = h^{q,p}`: the conjugation carries `H^{p,n-p}` onto `H^{n-p,p}`.
  It is only conjugate-linear, so it is not an isomorphism of complex vector spaces; it is an
  isomorphism of the underlying *real* vector spaces, and the two dimensions over `ℂ` are both
  half of the common dimension over `ℝ`.
* **The Hodge numbers partition the dimension**, `∑ᶠ p, h^{p,n-p} = dim_ℂ V_ℂ`: only finitely many
  Hodge components are nonzero because the filtration is bounded, and they decompose `V_ℂ` as an
  internal direct sum.

For a Hodge structure carried on a lattice, `dim_ℂ V_ℂ` is in turn the rank of the lattice.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.hodgeNumber`: the Hodge number `h^{p,n-p}`.
* `TauCeti.Hodge.HodgeStructureOn.finite_setOf_piece_ne_bot`: only finitely many Hodge components
  are nonzero.
* `TauCeti.Hodge.HodgeStructureOn.pieceConjEquiv`: conjugation as a real-linear isomorphism between
  conjugate Hodge components.
* `TauCeti.Hodge.HodgeStructureOn.hodgeNumber_symm`: Hodge symmetry.
* `TauCeti.Hodge.HodgeStructureOn.finsum_hodgeNumber`: the Hodge numbers sum to the dimension.
* `TauCeti.Hodge.finrank_complexification`: the complexification of a lattice has the rank of the
  lattice as its complex dimension.
* `TauCeti.Hodge.finsum_hodgeNumber_eq_finrank_lattice`: the Hodge numbers of a Hodge structure
  carried on a lattice sum to the rank of that lattice.

Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §6, and Peters–Steenbrink, *Mixed Hodge
Structures*, §2. This is the numerical layer of Layer L3 of
`TauCetiRoadmap/HodgeStructures/README.md`.
-/

public section

namespace TauCeti.Hodge

universe u v

namespace HodgeStructureOn

variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable {ω : Conjugation W} {n : ℤ}

/-- The `p`-th **Hodge number** `h^{p,n-p}` of a weight-`n` Hodge structure: the complex dimension
of its `p`-th Hodge component.

This follows the convention of `Module.finrank`, so an infinite-dimensional component has Hodge
number `0`; the statements that read the Hodge numbers as a dimension count, such as
`finsum_hodgeNumber`, therefore assume the ambient space is finite-dimensional. -/
noncomputable def hodgeNumber (hs : HodgeStructureOn W ω n) (p : ℤ) : ℕ :=
  Module.finrank ℂ (hs.piece p)

/-- The Hodge number is the dimension of the Hodge component. -/
theorem hodgeNumber_def (hs : HodgeStructureOn W ω n) (p : ℤ) :
    hs.hodgeNumber p = Module.finrank ℂ (hs.piece p) :=
  (rfl)

/-- Below a filtration index at which a Hodge filtration is the whole space, every Hodge component
vanishes: the conjugate step cutting it out is already zero. -/
theorem piece_eq_bot_of_F_eq_top (hs : HodgeStructureOn W ω n) {a p : ℤ} (ha : hs.F a = ⊤)
    (hp : p < a) : hs.piece p = ⊥ := by
  have hbot : hs.conjF (n + 1 - a) = ⊥ := by
    apply eq_bot_of_top_isCompl
    simpa only [ha] using hs.isCompl_F_conjF a
  have hle : hs.conjF (n - p) ≤ hs.conjF (n + 1 - a) := hs.conjF_antitone (by omega)
  rw [piece_def, le_bot_iff.1 (hle.trans_eq hbot), inf_bot_eq]

/-- Above a filtration index at which a Hodge filtration vanishes, every Hodge component
vanishes. -/
theorem piece_eq_bot_of_F_eq_bot (hs : HodgeStructureOn W ω n) {b p : ℤ} (hb : hs.F b = ⊥)
    (hp : b ≤ p) : hs.piece p = ⊥ := by
  rw [piece_def, hs.F_eq_bot_of_le hb hp, bot_inf_eq]

/-- A bounded Hodge filtration has only finitely many nonzero Hodge components. -/
theorem finite_setOf_piece_ne_bot (hs : HodgeStructureOn W ω n) :
    {p | hs.piece p ≠ ⊥}.Finite := by
  obtain ⟨a, ha⟩ := hs.F_top
  obtain ⟨b, hb⟩ := hs.F_bot
  refine (Set.finite_Ico a b).subset fun p hp ↦ ?_
  refine ⟨?_, ?_⟩
  · by_contra hpa
    exact hp (hs.piece_eq_bot_of_F_eq_top ha (by omega))
  · by_contra hpb
    exact hp (hs.piece_eq_bot_of_F_eq_bot hb (by omega))

/-- Only finitely many Hodge numbers are nonzero. -/
theorem finite_setOf_hodgeNumber_ne_zero (hs : HodgeStructureOn W ω n) :
    {p | hs.hodgeNumber p ≠ 0}.Finite := by
  refine hs.finite_setOf_piece_ne_bot.subset fun p hp hbot ↦ hp ?_
  change Module.finrank ℂ (hs.piece p) = 0
  rw [hbot, finrank_bot]

/-- Conjugation restricts to a **real**-linear isomorphism from the Hodge component `H^{p,n-p}`
onto its conjugate `H^{n-p,p}`. It is not complex-linear: it is conjugate-linear, so it is only an
isomorphism after restricting scalars to `ℝ`. -/
def pieceConjEquiv (hs : HodgeStructureOn W ω n) (p : ℤ) :
    hs.piece p ≃ₗ[ℝ] hs.piece (n - p) where
  toFun x := ⟨ω.toEquiv x, hs.conj_mem_piece x.2⟩
  invFun y := ⟨ω.toEquiv y, by simpa only [sub_sub_cancel] using hs.conj_mem_piece y.2⟩
  map_add' x y := by ext; exact map_add _ _ _
  map_smul' r x := by
    ext
    change ω.toEquiv ((r : ℂ) • (x : W)) = (r : ℂ) • ω.toEquiv (x : W)
    rw [ω.toEquiv.map_smulₛₗ, Complex.conj_ofReal]
  left_inv x := by ext; exact ω.apply_apply _
  right_inv y := by ext; exact ω.apply_apply _

@[simp]
theorem coe_pieceConjEquiv (hs : HodgeStructureOn W ω n) (p : ℤ) (x : hs.piece p) :
    (hs.pieceConjEquiv p x : W) = ω.toEquiv x :=
  (rfl)

/-- **Hodge symmetry**: `h^{p,q} = h^{q,p}`, where `q = n - p`. -/
theorem hodgeNumber_symm (hs : HodgeStructureOn W ω n) (p : ℤ) :
    hs.hodgeNumber p = hs.hodgeNumber (n - p) := by
  have h := (hs.pieceConjEquiv p).finrank_eq
  rw [finrank_real_of_complex, finrank_real_of_complex] at h
  simp only [hodgeNumber_def]
  omega

/-- **The Hodge numbers partition the dimension**: the Hodge numbers of a weight-`n` Hodge
structure on a finite-dimensional complex vector space sum to its dimension. -/
theorem finsum_hodgeNumber (hs : HodgeStructureOn W ω n) [FiniteDimensional ℂ W] :
    ∑ᶠ p, hs.hodgeNumber p = Module.finrank ℂ W :=
  finsum_finrank_eq_finrank_of_isInternal hs.isInternal_piece hs.finite_setOf_piece_ne_bot

end HodgeStructureOn

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- A complexification of a finitely generated lattice is a finite-dimensional complex vector
space. -/
theorem finiteDimensional_complexification [Module.Finite ℤ V] (hℂ : IsBaseChange ℂ ιℂ) :
    FiniteDimensional ℂ Vℂ :=
  finite_of_isBaseChange hℂ

/-- A complexification of a free lattice has the rank of that lattice as its complex dimension. -/
theorem finrank_complexification [Module.Free ℤ V] (hℂ : IsBaseChange ℂ ιℂ) :
    Module.finrank ℂ Vℂ = Module.finrank ℤ V :=
  finrank_of_isBaseChange hℂ

/-- **The Hodge numbers of a Hodge structure on a lattice partition the rank of the lattice.** -/
theorem finsum_hodgeNumber_eq_finrank_lattice [Module.Free ℤ V] [Module.Finite ℤ V]
    {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ} (hs : HodgeStructure hℂ n) :
    ∑ᶠ p, hs.hodgeNumber p = Module.finrank ℤ V := by
  have := finiteDimensional_complexification (V := V) hℂ
  rw [HodgeStructureOn.finsum_hodgeNumber hs, finrank_complexification hℂ]

end TauCeti.Hodge
