/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Hodge.Conjugation

/-!
# Pure Hodge structures

This file defines a pure Hodge structure of arbitrary integral weight on a complex vector space
with a specified conjugation. The primary datum is a bounded decreasing filtration `F`; purity is
the condition that `F p` and the conjugate of `F (n + 1 - p)` are complementary for every `p`.

Keeping the ambient conjugation as a parameter gives one definition for both integral and rational
Hodge structures. `TauCeti.Hodge.HodgeStructure` specializes it to an abstract complexification of
an integral module using the canonical lattice-induced conjugation. Finiteness and freeness of a
lattice are imposed by the arithmetic results that use them, rather than being redundant parameters
of this abbreviation.

The opposed-filtration convention follows Deligne, *Théorie de Hodge II*, §1.2.1. It is the
convention fixed by the Hodge structures roadmap and by the `#mathlib4` discussion
*Complexifications with a view towards Hodge theory* involving Johan Commelin, Andrew Yang, Kevin
Buzzard, and Joël Riou.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn`: a bounded `n`-opposed decreasing filtration on a complex
  vector space with conjugation.
* `TauCeti.Hodge.HodgeStructure`: the specialization to the canonical conjugation of an integral
  complexification.
* `TauCeti.Hodge.HodgeStructureOn.piece`: the Hodge component `H^{p,n-p}`.
* `TauCeti.Hodge.HodgeStructureOn.conj_piece`: conjugation exchanges `H^{p,n-p}` and
  `H^{n-p,p}`.
* `TauCeti.Hodge.HodgeStructureOn.IsEffective`: the filtration is supported in bidegrees with
  both indices nonnegative.
-/

public section

namespace TauCeti.Hodge

universe u v

/-- A pure Hodge structure of weight `n` on a complex vector space with conjugation `ω`.

The decreasing filtration `F` is bounded and `n`-opposed to its conjugate: for every `p`,
`F p` is complementary to the conjugate of `F (n + 1 - p)`. -/
@[ext]
structure HodgeStructureOn (W : Type u) [AddCommGroup W] [Module ℂ W]
    (ω : Conjugation W) (n : ℤ) where
  /-- The decreasing Hodge filtration. -/
  F : ℤ → Submodule ℂ W
  /-- The Hodge filtration is decreasing. -/
  F_antitone : Antitone F
  /-- The filtration is exhaustive: some step is the whole space. -/
  F_top : ∃ p, F p = ⊤
  /-- The filtration is separated: some step is zero. -/
  F_bot : ∃ p, F p = ⊥
  /-- The filtration is opposed to its conjugate in weight `n`. -/
  opposed : ∀ p, IsCompl (F p) ((F (n + 1 - p)).map ω.toEquiv.toLinearMap)

/-- A pure integral Hodge structure expressed in an arbitrary abstract complexification. Its
conjugation is induced canonically by the integral module. Arithmetic results impose finite
freeness on that module when they need it. -/
abbrev HodgeStructure {V : Type u} {Vℂ : Type v} [AddCommGroup V]
    [AddCommGroup Vℂ] [Module ℂ Vℂ] {ιℂ : V →ₗ[ℤ] Vℂ}
    (hℂ : IsBaseChange ℂ ιℂ) (n : ℤ) :=
  HodgeStructureOn Vℂ (latticeConjugation hℂ) n

namespace HodgeStructureOn

variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable {ω : Conjugation W} {n : ℤ}

/-- The conjugate of the `p`-th step of the Hodge filtration. -/
noncomputable def conjF (hs : HodgeStructureOn W ω n) (p : ℤ) : Submodule ℂ W :=
  (hs.F p).map ω.toEquiv.toLinearMap

/-- The conjugate filtration step is the image under the specified conjugation. -/
theorem conjF_def (hs : HodgeStructureOn W ω n) (p : ℤ) :
    hs.conjF p = (hs.F p).map ω.toEquiv.toLinearMap :=
  (rfl)

/-- Conjugating a filtration step twice recovers that step. -/
@[simp]
theorem conjF_conjF (hs : HodgeStructureOn W ω n) (p : ℤ) :
    (hs.conjF p).map ω.toEquiv.toLinearMap = hs.F p := by
  exact ω.map_map_eq_self (hs.F p)

/-- Opposedness expressed using `conjF`. -/
theorem isCompl_F_conjF (hs : HodgeStructureOn W ω n) (p : ℤ) :
    IsCompl (hs.F p) (hs.conjF (n + 1 - p)) := by
  exact hs.opposed p

/-- At every index below a top step, the decreasing filtration is also the whole space. -/
theorem F_eq_top_of_le (hs : HodgeStructureOn W ω n) {p q : ℤ}
    (hq : hs.F q = ⊤) (hpq : p ≤ q) : hs.F p = ⊤ := by
  apply top_unique
  rw [← hq]
  exact hs.F_antitone hpq

/-- At every index above a bottom step, the decreasing filtration is also zero. -/
theorem F_eq_bot_of_le (hs : HodgeStructureOn W ω n) {p q : ℤ}
    (hp : hs.F p = ⊥) (hpq : p ≤ q) : hs.F q = ⊥ := by
  apply bot_unique
  rw [← hp]
  exact hs.F_antitone hpq

/-- Exhaustiveness holds uniformly below a suitable filtration index. -/
theorem exists_forall_le_F_eq_top (hs : HodgeStructureOn W ω n) :
    ∃ q, ∀ p ≤ q, hs.F p = ⊤ := by
  obtain ⟨q, hq⟩ := hs.F_top
  exact ⟨q, fun _ hpq ↦ hs.F_eq_top_of_le hq hpq⟩

/-- Separatedness holds uniformly above a suitable filtration index. -/
theorem exists_forall_F_eq_bot_of_le (hs : HodgeStructureOn W ω n) :
    ∃ p, ∀ q, p ≤ q → hs.F q = ⊥ := by
  obtain ⟨p, hp⟩ := hs.F_bot
  exact ⟨p, fun _ hpq ↦ hs.F_eq_bot_of_le hp hpq⟩

/-- The Hodge component `H^{p,n-p} = F^p ∩ overline{F^{n-p}}`. -/
noncomputable def piece (hs : HodgeStructureOn W ω n) (p : ℤ) : Submodule ℂ W :=
  hs.F p ⊓ hs.conjF (n - p)

/-- The `p`-th Hodge component is the intersection of `F p` with the conjugate of
`F (n - p)`. -/
theorem piece_def (hs : HodgeStructureOn W ω n) (p : ℤ) :
    hs.piece p = hs.F p ⊓ hs.conjF (n - p) :=
  (rfl)

/-- A Hodge component lies in its corresponding filtration step. -/
theorem piece_le_F (hs : HodgeStructureOn W ω n) (p : ℤ) : hs.piece p ≤ hs.F p :=
  inf_le_left

/-- A Hodge component lies in the conjugate filtration step of complementary index. -/
theorem piece_le_conjF (hs : HodgeStructureOn W ω n) (p : ℤ) :
    hs.piece p ≤ hs.conjF (n - p) :=
  inf_le_right

/-- Conjugation exchanges the Hodge components `H^{p,n-p}` and `H^{n-p,p}`. -/
@[simp]
theorem conj_piece (hs : HodgeStructureOn W ω n) (p : ℤ) :
    (hs.piece p).map ω.toEquiv.toLinearMap = hs.piece (n - p) := by
  rw [piece_def, Submodule.map_inf _ ω.toEquiv.injective, conjF_def, ω.map_map_eq_self,
    piece_def, conjF_def, sub_sub_cancel, inf_comm]

/-- A weight-`n` Hodge structure is effective when its Hodge filtration begins at `F 0 = ⊤`
and ends at `F (n + 1) = ⊥`. Equivalently, its Hodge components can occur only when both
bidegrees are nonnegative. -/
def IsEffective (hs : HodgeStructureOn W ω n) : Prop :=
  hs.F 0 = ⊤ ∧ hs.F (n + 1) = ⊥

/-- Effectivity is exactly the conjunction of the two endpoint conditions. -/
theorem isEffective_iff (hs : HodgeStructureOn W ω n) :
    hs.IsEffective ↔ hs.F 0 = ⊤ ∧ hs.F (n + 1) = ⊥ :=
  Iff.rfl

/-- An effective Hodge filtration is the whole space in every nonpositive degree. -/
theorem IsEffective.F_eq_top_of_nonpos {hs : HodgeStructureOn W ω n}
    (h : hs.IsEffective) {p : ℤ} (hp : p ≤ 0) : hs.F p = ⊤ :=
  hs.F_eq_top_of_le h.1 hp

/-- An effective Hodge filtration vanishes in every degree strictly above its weight. -/
theorem IsEffective.F_eq_bot_of_weight_lt {hs : HodgeStructureOn W ω n}
    (h : hs.IsEffective) {p : ℤ} (hp : n < p) : hs.F p = ⊥ := by
  exact hs.F_eq_bot_of_le h.2 (by omega)

/-- In an effective Hodge structure, a component with negative first index vanishes. -/
theorem IsEffective.piece_eq_bot_of_neg {hs : HodgeStructureOn W ω n}
    (h : hs.IsEffective) {p : ℤ} (hp : p < 0) : hs.piece p = ⊥ := by
  rw [piece_def, h.F_eq_top_of_nonpos hp.le, top_inf_eq]
  rw [conjF_def, h.F_eq_bot_of_weight_lt (by omega), Submodule.map_bot]

/-- In an effective Hodge structure, a component with first index above the weight vanishes. -/
theorem IsEffective.piece_eq_bot_of_weight_lt {hs : HodgeStructureOn W ω n}
    (h : hs.IsEffective) {p : ℤ} (hp : n < p) : hs.piece p = ⊥ := by
  rw [piece_def, h.F_eq_bot_of_weight_lt hp, bot_inf_eq]

end HodgeStructureOn

end TauCeti.Hodge
