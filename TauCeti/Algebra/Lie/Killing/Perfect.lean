/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
-- Non-public: these appear only inside proofs, never in the type of an exported declaration.
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# A Lie algebra with nondegenerate Killing form is perfect

A finite-dimensional Lie algebra `L` whose Killing form `κ` is nondegenerate satisfies
`⁅L, L⁆ = L`. The proof is a two-line use of the invariance `κ ⁅x, y⁆ z = κ x ⁅y, z⁆`: a linear
form vanishing on the derived ideal is `κ x` for a unique `x`, and then `κ ⁅x, y⁆ z = κ x ⁅y, z⁆`
vanishes for all `z`, so `x` is central; a central element of a Killing algebra is zero, so the
form is zero and the derived ideal was already everything.

The statement is recorded here in the form its consumers use: an action of `L` that composes to
zero is itself zero (`TauCeti.isTrivial_of_derivedSeries_one_eq_top_of_lie_lie_eq_zero`), which is
what turns a two-step filtration of a module into a trivial action. This is the step that rules
out the degenerate case in the Casimir proof of Weyl's complete reducibility theorem, where a
module `M` with `⁅L, M⁆ ⊆ N` and `N` acted on trivially would otherwise escape the argument.

## Main results

* `TauCeti.derivedSeries_one_eq_top_of_isKilling`: **a Lie algebra with nondegenerate Killing form
  is perfect.**
* `TauCeti.isTrivial_of_derivedSeries_one_eq_top_of_lie_lie_eq_zero`: over a perfect Lie algebra,
  a module on which the action composes to zero is a trivial module.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §5.2, where
  perfectness is deduced from the decomposition of a semisimple Lie algebra into simple ideals;
  the argument here uses only the nondegeneracy and the invariance of the Killing form.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module

section Killing

variable (K L : Type*) [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [LieAlgebra.IsKilling K L]

/-- **A Lie algebra with nondegenerate Killing form is perfect**: `⁅L, L⁆ = L`.

A linear form killing the derived ideal is `κ x` for some `x`, by nondegeneracy of the Killing
form on a finite-dimensional space. Invariance turns `κ x ⁅y, z⁆ = 0` into `κ ⁅x, y⁆ z = 0` for
all `z`, so `⁅x, y⁆ = 0` for every `y`; then `ad x = 0`, so `κ x` vanishes identically and `x = 0`.
The linear form was therefore zero, which contradicts the properness of the derived ideal. -/
theorem derivedSeries_one_eq_top_of_isKilling : derivedSeries K L 1 = ⊤ := by
  by_contra hne
  have hlt : (derivedSeries K L 1).toSubmodule < ⊤ := by
    refine lt_of_le_of_ne le_top fun hcon ↦ hne ?_
    exact (LieSubmodule.toSubmodule_inj (derivedSeries K L 1) ⊤).1
      (by rw [hcon, LieSubmodule.top_toSubmodule])
  obtain ⟨φ, hφ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hvanish (y z : L) : φ ⁅y, z⁆ = 0 := by
    have hmem : ⁅y, z⁆ ∈ (derivedSeries K L 1).toSubmodule := by
      rw [← LieIdeal.toLieSubalgebra_toSubmodule, LieAlgebra.coe_derivedSeries_one_eq]
      exact Submodule.subset_span ⟨y, z, rfl⟩
    have := Submodule.mem_map_of_mem (f := φ) hmem
    rw [hmap] at this
    simpa using this
  have hnd := LieAlgebra.IsKilling.killingForm_nondegenerate K L
  obtain ⟨x, hx⟩ : ∃ x : L, ∀ y, killingForm K L x y = φ y :=
    ⟨(killingForm K L).toDual hnd |>.symm φ, fun y ↦
      LinearMap.BilinForm.apply_toDual_symm_apply φ y⟩
  have hcentral (y : L) : ⁅x, y⁆ = 0 := by
    refine hnd.1 _ fun z ↦ ?_
    rw [LieModule.traceForm_apply_lie_apply K L L x y z, hx, hvanish]
  have hx0 : x = 0 := by
    refine hnd.1 _ fun y ↦ ?_
    have had : LieModule.toEnd K L L x = 0 := by
      ext y
      simpa using hcentral y
    rw [LieModule.traceForm_apply_apply, had]
    simp
  exact hφ (by ext y; rw [← hx, hx0]; simp)

end Killing

section Perfect

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
variable {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- **Over a perfect Lie algebra an action that composes to zero is zero.** Each bracket `⁅y, z⁆`
acts as a composite of two actions by the Leibniz rule, hence by zero, and the brackets span a
perfect Lie algebra. -/
theorem isTrivial_of_derivedSeries_one_eq_top_of_lie_lie_eq_zero (hL : derivedSeries K L 1 = ⊤)
    (h : ∀ (x y : L) (m : M), ⁅x, ⁅y, m⁆⁆ = 0) : LieModule.IsTrivial L M := by
  refine ⟨fun {x m} ↦ ?_⟩
  have hbracket (y z : L) : ⁅⁅y, z⁆, m⁆ = 0 := by rw [lie_lie, h, h, sub_zero]
  have hspan : (derivedSeries K L 1).toSubmodule
      = Submodule.span K {b | ∃ y z : L, ⁅y, z⁆ = b} := by
    rw [← LieIdeal.toLieSubalgebra_toSubmodule]
    exact LieAlgebra.coe_derivedSeries_one_eq K L
  have hx : x ∈ Submodule.span K {b | ∃ y z : L, ⁅y, z⁆ = b} := by
    rw [← hspan]
    exact hL ▸ LieSubmodule.mem_top x
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, z, rfl⟩ := hu
    exact hbracket y z
  | zero => rw [zero_lie]
  | add u v _ _ hu hv => rw [add_lie, hu, hv, add_zero]
  | smul t u _ hu => rw [smul_lie, hu, smul_zero]

end Perfect

end TauCeti
