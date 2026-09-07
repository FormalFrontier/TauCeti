/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonalOrbit

/-!
# Orbits of compact real Spin groups

The compact real Spin group acts transitively on the unit level set of its positive-definite
quadratic form in dimensions `n ≥ 2`. This is the algebraic input for its continuous sphere orbit.

Roadmap: RepresentationTheory — SpinRepresentations Layer 7, “Connectivity of the compact spin
group”. The construction follows Lawson–Michelsohn, *Spin Geometry* (1989), Chapter I, §2, and
reuses the Clifford Spin action and special-orthogonal reflection APIs developed in TauCeti.
-/

public section

namespace CliffordAlgebra

open TauCeti

noncomputable section

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

noncomputable instance instMulActionRealCliffordSpinGroupZero (n : ℕ) :
    MulAction (realCliffordSpinGroupZero n) (Fin n → ℝ) :=
  MulAction.compHom _ (spinToOrthogonal (realCliffordForm n 0))

/-- The compact real Spin action is the usual vector action. -/
@[simp]
theorem realCliffordSpinGroupZero_smul_apply (n : ℕ)
    (s : realCliffordSpinGroupZero n) (x : Fin n → ℝ) :
    s • x = spinVectorAction (realCliffordForm n 0) s x := by
  rw [MulAction.compHom_smul_def]
  exact coe_spinToOrthogonal_apply (realCliffordForm n 0) s x

/-- The unit quadratic level as a subaction of the compact real Spin action. -/
noncomputable def realCliffordUnitLevel (n : ℕ) :
    SubMulAction (realCliffordSpinGroupZero n) (Fin n → ℝ) where
  carrier := {x | realCliffordForm n 0 x = 1}
  smul_mem' s x hx := by
    rw [realCliffordSpinGroupZero_smul_apply]
    exact (spinVectorAction_map_app (realCliffordForm n 0) s x).trans hx

/-- Membership in the unit quadratic level is exactly its defining equation. -/
@[simp]
theorem mem_realCliffordUnitLevel (n : ℕ) (x : Fin n → ℝ) :
    x ∈ realCliffordUnitLevel n ↔ realCliffordForm n 0 x = 1 := by
  rfl


/-- A positive-definite real Spin group acts transitively on every nonzero quadratic level set in
dimension at least two. -/
theorem exists_spinVectorAction_eq_of_posDef (Q : QuadraticForm ℝ V) (hQ : Q.PosDef)
    (hrank : 2 ≤ Module.finrank ℝ V) {x y : V} (hxy : Q x = Q y) (hy : Q y ≠ 0) :
    ∃ s : spinGroup Q, spinVectorAction Q s x = y := by
  obtain ⟨g, hg⟩ := TauCeti.QuadraticMap.exists_specialOrthogonal_map_eq_of_nondegenerate
    Q hQ.anisotropic.nondegenerate hrank hxy hy
  obtain ⟨s, hs⟩ := spinToSpecialOrthogonal_surjective_of_posDef Q hQ g
  refine ⟨s, ?_⟩
  rw [← coe_spinToSpecialOrthogonal_apply]
  simpa only [hs] using hg

/-- The compact real Spin group `Spin(n)` acts transitively on the unit level set when `n ≥ 2`.
-/
theorem exists_realCliffordSpinGroupZero_spinVectorAction_eq (n : ℕ) (hn : 2 ≤ n)
    {x y : Fin n → ℝ}
    (hx : realCliffordForm n 0 x = 1) (hy : realCliffordForm n 0 y = 1) :
    ∃ s : realCliffordSpinGroupZero n,
      spinVectorAction (realCliffordForm n 0) s x = y := by
  apply exists_spinVectorAction_eq_of_posDef _ (posDef_realCliffordForm_zero n)
  · simpa only [Module.finrank_pi, Fintype.card_fin, Module.finrank_self, one_mul,
      Nat.add_zero] using hn
  · exact hx.trans hy.symm
  · simp [hy]

/-- The compact real Spin action on the unit level is transitive in dimension at least two. -/
theorem realCliffordUnitLevel_isPretransitive (n : ℕ) (hn : 2 ≤ n) :
    MulAction.IsPretransitive (realCliffordSpinGroupZero n) (realCliffordUnitLevel n) where
  exists_smul_eq x y := by
    obtain ⟨s, hs⟩ :=
      exists_realCliffordSpinGroupZero_spinVectorAction_eq n hn x.2 y.2
    exact ⟨s, Subtype.ext (by
      simpa only [SubMulAction.val_smul, realCliffordSpinGroupZero_smul_apply] using hs)⟩

end

end CliffordAlgebra
