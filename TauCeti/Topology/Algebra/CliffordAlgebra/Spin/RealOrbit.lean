/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.RealOrbit
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
import TauCeti.GroupTheory.GroupAction.Transitive

/-!
# Continuous orbits of compact real Spin groups

The compact real Spin action gives a continuous surjection onto the unit level set of its
positive-definite quadratic form, and identifies that level with the quotient by a point
stabilizer. This is the sphere-orbit input for proving connectivity of `Spin(n)`.
-/

public section

namespace CliffordAlgebra

open TauCeti

noncomputable section

/-- The orbit map of the compact real Spin group through a point of its unit level set. -/
noncomputable def realCliffordSpinOrbitMap (n : ℕ) (x : realCliffordUnitLevel n) :
    C(realCliffordSpinGroupZero n, realCliffordUnitLevel n) where
  toFun s := s • x
  continuous_toFun := by
    apply Continuous.subtype_mk ?_ _
    simpa only [SubMulAction.val_smul, realCliffordSpinGroupZero_smul_apply] using
      continuous_spinVectorAction_apply (realCliffordForm n 0) x

@[simp]
theorem realCliffordSpinOrbitMap_apply (n : ℕ) (x : realCliffordUnitLevel n)
    (s : realCliffordSpinGroupZero n) :
    (realCliffordSpinOrbitMap n x s : Fin n → ℝ) =
      spinVectorAction (realCliffordForm n 0) s x := by
  simp only [realCliffordSpinOrbitMap, ContinuousMap.coe_mk, SubMulAction.val_smul,
    realCliffordSpinGroupZero_smul_apply]

/-- The compact real Spin orbit map is onto the unit level set in dimension at least two. -/
theorem realCliffordSpinOrbitMap_surjective (n : ℕ) (hn : 2 ≤ n)
    (x : realCliffordUnitLevel n) : Function.Surjective (realCliffordSpinOrbitMap n x) := by
  have h := @MulAction.surjective_smul _ _ _
    (realCliffordUnitLevel_isPretransitive n hn) x
  simpa only [realCliffordSpinOrbitMap, ContinuousMap.coe_mk] using h

/-- The homogeneous-space description of the unit level under the compact real Spin action. -/
noncomputable def realCliffordSpinStabilizerQuotientEquiv
    (n : ℕ) (hn : 2 ≤ n) (x : realCliffordUnitLevel n) :
    realCliffordSpinGroupZero n ⧸ MulAction.stabilizer _ x ≃ realCliffordUnitLevel n := by
  exact @quotientStabilizerEquiv _ _ _ _
    (realCliffordUnitLevel_isPretransitive n hn) x

@[simp]
theorem realCliffordSpinStabilizerQuotientEquiv_mk
    (n : ℕ) (hn : 2 ≤ n) (x : realCliffordUnitLevel n)
    (s : realCliffordSpinGroupZero n) :
    realCliffordSpinStabilizerQuotientEquiv n hn x (QuotientGroup.mk s) = s • x := by
  rw [realCliffordSpinStabilizerQuotientEquiv]
  exact @quotientStabilizerEquiv_mk _ _ _ _
    (realCliffordUnitLevel_isPretransitive n hn) x s

theorem realCliffordSpinStabilizerQuotientEquiv_smul
    (n : ℕ) (hn : 2 ≤ n) (x : realCliffordUnitLevel n)
    (s : realCliffordSpinGroupZero n)
    (q : realCliffordSpinGroupZero n ⧸ MulAction.stabilizer _ x) :
    realCliffordSpinStabilizerQuotientEquiv n hn x (s • q) =
      s • realCliffordSpinStabilizerQuotientEquiv n hn x q := by
  rw [realCliffordSpinStabilizerQuotientEquiv]
  exact @quotientStabilizerEquiv_smul _ _ _ _
    (realCliffordUnitLevel_isPretransitive n hn) x s q

end

end CliffordAlgebra
