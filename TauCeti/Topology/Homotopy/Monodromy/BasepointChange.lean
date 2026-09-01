/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
public import TauCeti.Topology.Homotopy.Monodromy.Basic

/-!
# Basepoint change for the subgroup recovered by a cover

Let `p : E → X` be a covering map, let `γ : Path x₀ x₁`, and let `e₀` lie over `x₀`. The
lifted endpoint `hp.monodromy ⟦γ⟧ e₀` lies over `x₁`, and the subgroup recovered from that
pointed lift is the transport of the subgroup recovered from `e₀` along `γ`:

```text
  im (p_* : π₁(E, hp.monodromy ⟦γ⟧ e₀) → π₁(X, x₁))
    = γ_* (im (p_* : π₁(E, e₀) → π₁(X, x₀))).
```

Here `p_*` denotes the induced map on fundamental groups and `γ_*` denotes the
basepoint-change isomorphism induced by `γ`; the displayed equality is an equality of
image subgroups.

The proof combines Mathlib's path-conjugation isomorphism for fundamental groups with its
path-lifting and monodromy API, packaged for recovered subgroups in
`TauCeti.Topology.Homotopy.Monodromy.Basic`. This is the path-level compatibility needed by
the pointed and unpointed parts of Stage 2, items 7 and 8, of
`TauCetiRoadmap/UniversalCovers/README.md`; the convention is the usual one from Hatcher,
*Algebraic Topology*, Section 1.3.
-/

public section

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X} {x₀ x₁ : X}

namespace IsCoveringMap

/-- The subgroup recovered at the endpoint of a lifted path is the basepoint transport of the
subgroup recovered at its starting point. -/
theorem _root_.IsCoveringMap.range_mapOfEq_monodromy_path (hp : IsCoveringMap p) (γ : Path x₀ x₁)
    (e₀ : p ⁻¹' {x₀}) :
    (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩
      (hp.monodromy ⟦γ⟧ e₀).2).range =
      FundamentalGroup.basepointChangeSubgroup γ
        (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e₀.2).range := by
  let γq : Path.Homotopic.Quotient x₀ x₁ := Path.Homotopic.Quotient.mk γ
  let e₁ : p ⁻¹' {x₁} := hp.monodromy γq e₀
  let f := _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ
  have hmon (g : _root_.FundamentalGroup X x₁) :
      hp.monodromy g e₁ = e₁ ↔ hp.monodromy (f.symm g) e₀ = e₀ := by
    -- Expose the local names so that the path-lifting composition laws apply directly.
    change hp.monodromy g (hp.monodromy γq e₀) = hp.monodromy γq e₀ ↔
      hp.monodromy (f.symm g) e₀ = e₀
    have htrans :
        hp.monodromy (Path.Homotopic.Quotient.trans γq g) e₀ =
          hp.monodromy g (hp.monodromy γq e₀) :=
      hp.monodromy_trans_apply γq g e₀
    have hf :
        f.symm g = Path.Homotopic.Quotient.trans γq
          (Path.Homotopic.Quotient.trans g γq.symm) := by
      simpa only [f, γq] using
        _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply γ g
    rw [← htrans]
    rw [hf]
    have hback : hp.monodromy γq.symm (hp.monodromy γq e₀) = e₀ := by
      rw [← hp.monodromy_trans_apply]
      rw [Path.Homotopic.Quotient.trans_symm, hp.monodromy_refl]
      rfl
    have hforward {z : p ⁻¹' {x₁}} :
        hp.monodromy γq (hp.monodromy γq.symm z) = z := by
      rw [← hp.monodromy_trans_apply]
      rw [Path.Homotopic.Quotient.symm_trans, hp.monodromy_refl]
      rfl
    have hcomp :
        hp.monodromy (Path.Homotopic.Quotient.trans γq
          (Path.Homotopic.Quotient.trans g γq.symm)) e₀ =
          hp.monodromy γq.symm (hp.monodromy (Path.Homotopic.Quotient.trans γq g) e₀) := by
      rw [← Path.Homotopic.Quotient.trans_assoc]
      exact hp.monodromy_trans_apply _ _ _
    rw [hcomp]
    constructor
    · intro h
      rw [h, hback]
    · intro h
      have := congrArg (hp.monodromy γq) h
      simpa only [hforward]
  ext g
  -- The range criterion is stated with the subtype's endpoint proof, while `e₁` is the
  -- locally named monodromy endpoint; this change aligns those definitionally equal terms.
  change g ∈ (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e₁.2).range ↔
    g ∈ FundamentalGroup.basepointChangeSubgroup γ
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e₀.2).range
  rw [← IsCoveringMap.monodromy_eq_self_iff_mem_range hp e₁ g,
    FundamentalGroup.mem_basepointChangeSubgroup_iff,
    ← IsCoveringMap.monodromy_eq_self_iff_mem_range hp e₀]
  exact hmon g

end IsCoveringMap

end TauCeti
