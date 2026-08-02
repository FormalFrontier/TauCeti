/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.SubgroupQuotient

/-!
# The subgroup recovered from a universal-cover quotient

For `H ≤ π₁(X, x₀)`, the orbit quotient `UniversalCover x₀ / H` has a distinguished
point represented by the constant path. The quotient map from the universal cover is a quotient
covering map with acting group `H`; since the universal cover is simply connected, this gives

  `π₁(UniversalCover x₀ / H) ≃* Hᵐᵒᵖ`.

The endpoint projection descends from the universal cover to the orbit quotient. This file
computes its induced fundamental-group homomorphism and proves that its range is exactly `H`.
The computation contains an inverse because the project uses a left action in which a loop class
acts on the universal cover by prepending its inverse.

This proves the subgroup-recovery part of `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2,
item 7: for the pointed quotient associated to `H`, prove `p_*(π₁(–)) = H`. It reuses the
fundamental-group action adapted from Kim Morrison's work in mathlib4#38292 and Mathlib's
quotient-cover monodromy comparison due to Junyan Xu. No Mathlib code is vendored.

## Main declarations

* `TauCeti.UniversalCover.SubgroupQuotient.basepointLift`: the constant-path lift of the
  distinguished quotient point.
* `TauCeti.UniversalCover.SubgroupQuotient.fundamentalGroupEquiv` and
  `TauCeti.UniversalCover.SubgroupQuotient.fundamentalGroupEquiv_unop_smul`: the fundamental
  group of the quotient is the opposite of `H`, compatibly with monodromy.
* `TauCeti.UniversalCover.mapOfEq_subgroupQuotientProj_apply`: the descended endpoint map sends
  a quotient loop to the inverse of its corresponding element of `H`.
* `TauCeti.UniversalCover.range_mapOfEq_subgroupQuotientProj`: the descended endpoint map
  recovers exactly `H`.
-/

public section
noncomputable section

open Topology
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X] (x₀ : X)

namespace TauCeti.UniversalCover

/-- The constant-path lift of the distinguished point of the subgroup quotient. -/
def SubgroupQuotient.basepointLift (H : Subgroup (FundamentalGroup X x₀)) :
    (subgroupQuotientMap x₀ H) ⁻¹' {SubgroupQuotient.basepoint x₀ H} :=
  ⟨TauCeti.UniversalCover.basepointLift x₀, by
    rw [Set.mem_preimage, Set.mem_singleton_iff, subgroupQuotientMap_apply,
      SubgroupQuotient.basepoint_eq_mk, TauCeti.UniversalCover.basepointLift_coe]⟩

/-- The underlying universal-cover point of the distinguished lift is the constant-path
point. -/
@[simp]
theorem SubgroupQuotient.basepointLift_coe (H : Subgroup (FundamentalGroup X x₀)) :
    (SubgroupQuotient.basepointLift x₀ H : UniversalCover x₀) =
      (TauCeti.UniversalCover.basepointLift x₀ : UniversalCover x₀) := by
  simp [SubgroupQuotient.basepointLift]

/-- The fundamental group of the subgroup quotient at its distinguished point is the opposite
of the acting subgroup. The opposite records the left-action convention used by quotient-cover
monodromy. -/
noncomputable def SubgroupQuotient.fundamentalGroupEquiv
    [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X]
    (H : Subgroup (FundamentalGroup X x₀)) :
    FundamentalGroup (SubgroupQuotient x₀ H)
        (SubgroupQuotient.basepoint x₀ H) ≃* Hᵐᵒᵖ :=
  (isQuotientCoveringMap_subgroupQuotientMap x₀ H).fundamentalGroupEquiv
    (SubgroupQuotient.basepointLift x₀ H)

/-- The subgroup element assigned to a quotient loop moves the distinguished lift to the
endpoint of that loop's monodromy lift. -/
@[simp]
theorem SubgroupQuotient.fundamentalGroupEquiv_unop_smul
    [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X]
    (H : Subgroup (FundamentalGroup X x₀))
    (g : FundamentalGroup (SubgroupQuotient x₀ H)
      (SubgroupQuotient.basepoint x₀ H)) :
    (SubgroupQuotient.fundamentalGroupEquiv x₀ H g).unop •
        (SubgroupQuotient.basepointLift x₀ H : UniversalCover x₀) =
      (isQuotientCoveringMap_subgroupQuotientMap x₀ H).isCoveringMap.monodromy g
        (SubgroupQuotient.basepointLift x₀ H) :=
  (isQuotientCoveringMap_subgroupQuotientMap x₀ H).unop_fundamentalGroupToMulOpposite_smul

variable [LocallyPathConnectedSpace X] [PathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

/-- Monodromy along the quotient map followed by the descended endpoint map agrees with
monodromy of the universal-cover projection. -/
private theorem monodromy_mapOfEq_subgroupQuotientProj
    (H : Subgroup (FundamentalGroup X x₀))
    (g : FundamentalGroup (SubgroupQuotient x₀ H)
      (SubgroupQuotient.basepoint x₀ H)) :
    ((isCoveringMap x₀).monodromy
        (FundamentalGroup.mapOfEq
          ⟨subgroupQuotientProj x₀ H, continuous_subgroupQuotientProj x₀ H⟩
          (subgroupQuotientProj_basepoint x₀ H) g)
        (TauCeti.UniversalCover.basepointLift x₀) : UniversalCover x₀) =
      ((isQuotientCoveringMap_subgroupQuotientMap x₀ H).isCoveringMap.monodromy g
        (SubgroupQuotient.basepointLift x₀ H) : UniversalCover x₀) := by
  let hq := isQuotientCoveringMap_subgroupQuotientMap x₀ H
  let e := SubgroupQuotient.basepointLift x₀ H
  have he : (e : UniversalCover x₀) =
      (TauCeti.UniversalCover.basepointLift x₀ : UniversalCover x₀) := by
    dsimp only [e]
    rw [SubgroupQuotient.basepointLift_coe]
  let e' := hq.isCoveringMap.monodromy g e
  have he'_basepoint : subgroupQuotientMap x₀ H e' =
      SubgroupQuotient.basepoint x₀ H := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using e'.2
  have he' : proj (e' : UniversalCover x₀) = x₀ := by
    calc
      proj (e' : UniversalCover x₀) =
          subgroupQuotientProj x₀ H (subgroupQuotientMap x₀ H e') := by
            exact congrFun (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H) e' |>.symm
      _ = subgroupQuotientProj x₀ H (SubgroupQuotient.basepoint x₀ H) := by
            rw [he'_basepoint]
      _ = x₀ := subgroupQuotientProj_basepoint x₀ H
  let e'' : (proj : UniversalCover x₀ → X) ⁻¹' {x₀} := ⟨e', he'⟩
  -- Lift `g` through the quotient map, then map that same lifted path through the descended
  -- endpoint map; the commuting triangle identifies it as the universal-cover lift.
  have hmon : (isCoveringMap x₀).monodromy
      (FundamentalGroup.mapOfEq
        ⟨subgroupQuotientProj x₀ H, continuous_subgroupQuotientProj x₀ H⟩
        (subgroupQuotientProj_basepoint x₀ H) g)
      (TauCeti.UniversalCover.basepointLift x₀) = e'' := by
    let Γ := (hq.isCoveringMap.liftPathQuotient g e).cast he.symm rfl
    apply (isCoveringMap x₀).monodromy_eq_of_map_eq
      Γ
    rw [FundamentalGroup.mapOfEq_apply]
    let r : C(SubgroupQuotient x₀ H, X) :=
      ⟨subgroupQuotientProj x₀ H, continuous_subgroupQuotientProj x₀ H⟩
    let q : C(UniversalCover x₀, SubgroupQuotient x₀ H) :=
      ⟨subgroupQuotientMap x₀ H, hq.continuous⟩
    dsimp only [Γ]
    rw [Path.Homotopic.Quotient.map_cast]
    have hmapped := congrArg (fun δ ↦ δ.map r)
      (hq.isCoveringMap.map_liftPathQuotient g e)
    rw [← Path.Homotopic.Quotient.map_comp] at hmapped
    erw [Path.Homotopic.Quotient.map_cast] at hmapped
    -- The four conversion goals reconcile the dependent endpoint casts; their pointwise
    -- equalities all come from `subgroupQuotientProj ∘ subgroupQuotientMap = proj`.
    convert hmapped using 2
    · calc
        proj (TauCeti.UniversalCover.basepointLift x₀ : UniversalCover x₀) =
            proj (e : UniversalCover x₀) :=
          congrArg proj he.symm
        _ = subgroupQuotientProj x₀ H (subgroupQuotientMap x₀ H e) :=
          congrFun (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H) e |>.symm
    · exact congrFun (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H) e' |>.symm
    · induction hΓ : hq.isCoveringMap.liftPathQuotient g e using Quotient.inductionOn with
      | h Γ =>
        apply Path.Homotopic.hpath_hext
        intro t
        exact congrFun (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H) (Γ t) |>.symm
    · erw [Path.Homotopic.Quotient.cast_cast]
      exact (Path.Homotopic.Quotient.cast_heq _ _).trans
        (Path.Homotopic.Quotient.cast_heq _ _).symm
  exact congrArg Subtype.val hmon

/-- The descended endpoint map sends a quotient loop to the inverse of the corresponding
element of the acting subgroup. The inverse is forced by the left-action convention. -/
@[simp]
theorem mapOfEq_subgroupQuotientProj_apply
    (H : Subgroup (FundamentalGroup X x₀))
    (g : FundamentalGroup (SubgroupQuotient x₀ H)
      (SubgroupQuotient.basepoint x₀ H)) :
    FundamentalGroup.mapOfEq
        ⟨subgroupQuotientProj x₀ H, continuous_subgroupQuotientProj x₀ H⟩
        (subgroupQuotientProj_basepoint x₀ H) g =
      ((SubgroupQuotient.fundamentalGroupEquiv x₀ H g).unop.1)⁻¹ := by
  let f := FundamentalGroup.mapOfEq
    ⟨subgroupQuotientProj x₀ H, continuous_subgroupQuotientProj x₀ H⟩
    (subgroupQuotientProj_basepoint x₀ H) g
  let h := (SubgroupQuotient.fundamentalGroupEquiv x₀ H g).unop
  apply inv_injective
  rw [inv_inv]
  apply IsCancelSMul.right_cancel _ _
    (TauCeti.UniversalCover.basepointLift x₀ : UniversalCover x₀)
  calc
    f⁻¹ • (TauCeti.UniversalCover.basepointLift x₀ : UniversalCover x₀) =
        ((isCoveringMap x₀).monodromy f (TauCeti.UniversalCover.basepointLift x₀) :
          UniversalCover x₀) :=
      (monodromy_basepointLift x₀ f).symm
    _ = ((isQuotientCoveringMap_subgroupQuotientMap x₀ H).isCoveringMap.monodromy g
        (SubgroupQuotient.basepointLift x₀ H) : UniversalCover x₀) :=
      monodromy_mapOfEq_subgroupQuotientProj x₀ H g
    _ = h • (SubgroupQuotient.basepointLift x₀ H : UniversalCover x₀) := by
      exact (SubgroupQuotient.fundamentalGroupEquiv_unop_smul x₀ H g).symm
    _ = h.1 • (TauCeti.UniversalCover.basepointLift x₀ : UniversalCover x₀) := by
      simp only [SubgroupQuotient.basepointLift_coe, Subgroup.smul_def]

/-- The subgroup induced by the descended endpoint map is exactly the subgroup used to form
the orbit quotient. -/
theorem range_mapOfEq_subgroupQuotientProj
    (H : Subgroup (FundamentalGroup X x₀)) :
    (FundamentalGroup.mapOfEq
      (x := SubgroupQuotient.basepoint x₀ H) (y := x₀)
      ⟨subgroupQuotientProj x₀ H, continuous_subgroupQuotientProj x₀ H⟩
      (subgroupQuotientProj_basepoint x₀ H)).range = H := by
  ext g
  constructor
  · rintro ⟨γ, rfl⟩
    rw [mapOfEq_subgroupQuotientProj_apply]
    exact H.inv_mem (SubgroupQuotient.fundamentalGroupEquiv x₀ H γ).unop.2
  · intro hg
    let h : H := ⟨g⁻¹, H.inv_mem hg⟩
    refine ⟨(SubgroupQuotient.fundamentalGroupEquiv x₀ H).symm
      (MulOpposite.op h), ?_⟩
    rw [mapOfEq_subgroupQuotientProj_apply, MulEquiv.apply_symm_apply]
    exact inv_inv g

end TauCeti.UniversalCover
