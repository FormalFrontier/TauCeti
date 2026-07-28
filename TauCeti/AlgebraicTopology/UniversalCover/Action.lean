/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Covering.Quotient
public import TauCeti.AlgebraicTopology.UniversalCover.Covering

/-!
# The fundamental-group action on the universal cover

The fundamental group `FundamentalGroup X x₀` acts on `UniversalCover x₀` by deck
transformations: an element `g` acts on a point represented by a homotopy class of paths from
`x₀` by prepending a loop representing `g⁻¹`. The action is free, continuous in the universal
cover variable, and properly discontinuous in the local form used by `IsQuotientCoveringMap`.
Consequently, the endpoint projection is a quotient covering map for this action.

This file is adapted from Kim Morrison's
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292), file
`Mathlib/AlgebraicTopology/FundamentalGroupoid/UniversalCover/Action.lean`.

## Convention

`FundamentalGroup X x₀ = End (FundamentalGroupoid.mk x₀)`, and Mathlib's `End`
multiplication reverses composition:
`(g * h).toPath = h.toPath.trans g.toPath`. Geometric concatenation therefore gives a right
action. To obtain the left action consumed by Mathlib's quotient-covering API, we define

`g • mk x q = mk x (g⁻¹.toPath.trans q)`.

The inverse-free computation rule is `inv_smul_mk`.

## Main declarations

* The `MulAction`, `FaithfulSMul`, `ContinuousConstSMul`, and `IsCancelSMul` instances for
  `FundamentalGroup X x₀` acting on `UniversalCover x₀`.
* `TauCeti.UniversalCover.proj_eq_iff_mem_orbit`: the fibres of `proj` are precisely the
  action orbits.
* `TauCeti.UniversalCover.exists_nhds_smul_disjoint`: the action is locally properly
  discontinuous.
* `TauCeti.UniversalCover.isQuotientCoveringMap`: `proj` is the quotient covering map for
  the fundamental-group action.
-/

public section
noncomputable section

open scoped unitInterval
open Topology

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

namespace TauCeti.UniversalCover

/-- The fundamental group acts on the universal cover by prepending the inverse loop class. -/
instance : SMul (FundamentalGroup X x₀) (UniversalCover x₀) where
  smul g p := mk p.proj (g⁻¹.toPath.trans p.path)

/-- The fundamental-group action prepends the inverse loop class to a representative path. -/
@[simp]
theorem smul_mk (g : FundamentalGroup X x₀) (x : X)
    (q : Path.Homotopic.Quotient x₀ x) :
    g • mk x q = mk x (g⁻¹.toPath.trans q) :=
  rfl

/-- Acting by an inverse prepends the corresponding loop class without an inverse. -/
theorem inv_smul_mk (g : FundamentalGroup X x₀) (x : X)
    (q : Path.Homotopic.Quotient x₀ x) :
    g⁻¹ • mk x q = mk x (g.toPath.trans q) := by
  rw [smul_mk, inv_inv]

/-- The fundamental-group action preserves the endpoint projection. -/
@[simp]
theorem proj_smul (g : FundamentalGroup X x₀) (p : UniversalCover x₀) :
    proj (g • p) = proj p :=
  rfl

/-- The action of the fundamental group on the universal cover. -/
instance : MulAction (FundamentalGroup X x₀) (UniversalCover x₀) where
  one_smul p := by
    rcases p with ⟨x, q⟩
    rw [smul_mk, inv_one, FundamentalGroup.one_def,
      Path.Homotopic.Quotient.refl_trans]
  mul_smul g h p := by
    rcases p with ⟨x, q⟩
    rw [smul_mk, smul_mk, smul_mk, mul_inv_rev, FundamentalGroup.mul_def,
      Path.Homotopic.Quotient.trans_assoc]

/-- The action on the universal cover is faithful. -/
instance : FaithfulSMul (FundamentalGroup X x₀) (UniversalCover x₀) where
  eq_of_smul_eq_smul {g₁ g₂} h := by
    have h' := h (mk x₀ (Path.Homotopic.Quotient.refl x₀))
    rw [smul_mk, smul_mk, Path.Homotopic.Quotient.trans_refl,
      Path.Homotopic.Quotient.trans_refl] at h'
    have hpath : g₁⁻¹.toPath = g₂⁻¹.toPath :=
      eq_of_heq ((UniversalCover.mk.injEq _ _ _ _).mp h').2
    exact inv_injective hpath

/-- Every fundamental-group element acts continuously on the universal cover. -/
instance : ContinuousConstSMul (FundamentalGroup X x₀) (UniversalCover x₀) where
  continuous_const_smul g := by
    rw [(isQuotientMap_ofBasedPath x₀).continuous_iff]
    obtain ⟨γ, hγ⟩ := Quotient.exists_rep (g⁻¹.toPath : Path.Homotopic.Quotient x₀ x₀)
    have hγ' : Path.Homotopic.Quotient.mk γ = g⁻¹.toPath := hγ
    suffices h_cont : Continuous (fun β : BasedPath x₀ ↦
        ofBasedPath x₀ (BasedPath.ofPath (γ.trans β.toPath))) by
      apply h_cont.congr
      intro β
      rw [ofBasedPath_ofPath, Function.comp_apply, ofBasedPath_eq, smul_mk,
        Path.Homotopic.Quotient.mk_trans, hγ']
    refine (continuous_ofBasedPath x₀).comp (Continuous.subtype_mk ?_ _)
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    have h_eval : Continuous fun p : BasedPath x₀ × I ↦ p.1.1 p.2 :=
      continuous_eval.comp (continuous_subtype_val.prodMap continuous_id)
    simpa using!
      Path.trans_continuous_family (a := fun _ : BasedPath x₀ ↦ x₀)
        (b := fun _ : BasedPath x₀ ↦ x₀)
        (c := fun β : BasedPath x₀ ↦ BasedPath.endpoint β)
        (fun _ ↦ γ) (Path.continuous_uncurry_iff.mpr continuous_const)
        (fun β ↦ β.toPath) h_eval

/-- The action of the fundamental group on the universal cover is free. -/
instance : IsCancelSMul (FundamentalGroup X x₀) (UniversalCover x₀) where
  right_cancel' a b c h := by
    rcases c with ⟨x, q⟩
    rw [smul_mk, smul_mk] at h
    have hpath : a⁻¹.toPath.trans q = b⁻¹.toPath.trans q :=
      eq_of_heq ((UniversalCover.mk.injEq _ _ _ _).mp h).2
    have h' := congrArg (fun r ↦ r.trans q.symm) hpath
    simp only [Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.trans_refl] at h'
    exact inv_injective h'

/-- Two points of the universal cover have the same projection exactly when they lie in the
same fundamental-group orbit. -/
theorem proj_eq_iff_mem_orbit {p₁ p₂ : UniversalCover x₀} :
    proj p₁ = proj p₂ ↔ p₁ ∈ MulAction.orbit (FundamentalGroup X x₀) p₂ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases p₁ with ⟨x₁, q₁⟩
    rcases p₂ with ⟨x₂, q₂⟩
    have hx : x₁ = x₂ := h
    subst hx
    refine ⟨(FundamentalGroup.fromPath (q₁.trans q₂.symm))⁻¹, ?_⟩
    simp only [smul_mk, inv_inv, Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]
  · rintro ⟨g, hg⟩
    rw [← hg, proj_smul]

/-- The endpoint projection is surjective when the base is path-connected. -/
theorem proj_surjective [PathConnectedSpace X] :
    Function.Surjective (proj : UniversalCover x₀ → X) := fun x ↦
  ⟨mk x (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ x)), rfl⟩

/-- Every point has a neighbourhood disjoint from each of its nonidentity translates. -/
theorem exists_nhds_smul_disjoint
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (e : UniversalCover x₀) :
    ∃ U ∈ 𝓝 e, ∀ g : FundamentalGroup X x₀,
      ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  rcases e with ⟨x, q⟩
  obtain ⟨baseU, hU_open, hxU, -, hU_slsc⟩ :=
    exists_isOpen_mem_isPathConnected_isPathHomotopyTrivial x
  let U := sheet baseU hxU q
  have hU_open' : IsOpen U := isOpen_sheet baseU hU_open hxU q
  have hU_mem : mk x q ∈ U := by
    induction q using Quotient.inductionOn with
    | h p => exact ofBasedPath_ofPath p ▸ mem_sheet_self hxU p
  refine ⟨U, hU_open'.mem_nhds hU_mem, fun g hgU ↦ ?_⟩
  obtain ⟨_, ⟨y, hyU, rfl⟩, hgyU⟩ := hgU
  exact IsCancelSMul.eq_one_of_smul
    (proj_injOn_sheet hU_slsc hxU q hgyU hyU (proj_smul g y))

/-- The endpoint projection is a quotient covering map for the fundamental-group action. -/
theorem isQuotientCoveringMap
    [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] :
    IsQuotientCoveringMap (proj : UniversalCover x₀ → X) (FundamentalGroup X x₀) where
  __ := (isCoveringMap x₀).isOpenMap.isQuotientMap
    (continuous_proj x₀) proj_surjective
  apply_eq_iff_mem_orbit := proj_eq_iff_mem_orbit
  disjoint := exists_nhds_smul_disjoint

end TauCeti.UniversalCover
