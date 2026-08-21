/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Action
public import TauCeti.Topology.Covering.BalancedProduct
public import TauCeti.Topology.Covering.Category
public import TauCeti.Topology.Homotopy.Monodromy.Functoriality

/-!
# The covering space attached to a fundamental-group set

Let `X` be path connected, locally path connected and semilocally simply connected, and let `A`
be a set with an action of `π₁(X, x₀)`. The universal cover `UniversalCover x₀` is the total
space of a quotient covering map for `π₁(X, x₀)`, so the balanced product

`ActionCover x₀ A = UniversalCover x₀ ×_{π₁(X, x₀)} A`

is a covering space of `X` by `TauCeti.BalancedProduct.isCoveringMap_proj`, and its fibre over
`x₀` is `A`.

The action is arbitrary: it is neither assumed transitive nor nonempty, so the resulting cover is
in general disconnected. That is the point. The transitive case is already available as the
quotient of the universal cover by a stabiliser
(`TauCeti.UniversalCover.stabilizerCover`), and a connected cover is exactly what such a quotient
produces; a general action needs the disjoint union of one such quotient per orbit, which is what
the balanced product provides in one step.

The fibre identification is equivariant. The map `e ↦ ⟦(e, a)⟧` from the universal cover is a map
of covering spaces over `X`, and monodromy is functorial in such maps, so monodromy on the fibre
of `ActionCover x₀ A` is computed by monodromy on the fibre of the universal cover, which is the
fundamental-group action by `TauCeti.UniversalCover.monodromy_basepointLift`. Because that action
prepends the *inverse* loop class, the inverse cancels against the exchange
`⟦(g • e, a)⟧ = ⟦(e, g⁻¹ • a)⟧` and no `ᵐᵒᵖ` appears here.

## Main declarations

* `TauCeti.UniversalCover.ActionCover`: the balanced product of the universal cover with `A`.
* `TauCeti.UniversalCover.isCoveringMap_actionCoverProj`: **its projection is a covering map.**
* `TauCeti.UniversalCover.actionCoveringSpace`: the same cover, bundled as an object of
  `TauCeti.CoveringSpace`.
* `TauCeti.UniversalCover.actionCoverFiberEquiv`: its fibre over `x₀` is `A`, and
  `TauCeti.UniversalCover.monodromy_actionCoverFiberEquiv` says the identification intertwines
  monodromy with the given action.

## References

This is the object half of the essential surjectivity of monodromy on *all* covering spaces,
the disconnected case of `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, item 8, which asks
for covers to be classified by functors out of the fundamental groupoid. It consumes the
based-path universal cover adapted from Kim Morrison's
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292) and Mathlib's
quotient-covering-map interface due to Junyan Xu.
-/

public section
noncomputable section

open CategoryTheory Topology

universe u

namespace TauCeti.UniversalCover

variable {X : Type u} [TopologicalSpace X] [LocallyPathConnectedSpace X] [PathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] (x₀ : X) (A : Type u)
  [MulAction (FundamentalGroup X x₀) A] [TopologicalSpace A] [DiscreteTopology A]

/-- The total space of the covering space attached to a `π₁(X, x₀)`-set `A`: the balanced product
of the universal cover with `A`. -/
abbrev ActionCover : Type u := BalancedProduct (FundamentalGroup X x₀) (UniversalCover x₀) A

/-- The projection of the cover attached to `A` down to the base. -/
def actionCoverProj : ActionCover x₀ A → X :=
  BalancedProduct.proj A fun g e => proj_smul g e

omit [LocallyPathConnectedSpace X] [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
  [DiscreteTopology A] [TopologicalSpace A] in
@[simp]
theorem actionCoverProj_mk (e : UniversalCover x₀) (a : A) :
    actionCoverProj x₀ A (BalancedProduct.mk (FundamentalGroup X x₀) e a) = proj e :=
  BalancedProduct.proj_mk A _ e a

omit [LocallyPathConnectedSpace X] [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
  [DiscreteTopology A] in
theorem continuous_actionCoverProj : Continuous (actionCoverProj x₀ A) :=
  BalancedProduct.continuous_proj A _ (continuous_proj x₀)

/-- **The cover attached to a `π₁(X, x₀)`-set is a covering space of `X`.** -/
theorem isCoveringMap_actionCoverProj : IsCoveringMap (actionCoverProj x₀ A) :=
  BalancedProduct.isCoveringMap_proj A _ isQuotientCoveringMap

/-- The cover attached to a `π₁(X, x₀)`-set, bundled as a covering space over `X`. -/
def actionCoveringSpace : CoveringSpace (TopCat.of X) :=
  CoveringSpace.mk (TopCat.ofHom ⟨actionCoverProj x₀ A, continuous_actionCoverProj x₀ A⟩)
    (isCoveringMap_actionCoverProj x₀ A)

/-- The total space of the bundled cover attached to `A` is `ActionCover x₀ A`. -/
@[simp]
theorem actionCoveringSpace_coe :
    (actionCoveringSpace x₀ A : TopCat) = TopCat.of (ActionCover x₀ A) :=
  CoveringSpace.mk_coe _ _

/-- The projection of the bundled cover attached to `A` is `actionCoverProj`. -/
theorem actionCoveringSpace_proj :
    (actionCoveringSpace x₀ A).proj =
      eqToHom (actionCoveringSpace_coe x₀ A) ≫
        TopCat.ofHom ⟨actionCoverProj x₀ A, continuous_actionCoverProj x₀ A⟩ :=
  CoveringSpace.mk_proj _ _

/-- The characteristic equality of total spaces, viewed as a homeomorphism. -/
private def actionCoverTotalSpaceHomeomorph :
    (actionCoveringSpace x₀ A : TopCat) ≃ₜ ActionCover x₀ A :=
  TopCat.homeoOfIso (eqToIso (actionCoveringSpace_coe x₀ A))

/-- The characteristic total-space homeomorphism commutes with the two projections. -/
@[simp]
private theorem actionCoverProj_actionCoverTotalSpaceHomeomorph
    (e : (actionCoveringSpace x₀ A : TopCat)) :
    actionCoverProj x₀ A (actionCoverTotalSpaceHomeomorph x₀ A e) =
      (actionCoveringSpace x₀ A).proj e :=
  (DFunLike.congr_fun (congrArg TopCat.Hom.hom (actionCoveringSpace_proj x₀ A)) e).symm

/-- Transport from the fibre of the bundled cover to the fibre of its projection. -/
private def actionCoverFiberTransport :
    ⇑(actionCoveringSpace x₀ A).proj ⁻¹' {x₀} ≃ actionCoverProj x₀ A ⁻¹' {x₀} :=
  ((actionCoverTotalSpaceHomeomorph x₀ A).subtype fun e => by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [actionCoverProj_actionCoverTotalSpaceHomeomorph x₀ A e]).toEquiv

/-- On underlying points, fibre transport applies the characteristic homeomorphism. -/
@[simp]
private theorem actionCoverFiberTransport_apply_coe
    (e : ⇑(actionCoveringSpace x₀ A).proj ⁻¹' {x₀}) :
    (actionCoverFiberTransport x₀ A e : ActionCover x₀ A) =
      actionCoverTotalSpaceHomeomorph x₀ A e :=
  (rfl)

/-- Fibre transport commutes with monodromy. -/
@[simp]
private theorem actionCoverFiberTransport_apply_monodromy (g : FundamentalGroup X x₀)
    (e : ⇑(actionCoveringSpace x₀ A).proj ⁻¹' {x₀}) :
    actionCoverFiberTransport x₀ A
        ((actionCoveringSpace x₀ A).isCoveringMap_proj.monodromy g e) =
      (isCoveringMap_actionCoverProj x₀ A).monodromy g (actionCoverFiberTransport x₀ A e) := by
  have hmonodromy := TauCeti.IsCoveringMap.fiberMap_monodromy
    (actionCoveringSpace x₀ A).isCoveringMap_proj (isCoveringMap_actionCoverProj x₀ A)
    (actionCoverTotalSpaceHomeomorph x₀ A)
    (funext (actionCoverProj_actionCoverTotalSpaceHomeomorph x₀ A)) g e
  have hfiberMap (e' : ⇑(actionCoveringSpace x₀ A).proj ⁻¹' {x₀}) :
      TauCeti.IsCoveringMap.fiberMap (actionCoverTotalSpaceHomeomorph x₀ A)
          (funext (actionCoverProj_actionCoverTotalSpaceHomeomorph x₀ A)) x₀ e' =
        actionCoverFiberTransport x₀ A e' :=
    Subtype.ext (TauCeti.IsCoveringMap.fiberMap_apply_coe _ _ x₀ e')
  simpa only [hfiberMap] using hmonodromy

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- **The fibre of the cover attached to `A` over `x₀` is `A`.** A point of `A` labels the class
of the pair it forms with the constant-path point of the universal cover. -/
def actionCoverFiberEquiv : A ≃ actionCoverProj x₀ A ⁻¹' {x₀} :=
  BalancedProduct.fiberEquiv A _ (fun h => proj_eq_iff_mem_orbit.mp h) (basepointLift x₀)

omit [LocallyPathConnectedSpace X] [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
  [TopologicalSpace A] [DiscreteTopology A] in
@[simp]
theorem actionCoverFiberEquiv_apply_coe (a : A) :
    (actionCoverFiberEquiv x₀ A a : ActionCover x₀ A) =
      BalancedProduct.mk (FundamentalGroup X x₀) (basepointLift x₀ : UniversalCover x₀) a :=
  BalancedProduct.fiberEquiv_apply_coe A _ (fun h => proj_eq_iff_mem_orbit.mp h)
    (basepointLift x₀) a

/-- **The fibre identification is equivariant**: the monodromy of a loop class on the fibre of
the cover attached to `A` is the action of that loop class on `A`. -/
@[simp]
theorem monodromy_actionCoverFiberEquiv (g : FundamentalGroup X x₀) (a : A) :
    (isCoveringMap_actionCoverProj x₀ A).monodromy g (actionCoverFiberEquiv x₀ A a) =
      actionCoverFiberEquiv x₀ A (g • a) := by
  -- Attaching the label `a` is a map of covering spaces over `X`, so it intertwines monodromy.
  let ι : C(UniversalCover x₀, ActionCover x₀ A) :=
    ⟨fun e => BalancedProduct.mk (FundamentalGroup X x₀) e a,
      continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const)⟩
  have hcomp : actionCoverProj x₀ A ∘ ι = proj := funext fun e => actionCoverProj_mk x₀ A e a
  have key := TauCeti.IsCoveringMap.fiberMap_monodromy (isCoveringMap x₀)
    (isCoveringMap_actionCoverProj x₀ A) ι hcomp g (basepointLift x₀)
  have hbase : actionCoverFiberEquiv x₀ A a =
      TauCeti.IsCoveringMap.fiberMap ι hcomp x₀ (basepointLift x₀) :=
    Subtype.ext ((actionCoverFiberEquiv_apply_coe x₀ A a).trans
      (TauCeti.IsCoveringMap.fiberMap_apply_coe ι hcomp x₀ (basepointLift x₀)).symm)
  rw [hbase, ← key]
  refine Subtype.ext ?_
  rw [TauCeti.IsCoveringMap.fiberMap_apply_coe, actionCoverFiberEquiv_apply_coe]
  -- The application lemmas expose the maps, but leave coercions from the two fibre subtypes.
  -- This reduction records exactly their underlying points before rewriting quotient classes.
  change BalancedProduct.mk (FundamentalGroup X x₀)
      ((isCoveringMap x₀).monodromy g (basepointLift x₀) : UniversalCover x₀) a =
    BalancedProduct.mk (FundamentalGroup X x₀) (basepointLift x₀ : UniversalCover x₀) (g • a)
  rw [monodromy_basepointLift, BalancedProduct.mk_smul_left, inv_inv]

/-- **The fibre of the bundled cover attached to `A` over `x₀` is `A`.** -/
def actionCoveringSpaceFiberEquiv : ⇑(actionCoveringSpace x₀ A).proj ⁻¹' {x₀} ≃ A :=
  (actionCoverFiberTransport x₀ A).trans (actionCoverFiberEquiv x₀ A).symm

/-- **The bundled fibre identification is equivariant**: monodromy on the fibre of the cover
attached to `A` agrees with the given action of the fundamental group on `A`. -/
@[simp]
theorem actionCoveringSpaceFiberEquiv_apply_monodromy (g : FundamentalGroup X x₀)
    (e : ⇑(actionCoveringSpace x₀ A).proj ⁻¹' {x₀}) :
    actionCoveringSpaceFiberEquiv x₀ A
        ((actionCoveringSpace x₀ A).isCoveringMap_proj.monodromy g e) =
      g • actionCoveringSpaceFiberEquiv x₀ A e := by
  obtain ⟨a, ha⟩ := (actionCoverFiberEquiv x₀ A).surjective (actionCoverFiberTransport x₀ A e)
  rw [actionCoveringSpaceFiberEquiv, Equiv.trans_apply, Equiv.trans_apply,
    actionCoverFiberTransport_apply_monodromy, ← ha, monodromy_actionCoverFiberEquiv,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end TauCeti.UniversalCover
