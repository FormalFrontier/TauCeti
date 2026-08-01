/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Homeomorph.Defs

/-!
# The fundamental group is a homeomorphism invariant

Mathlib records the homomorphism `FundamentalGroup.map` induced by a continuous map and the
variant `FundamentalGroup.mapOfEq` that adjusts the target basepoint along an equality, but it
stops short of packaging a homeomorphism as an *isomorphism* of fundamental groups. This file
supplies that: a homeomorphism `e : X ≃ₜ Y` induces a group isomorphism
`π₁(X, x) ≃* π₁(Y, e x)`, and more generally `π₁(X, x) ≃* π₁(Y, y)` whenever `e x = y`.

The forward map is `FundamentalGroup.mapOfEq` of `e`; the inverse is `FundamentalGroup.mapOfEq`
of `e.symm`. The two round trips are the composition law `mapOfEq_comp` (the induced maps of two
continuous maps compose to the induced map of their composite) applied to `e.symm ∘ e = id` and
`e ∘ e.symm = id`, together with `mapOfEq_id` (the induced map of the identity is the identity).
Both auxiliary lemmas are proved once here from Mathlib's `FundamentalGroup.mapOfEq_apply` and the
`Path.Homotopic.Quotient` transport lemmas (`map_comp`, `map_cast`, `cast_cast`), and are useful
on their own.

Transporting a fundamental-group computation across a homeomorphism is the group-level input the
universal-covers roadmap needs for its Stage 4 applications: for example the fundamental group of
the unit circle `Circle ⊆ ℂ`, obtained from the additive-circle computation through Mathlib's
`AddCircle.homeomorphCircle`, and later `π₁(ℝPⁿ)`. This mirrors the way
`TauCeti.FundamentalGroup.prodMulEquiv` supplied the product formula the torus computation needs.

## Main declarations

* `TauCeti.FundamentalGroup.mapOfEq_comp`: `mapOfEq g hg (mapOfEq f hf p) = mapOfEq (g.comp f) _ p`.
* `TauCeti.FundamentalGroup.mapOfEq_id`: `mapOfEq (ContinuousMap.id X) h = id`.
* `TauCeti.FundamentalGroup.mapOfEq_rfl`: along the reflexivity proof, `mapOfEq` is `map`.
* `TauCeti.FundamentalGroup.homeomorphMulEquivOfEq`: `π₁(X, x) ≃* π₁(Y, y)` from `e : X ≃ₜ Y`
  with `e x = y`.
* `TauCeti.FundamentalGroup.homeomorphMulEquiv`: `π₁(X, x) ≃* π₁(Y, e x)`.
-/

public section

namespace TauCeti

namespace FundamentalGroup

open Path.Homotopic

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {x : X} {y : Y} {z : Z}

/-- The maps induced on fundamental groups by two continuous maps compose to the map induced by
their composite: `mapOfEq g hg (mapOfEq f hf p) = mapOfEq (g.comp f) _ p`. -/
theorem mapOfEq_comp (g : C(Y, Z)) (f : C(X, Y)) (hf : f x = y) (hg : g y = z)
    (p : _root_.FundamentalGroup X x) :
    _root_.FundamentalGroup.mapOfEq g hg (_root_.FundamentalGroup.mapOfEq f hf p) =
      _root_.FundamentalGroup.mapOfEq (g.comp f)
        (show (g.comp f) x = z by rw [ContinuousMap.comp_apply, hf, hg]) p := by
  simp only [_root_.FundamentalGroup.mapOfEq_apply]
  rw [Path.Homotopic.Quotient.map_cast, Path.Homotopic.Quotient.cast_cast,
    ← Path.Homotopic.Quotient.map_comp]

/-- The map induced on fundamental groups by the identity continuous map is the identity. -/
@[simp]
theorem mapOfEq_id (h : (ContinuousMap.id X) x = x) (p : _root_.FundamentalGroup X x) :
    _root_.FundamentalGroup.mapOfEq (ContinuousMap.id X) h p = p := by
  have key : ∀ q : Path.Homotopic.Quotient x x,
      Path.Homotopic.Quotient.map q (ContinuousMap.id X) = q := by
    intro q
    induction q using Quotient.inductionOn with
    | h γ => exact congrArg _ (Path.map_id γ)
  rw [_root_.FundamentalGroup.mapOfEq_apply, key]
  exact Path.Homotopic.Quotient.cast_rfl_rfl p

/-- Transporting the target basepoint along the reflexivity proof does nothing: `mapOfEq f rfl`
is Mathlib's `FundamentalGroup.map f x`.

This is the comparison needed whenever a statement phrased with a general basepoint equation
`f x = y` is applied to a lifting criterion phrased at the basepoint `f x` itself. -/
@[simp]
theorem mapOfEq_rfl (f : C(X, Y)) :
    _root_.FundamentalGroup.mapOfEq f (rfl : f x = f x) = _root_.FundamentalGroup.map f x := by
  ext γ
  rw [_root_.FundamentalGroup.mapOfEq_apply]
  exact Path.Homotopic.Quotient.cast_rfl_rfl _

/-- The induced map `mapOfEq` depends only on the underlying continuous map, not on the chosen
proof of the basepoint equation: two equal continuous maps induce the same map. -/
theorem mapOfEq_congr {f₁ f₂ : C(X, Y)} (hfe : f₁ = f₂) (h₁ : f₁ x = y) (h₂ : f₂ x = y)
    (p : _root_.FundamentalGroup X x) :
    _root_.FundamentalGroup.mapOfEq f₁ h₁ p = _root_.FundamentalGroup.mapOfEq f₂ h₂ p := by
  subst hfe
  rfl

/-- If `g ∘ f` is the identity, then the induced map of `g` undoes the induced map of `f`. -/
theorem mapOfEq_mapOfEq_of_comp_eq_id (g : C(Y, X)) (f : C(X, Y)) (hf : f x = y) (hg : g y = x)
    (hgf : g.comp f = ContinuousMap.id X) (p : _root_.FundamentalGroup X x) :
    _root_.FundamentalGroup.mapOfEq g hg (_root_.FundamentalGroup.mapOfEq f hf p) = p := by
  rw [mapOfEq_comp g f hf hg]
  exact (mapOfEq_congr hgf _ rfl p).trans (mapOfEq_id rfl p)

/-- A homeomorphism `e : X ≃ₜ Y` carrying `x` to `y` induces an isomorphism of fundamental groups
`π₁(X, x) ≃* π₁(Y, y)`. The forward map is `FundamentalGroup.mapOfEq` of `e`; the inverse is
`FundamentalGroup.mapOfEq` of `e.symm`. -/
@[expose] noncomputable def homeomorphMulEquivOfEq (e : X ≃ₜ Y) (h : e x = y) :
    _root_.FundamentalGroup X x ≃* _root_.FundamentalGroup Y y where
  toFun := _root_.FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h
  invFun := _root_.FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
    (show e.symm y = x by rw [← h, e.symm_apply_apply])
  left_inv p :=
    mapOfEq_mapOfEq_of_comp_eq_id ⟨e.symm, e.symm.continuous⟩ ⟨e, e.continuous⟩ h
      (show e.symm y = x by rw [← h, e.symm_apply_apply])
      (ContinuousMap.ext fun t => e.symm_apply_apply t) p
  right_inv q :=
    mapOfEq_mapOfEq_of_comp_eq_id ⟨e, e.continuous⟩ ⟨e.symm, e.symm.continuous⟩
      (show e.symm y = x by rw [← h, e.symm_apply_apply]) h
      (ContinuousMap.ext fun t => e.apply_symm_apply t) q
  map_mul' := (_root_.FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h).map_mul

@[simp]
theorem homeomorphMulEquivOfEq_apply (e : X ≃ₜ Y) (h : e x = y)
    (p : _root_.FundamentalGroup X x) :
    homeomorphMulEquivOfEq e h p = _root_.FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h p :=
  rfl

@[simp]
theorem homeomorphMulEquivOfEq_symm_apply (e : X ≃ₜ Y) (h : e x = y)
    (q : _root_.FundamentalGroup Y y) :
    (homeomorphMulEquivOfEq e h).symm q =
      _root_.FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
        (show e.symm y = x by rw [← h, e.symm_apply_apply]) q :=
  rfl

/-- A homeomorphism `e : X ≃ₜ Y` induces an isomorphism of fundamental groups
`π₁(X, x) ≃* π₁(Y, e x)`. -/
@[expose] noncomputable def homeomorphMulEquiv (e : X ≃ₜ Y) (x : X) :
    _root_.FundamentalGroup X x ≃* _root_.FundamentalGroup Y (e x) :=
  homeomorphMulEquivOfEq e rfl

@[simp]
theorem homeomorphMulEquiv_apply (e : X ≃ₜ Y) (x : X) (p : _root_.FundamentalGroup X x) :
    homeomorphMulEquiv e x p =
      _root_.FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ rfl p :=
  rfl

@[simp]
theorem homeomorphMulEquiv_symm_apply (e : X ≃ₜ Y) (x : X)
    (q : _root_.FundamentalGroup Y (e x)) :
    (homeomorphMulEquiv e x).symm q =
      _root_.FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_apply x) q :=
  rfl

end FundamentalGroup

end TauCeti
