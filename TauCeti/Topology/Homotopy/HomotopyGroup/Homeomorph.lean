/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.Map

/-!
# Higher homotopy groups are homeomorphism invariants

The functoriality API in `TauCeti.Topology.Homotopy.HomotopyGroup.Map` records the map
`HomotopyGroup.map` on homotopy classes induced by a based continuous map (a monoid
homomorphism `HomotopyGroup.mapHom` in positive dimensions), but it stops short of packaging a
homeomorphism as an *isomorphism* of homotopy groups. This file supplies that: a homeomorphism
`e : X ≃ₜ Y` induces an equivalence `π_N(X, x) ≃ π_N(Y, e x)` in every dimension, and a group
isomorphism `π_N(X, x) ≃* π_N(Y, e x)` in positive dimensions, and more generally the versions
sending `x` to any `y` with `e x = y`.

The forward and inverse application lemmas characterize these equivalences as
`HomotopyGroup.map` for `e` and `e.symm`, respectively.

Transporting a homotopy-group computation across a homeomorphism is the dimension-`N` analogue of
`TauCeti.FundamentalGroup.homeomorphMulEquiv`, and is part of the higher-homotopy-group API the
universal-covers roadmap asks for in Stage 3 item 9 (`TauCetiRoadmap/UniversalCovers/README.md`),
before proving that a covering map induces isomorphisms on `π_n` for `n ≥ 2`.

## Main declarations

* `TauCeti.HomotopyGroup.homeomorphEquivOfEq`: `π_N(X, x) ≃ π_N(Y, y)` from `e : X ≃ₜ Y` with
  `e x = y`.
* `TauCeti.HomotopyGroup.homeomorphEquiv`: `π_N(X, x) ≃ π_N(Y, e x)`.
* `TauCeti.HomotopyGroup.homeomorphMulEquivOfEq`: the positive-dimensional group isomorphism
  `π_N(X, x) ≃* π_N(Y, y)`.
* `TauCeti.HomotopyGroup.homeomorphMulEquiv`: `π_N(X, x) ≃* π_N(Y, e x)`.
-/

public section

namespace TauCeti

namespace HomotopyGroup

variable {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {x : X} {y : Y}

/-- A homeomorphism `e : X ≃ₜ Y` carrying `x` to `y` induces an equivalence of homotopy groups
`π_N(X, x) ≃ π_N(Y, y)`. The forward map is `HomotopyGroup.map` of `e`; the inverse is
`HomotopyGroup.map` of `e.symm`. This holds in every dimension `N`. -/
@[expose] noncomputable def homeomorphEquivOfEq (e : X ≃ₜ Y) (h : e x = y) :
    HomotopyGroup N X x ≃ HomotopyGroup N Y y where
  toFun := map ⟨e, e.continuous⟩ h
  invFun := map ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_eq.mpr h.symm)
  left_inv a :=
    map_map_of_comp_eq_id ⟨e.symm, e.symm.continuous⟩ ⟨e, e.continuous⟩ h
      (e.symm_apply_eq.mpr h.symm)
      (ContinuousMap.ext fun t => e.symm_apply_apply t) a
  right_inv b :=
    map_map_of_comp_eq_id ⟨e, e.continuous⟩ ⟨e.symm, e.symm.continuous⟩
      (e.symm_apply_eq.mpr h.symm) h
      (ContinuousMap.ext fun t => e.apply_symm_apply t) b

@[simp]
theorem homeomorphEquivOfEq_apply (e : X ≃ₜ Y) (h : e x = y) (a : HomotopyGroup N X x) :
    homeomorphEquivOfEq e h a = map ⟨e, e.continuous⟩ h a :=
  rfl

@[simp]
theorem homeomorphEquivOfEq_symm_apply (e : X ≃ₜ Y) (h : e x = y) (b : HomotopyGroup N Y y) :
    (homeomorphEquivOfEq e h).symm b =
      map ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_eq.mpr h.symm) b :=
  rfl

/-- A homeomorphism `e : X ≃ₜ Y` induces an equivalence of homotopy groups
`π_N(X, x) ≃ π_N(Y, e x)`, in every dimension `N`. -/
@[expose] noncomputable def homeomorphEquiv (e : X ≃ₜ Y) (x : X) :
    HomotopyGroup N X x ≃ HomotopyGroup N Y (e x) :=
  homeomorphEquivOfEq e rfl

@[simp]
theorem homeomorphEquiv_apply (e : X ≃ₜ Y) (x : X) (a : HomotopyGroup N X x) :
    homeomorphEquiv e x a = map ⟨e, e.continuous⟩ rfl a :=
  rfl

@[simp]
theorem homeomorphEquiv_symm_apply (e : X ≃ₜ Y) (x : X) (b : HomotopyGroup N Y (e x)) :
    (homeomorphEquiv e x).symm b =
      map ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_apply x) b :=
  rfl

/-- A homeomorphism `e : X ≃ₜ Y` carrying `x` to `y` induces an isomorphism of homotopy groups
`π_N(X, x) ≃* π_N(Y, y)` in positive dimensions. -/
@[expose] noncomputable def homeomorphMulEquivOfEq [DecidableEq N] [Nonempty N]
    (e : X ≃ₜ Y) (h : e x = y) :
    HomotopyGroup N X x ≃* HomotopyGroup N Y y :=
  { homeomorphEquivOfEq e h with
    map_mul' := map_mul ⟨e, e.continuous⟩ h }

@[simp]
theorem homeomorphMulEquivOfEq_apply [DecidableEq N] [Nonempty N] (e : X ≃ₜ Y) (h : e x = y)
    (a : HomotopyGroup N X x) :
    homeomorphMulEquivOfEq e h a = map ⟨e, e.continuous⟩ h a :=
  rfl

@[simp]
theorem homeomorphMulEquivOfEq_symm_apply [DecidableEq N] [Nonempty N] (e : X ≃ₜ Y) (h : e x = y)
    (b : HomotopyGroup N Y y) : (homeomorphMulEquivOfEq e h).symm b =
      map ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_eq.mpr h.symm) b :=
  rfl

/-- A homeomorphism `e : X ≃ₜ Y` induces an isomorphism of homotopy groups
`π_N(X, x) ≃* π_N(Y, e x)` in positive dimensions. -/
@[expose] noncomputable def homeomorphMulEquiv [DecidableEq N] [Nonempty N] (e : X ≃ₜ Y) (x : X) :
    HomotopyGroup N X x ≃* HomotopyGroup N Y (e x) :=
  homeomorphMulEquivOfEq e rfl

@[simp]
theorem homeomorphMulEquiv_apply [DecidableEq N] [Nonempty N] (e : X ≃ₜ Y) (x : X)
    (a : HomotopyGroup N X x) :
    homeomorphMulEquiv e x a = map ⟨e, e.continuous⟩ rfl a :=
  rfl

@[simp]
theorem homeomorphMulEquiv_symm_apply [DecidableEq N] [Nonempty N] (e : X ≃ₜ Y) (x : X)
    (b : HomotopyGroup N Y (e x)) : (homeomorphMulEquiv e x).symm b =
      map ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_apply x) b :=
  rfl

end HomotopyGroup

end TauCeti
