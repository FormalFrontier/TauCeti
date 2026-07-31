/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Basic

/-!
# Lagrangian graphs in a cotangent space

A linear map `A : V → V*` determines the graph
`{(v, A v) | v ∈ V}` in the canonical symplectic vector space `V × V*`. This file proves
that its symplectic orthogonal is the graph of the flipped bilinear form and, consequently, that
the graph is Lagrangian exactly when the bilinear form `(v, w) ↦ A v w` is symmetric.

Graphs of differentials of functions are the basic exact Lagrangians in cotangent bundles. The
linear result here is their pointwise model and is a prerequisite for the cotangent-bundle examples
in Lane F3 of the analytic Heegaard Floer roadmap.

## Main declarations

* `TauCeti.SymplecticForm.orthogonal_cotangentGraph`: its symplectic orthogonal is the graph of
  the flipped map.
* `TauCeti.SymplecticForm.isIsotropic_cotangentGraph_iff`: the graph is isotropic exactly when
  the corresponding bilinear form is symmetric.
* `TauCeti.SymplecticForm.isLagrangian_cotangentGraph_iff`: the same condition characterizes
  Lagrangian graphs.

The sign convention is `ω((v, α), (w, β)) = β(v) - α(w)`, as in
`TauCeti.cotangentSymplecticForm`. The argument is the standard cotangent-space calculation;
see McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Section 3.3.
-/

public section

namespace TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

namespace SymplecticForm

variable {A : V →ₗ[ℝ] Module.Dual ℝ V}

/-- The symplectic orthogonal of the graph of `A : V → V*` is the graph of its flip.

No finite-dimensionality or reflexivity hypothesis is required: orthogonality to every
`(w, A w)` directly says that the covector component is `w ↦ A w v`. -/
@[simp]
lemma orthogonal_cotangentGraph :
    (cotangentSymplecticForm (V := V)).orthogonal A.graph = A.flip.graph := by
  ext x
  rw [mem_orthogonal_iff, LinearMap.mem_graph_iff]
  constructor
  · intro hx
    apply LinearMap.ext
    intro w
    have hw : (w, A w) ∈ A.graph := by simp [LinearMap.mem_graph_iff]
    have h := hx (w, A w) hw
    simp only [cotangentSymplecticForm_apply] at h
    exact sub_eq_zero.mp h
  · intro hx y hy
    rw [LinearMap.mem_graph_iff] at hy
    rw [cotangentSymplecticForm_apply, hy, hx]
    simp

/-- The graph of `A : V → V*` is isotropic exactly when its associated bilinear form is
symmetric. -/
@[simp]
lemma isIsotropic_cotangentGraph_iff :
    (cotangentSymplecticForm (V := V)).IsIsotropic A.graph ↔ A.IsSymm := by
  rw [isIsotropic_iff]
  constructor
  · intro h
    refine ⟨fun v w => ?_⟩
    have hv : (v, A v) ∈ A.graph := by simp [LinearMap.mem_graph_iff]
    have hw : (w, A w) ∈ A.graph := by simp [LinearMap.mem_graph_iff]
    have hvw := h (v, A v) hv (w, A w) hw
    simp only [cotangentSymplecticForm_apply] at hvw
    simpa only [RingHom.id_apply] using (sub_eq_zero.mp hvw).symm
  · intro h x hx y hy
    rw [LinearMap.mem_graph_iff] at hx hy
    rw [cotangentSymplecticForm_apply, hx, hy]
    exact sub_eq_zero.mpr (by simpa only [RingHom.id_apply] using (h.eq x.1 y.1).symm)

/-- The graph of `A : V → V*` is coisotropic exactly when its associated bilinear form is
symmetric. -/
@[simp]
lemma isCoisotropic_cotangentGraph_iff :
    (cotangentSymplecticForm (V := V)).IsCoisotropic A.graph ↔ A.IsSymm := by
  rw [isCoisotropic_iff_le, orthogonal_cotangentGraph]
  constructor
  · intro h
    refine ⟨fun v w => ?_⟩
    have hv : (v, A.flip v) ∈ A.flip.graph := by simp [LinearMap.mem_graph_iff]
    have hm := h hv
    rw [LinearMap.mem_graph_iff] at hm
    exact (LinearMap.congr_fun hm w).symm
  · intro h x hx
    rw [LinearMap.mem_graph_iff] at hx ⊢
    apply LinearMap.ext
    intro w
    rw [LinearMap.congr_fun hx w]
    exact h.eq w x.1

/-- A cotangent graph is Lagrangian exactly when the corresponding bilinear form is symmetric.

Unlike dimension-counting proofs of this familiar fact, this statement works for arbitrary real
modules: symmetry identifies the graph with its symplectic orthogonal directly. -/
@[simp]
lemma isLagrangian_cotangentGraph_iff :
    (cotangentSymplecticForm (V := V)).IsLagrangian A.graph ↔ A.IsSymm := by
  rw [isLagrangian_iff, isIsotropic_cotangentGraph_iff,
    isCoisotropic_cotangentGraph_iff, and_self]

/-- A symmetric linear map `V → V*` has Lagrangian graph in the cotangent symplectic space. -/
lemma LinearMap.IsSymm.isLagrangian_cotangentGraph (hA : A.IsSymm) :
    (cotangentSymplecticForm (V := V)).IsLagrangian A.graph :=
  isLagrangian_cotangentGraph_iff.2 hA

end SymplecticForm

end TauCeti
