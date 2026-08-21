/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# Products, transports, and graphs of Lagrangian subspaces

This file collects the linear symplectic constructions that produce isotropic, coisotropic, and
Lagrangian subspaces out of existing ones, used by the analytic Heegaard Floer roadmap before the
manifold, bundle, and Floer-boundary layers restate them in local trivializations. All three
groups are pointwise linear algebra over the symplectic-form API in
`TauCeti.Geometry.Symplectic.Lagrangian.Basic`.

* **Products.** The direct-sum symplectic form `ω₁.prod ω₂` on `V × W` has the product
  orthogonal-complement formula `(L₁ × L₂)^(ω₁ ⊕ ω₂) = L₁^ω₁ × L₂^ω₂`, so isotropy, coisotropy,
  and Lagrangian-ness of a product subspace are factorwise.
* **Transports.** A linear equivalence `e : V ≃ₗ[ℝ] W` transports a symplectic form by pulling
  arguments back along `e.symm`, sending a subspace to its image `L.map e.toLinearMap`. Symplectic
  complements commute with transport, so all three boundary predicates are invariant under linear
  coordinate changes.
* **Graphs.** In the twisted product `(V × W, ω₁ ⊖ ω₂)` the graph `{(v, e v)}` of a real-linear
  isomorphism `e : V ≃ W` is Lagrangian exactly when `e` is a symplectomorphism; the special case
  `e = id` makes the diagonal of `(V × V, ω ⊖ ω)` Lagrangian. This is the linear model of the
  Lagrangian-correspondence principle needed by Lagrangian Floer homology (Lane F3): the boundary
  conditions of Floer strips between two Lagrangians are packaged as a single Lagrangian in the
  twisted product, and the diagonal is the model boundary condition for the identity continuation.

## Main declarations

* `TauCeti.SymplecticForm.orthogonal_prod`, `isIsotropic_prod_iff`, `isCoisotropic_prod_iff`,
  `isLagrangian_prod_iff`, and the one-way `IsIsotropic.prod`, `IsCoisotropic.prod`,
  `IsLagrangian.prod`: the product API.
* `TauCeti.SymplecticForm.orthogonal_map_transport`, `isIsotropic_map_transport_iff`,
  `isCoisotropic_map_transport_iff`, `isLagrangian_map_transport_iff`, and the one-way
  `IsIsotropic.map_transport`, `IsCoisotropic.map_transport`, `IsLagrangian.map_transport`: the
  transport API.
* `TauCeti.SymplecticForm.isIsotropic_graph_iff`, `isIsotropic_linearEquiv_graph_iff`,
  `IsSymplectomorphism.isLagrangian_graph`, `isLagrangian_graph_iff`, and `isLagrangian_diagonal`:
  the graph API.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Sections 2.1 and 2.3. The twisted product form `ω₁ ⊖ ω₂` itself lives with the rest of the
product-form API in `TauCeti.Geometry.Symplectic.Prod.Basic`, and the graph is Mathlib's submodule
`LinearMap.graph`.
-/

public section

namespace TauCeti

namespace SymplecticForm

section Prod

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
variable {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W}
variable {L₁ : Submodule ℝ V} {L₂ : Submodule ℝ W}

/-- The symplectic complement of a product subspace is the product of the symplectic
complements for the direct-sum symplectic form. -/
@[simp]
lemma orthogonal_prod :
    (ω₁.prod ω₂).orthogonal (L₁.prod L₂) = (ω₁.orthogonal L₁).prod (ω₂.orthogonal L₂) := by
  ext x
  rw [mem_orthogonal_iff, Submodule.mem_prod, mem_orthogonal_iff, mem_orthogonal_iff]
  constructor
  · intro h
    constructor
    · intro y hy
      have := h (y, 0) (Submodule.mem_prod.2 ⟨hy, Submodule.zero_mem L₂⟩)
      simpa using this
    · intro y hy
      have := h (0, y) (Submodule.mem_prod.2 ⟨Submodule.zero_mem L₁, hy⟩)
      simpa using this
  · rintro ⟨h₁, h₂⟩ y hy
    rw [SymplecticForm.prod_apply]
    rw [h₁ y.1 hy.1, h₂ y.2 hy.2, add_zero]

/-- A product subspace is isotropic for the direct-sum symplectic form exactly when both factors
are isotropic. -/
@[simp]
lemma isIsotropic_prod_iff :
    (ω₁.prod ω₂).IsIsotropic (L₁.prod L₂) ↔ ω₁.IsIsotropic L₁ ∧ ω₂.IsIsotropic L₂ := by
  rw [isIsotropic_iff_le, isIsotropic_iff_le, isIsotropic_iff_le, orthogonal_prod,
    Submodule.le_prod_iff, Submodule.prod_map_fst, Submodule.prod_map_snd]

/-- The product of two isotropic subspaces is isotropic for the direct-sum symplectic form. -/
lemma IsIsotropic.prod (h₁ : ω₁.IsIsotropic L₁) (h₂ : ω₂.IsIsotropic L₂) :
    (ω₁.prod ω₂).IsIsotropic (L₁.prod L₂) :=
  isIsotropic_prod_iff.2 ⟨h₁, h₂⟩

/-- A product subspace is coisotropic for the direct-sum symplectic form exactly when both
factors are coisotropic. -/
@[simp]
lemma isCoisotropic_prod_iff :
    (ω₁.prod ω₂).IsCoisotropic (L₁.prod L₂) ↔
      ω₁.IsCoisotropic L₁ ∧ ω₂.IsCoisotropic L₂ := by
  rw [isCoisotropic_iff_le, isCoisotropic_iff_le, isCoisotropic_iff_le, orthogonal_prod,
    Submodule.le_prod_iff, Submodule.prod_map_fst, Submodule.prod_map_snd]

/-- The product of two coisotropic subspaces is coisotropic for the direct-sum symplectic form. -/
lemma IsCoisotropic.prod (h₁ : ω₁.IsCoisotropic L₁) (h₂ : ω₂.IsCoisotropic L₂) :
    (ω₁.prod ω₂).IsCoisotropic (L₁.prod L₂) :=
  isCoisotropic_prod_iff.2 ⟨h₁, h₂⟩

/-- A product subspace is Lagrangian for the direct-sum symplectic form exactly when both factors
are Lagrangian. -/
@[simp]
lemma isLagrangian_prod_iff :
    (ω₁.prod ω₂).IsLagrangian (L₁.prod L₂) ↔
      ω₁.IsLagrangian L₁ ∧ ω₂.IsLagrangian L₂ := by
  rw [isLagrangian_iff, isIsotropic_prod_iff, isCoisotropic_prod_iff,
    isLagrangian_iff, isLagrangian_iff]
  tauto

/-- The product of two Lagrangian subspaces is Lagrangian for the direct-sum symplectic form. -/
lemma IsLagrangian.prod (h₁ : ω₁.IsLagrangian L₁) (h₂ : ω₂.IsLagrangian L₂) :
    (ω₁.prod ω₂).IsLagrangian (L₁.prod L₂) :=
  isLagrangian_prod_iff.2 ⟨h₁, h₂⟩

end Prod

section Transport

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]
variable {ω : SymplecticForm V} {L : Submodule ℝ V} {e : V ≃ₗ[ℝ] W}

/-- The symplectic complement of a transported subspace is the transport of the symplectic
complement. -/
@[simp]
lemma orthogonal_map_transport :
    (ω.transport e).orthogonal (L.map e.toLinearMap) = (ω.orthogonal L).map e.toLinearMap := by
  ext w
  constructor
  · intro hw
    rw [Submodule.mem_map]
    refine ⟨e.symm w, ?_, by simp⟩
    rw [mem_orthogonal_iff]
    intro v hv
    have h := mem_orthogonal_iff.1 hw (e v)
      (Submodule.mem_map.2 ⟨v, hv, rfl⟩)
    simpa [SymplecticForm.transport_apply] using h
  · intro hw
    rw [mem_orthogonal_iff]
    intro y hy
    rcases Submodule.mem_map.1 hw with ⟨v, hv, hvw⟩
    rcases Submodule.mem_map.1 hy with ⟨x, hx, hxy⟩
    subst hvw
    subst hxy
    simpa [SymplecticForm.transport_apply] using (mem_orthogonal_iff.1 hv x hx)

/-- Isotropy is invariant under transporting both the symplectic form and the subspace along a
linear equivalence. -/
@[simp]
lemma isIsotropic_map_transport_iff :
    (ω.transport e).IsIsotropic (L.map e.toLinearMap) ↔ ω.IsIsotropic L := by
  rw [isIsotropic_iff, isIsotropic_iff]
  constructor
  · intro h x hx y hy
    have hxy := h (e x) (Submodule.mem_map.2 ⟨x, hx, rfl⟩)
      (e y) (Submodule.mem_map.2 ⟨y, hy, rfl⟩)
    simpa [SymplecticForm.transport_apply] using hxy
  · intro h x hx y hy
    rcases Submodule.mem_map.1 hx with ⟨x', hx', rfl⟩
    rcases Submodule.mem_map.1 hy with ⟨y', hy', rfl⟩
    simpa [SymplecticForm.transport_apply] using h x' hx' y' hy'

/-- Coisotropy is invariant under transporting both the symplectic form and the subspace along a
linear equivalence. -/
@[simp]
lemma isCoisotropic_map_transport_iff :
    (ω.transport e).IsCoisotropic (L.map e.toLinearMap) ↔ ω.IsCoisotropic L := by
  rw [isCoisotropic_iff, isCoisotropic_iff]
  constructor
  · intro h x hx
    have hx' : e x ∈ (ω.transport e).orthogonal (L.map e.toLinearMap) := by
      rw [orthogonal_map_transport]
      exact Submodule.mem_map.2 ⟨x, hx, rfl⟩
    rcases Submodule.mem_map.1 (h (e x) hx') with ⟨y, hy, hyx⟩
    have : y = x := by simpa using congrArg e.symm hyx
    simpa [this] using hy
  · intro h y hy
    rw [orthogonal_map_transport] at hy
    rcases Submodule.mem_map.1 hy with ⟨x, hx, rfl⟩
    exact Submodule.mem_map.2 ⟨x, h x hx, rfl⟩

/-- Lagrangian-ness is invariant under transporting both the symplectic form and the subspace
along a linear equivalence. -/
@[simp]
lemma isLagrangian_map_transport_iff :
    (ω.transport e).IsLagrangian (L.map e.toLinearMap) ↔ ω.IsLagrangian L := by
  rw [isLagrangian_iff, isLagrangian_iff, isIsotropic_map_transport_iff,
    isCoisotropic_map_transport_iff]

namespace IsIsotropic

/-- Transport an isotropic subspace along a linear equivalence, together with the transported
symplectic form. -/
lemma map_transport (h : ω.IsIsotropic L) :
    (ω.transport e).IsIsotropic (L.map e.toLinearMap) :=
  isIsotropic_map_transport_iff.2 h

end IsIsotropic

namespace IsCoisotropic

/-- Transport a coisotropic subspace along a linear equivalence, together with the transported
symplectic form. -/
lemma map_transport (h : ω.IsCoisotropic L) :
    (ω.transport e).IsCoisotropic (L.map e.toLinearMap) :=
  isCoisotropic_map_transport_iff.2 h

end IsCoisotropic

namespace IsLagrangian

/-- Transport a Lagrangian subspace along a linear equivalence, together with the transported
symplectic form. -/
lemma map_transport (h : ω.IsLagrangian L) :
    (ω.transport e).IsLagrangian (L.map e.toLinearMap) :=
  isLagrangian_map_transport_iff.2 h

end IsLagrangian

end Transport

section Graph

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
variable {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W}

/-- The graph of `f` is isotropic for the twisted product form iff `f` preserves the symplectic
forms pointwise: `ω₂(f v, f w) = ω₁(v, w)`. -/
@[simp]
lemma isIsotropic_graph_iff {f : V →ₗ[ℝ] W} :
    (twistedProd ω₁ ω₂).IsIsotropic f.graph ↔ ∀ v w, ω₂ (f v) (f w) = ω₁ v w := by
  rw [isIsotropic_iff]
  constructor
  · intro h v w
    have hv : ((v, f v) : V × W) ∈ f.graph := by simp [LinearMap.mem_graph_iff]
    have hw : ((w, f w) : V × W) ∈ f.graph := by simp [LinearMap.mem_graph_iff]
    have hvw := h (v, f v) hv (w, f w) hw
    simp only [twistedProd_apply] at hvw
    linarith
  · intro h p hp q hq
    rw [LinearMap.mem_graph_iff] at hp hq
    rw [twistedProd_apply, hp, hq]
    linarith [h p.1 q.1]

/-- The graph of `e` is isotropic for the twisted product form iff `e` is a symplectomorphism.

This is a plain bridging lemma, not a `simp` lemma: the general `isIsotropic_graph_iff` already
puts graph isotropy into its own normal form, so marking this `@[simp]` too would leave two
competing normal forms for `e.toLinearMap.graph`. -/
lemma isIsotropic_linearEquiv_graph_iff {e : V ≃ₗ[ℝ] W} :
    (twistedProd ω₁ ω₂).IsIsotropic e.toLinearMap.graph ↔ IsSymplectomorphism ω₁ ω₂ e := by
  rw [isIsotropic_graph_iff]
  constructor
  · intro h
    exact isSymplectomorphism_iff.2 fun v w => h v w
  · intro h v w
    exact h.apply v w

/-- The graph of a symplectomorphism `e : V ≃ₗ[ℝ] W` is a Lagrangian subspace of the twisted
product `(V × W, ω₁ ⊖ ω₂)`. No finite-dimensionality is required. -/
lemma IsSymplectomorphism.isLagrangian_graph {e : V ≃ₗ[ℝ] W} (h : IsSymplectomorphism ω₁ ω₂ e) :
    (twistedProd ω₁ ω₂).IsLagrangian e.toLinearMap.graph := by
  rw [isLagrangian_iff]
  refine ⟨isIsotropic_linearEquiv_graph_iff.2 h, ?_⟩
  rw [isCoisotropic_iff]
  intro x hx
  rw [mem_orthogonal_iff] at hx
  -- For every `w`, testing against `(w, e w) ∈ graph` gives `ω₁ w x.1 = ω₂ (e w) x.2`.
  have key : ∀ w : V, ω₁ w x.1 - ω₂ (e w) x.2 = 0 := by
    intro w
    have hw : ((w, e w) : V × W) ∈ e.toLinearMap.graph := by simp [LinearMap.mem_graph_iff]
    have hthis := hx (w, e w) hw
    simp only [twistedProd_apply] at hthis
    exact hthis
  -- Rewrite `ω₂ (e w) x.2 = ω₁ w (e.symm x.2)`, so `ω₁ w (x.1 - e.symm x.2) = 0` for all `w`.
  have key2 : ∀ w : V, (ω₁.toBilinForm w) (x.1 - e.symm x.2) = 0 := by
    intro w
    have hb : ω₂ (e w) x.2 = ω₁ w (e.symm x.2) := by
      have hh := h.apply w (e.symm x.2)
      rwa [e.apply_symm_apply] at hh
    have hk := key w
    rw [hb] at hk
    rw [map_sub]
    exact hk
  have hz : x.1 - e.symm x.2 = 0 := ω₁.separatingRight _ key2
  have hx1 : x.1 = e.symm x.2 := sub_eq_zero.mp hz
  rw [LinearMap.mem_graph_iff]
  simp [hx1]

/-- The graph of `e` is Lagrangian for the twisted product form iff `e` is a symplectomorphism. -/
@[simp]
lemma isLagrangian_graph_iff {e : V ≃ₗ[ℝ] W} :
    (twistedProd ω₁ ω₂).IsLagrangian e.toLinearMap.graph ↔ IsSymplectomorphism ω₁ ω₂ e :=
  ⟨fun h => isIsotropic_linearEquiv_graph_iff.1 h.isIsotropic,
    IsSymplectomorphism.isLagrangian_graph⟩

/-- The diagonal of `(V × V, ω ⊖ ω)`, realized as the graph of the identity equivalence, is
Lagrangian. This is the boundary condition modeled by the identity continuation in Lagrangian
Floer homology. -/
lemma isLagrangian_diagonal (ω : SymplecticForm V) :
    (twistedProd ω ω).IsLagrangian (LinearEquiv.refl ℝ V).toLinearMap.graph :=
  (IsSymplectomorphism.refl ω).isLagrangian_graph

end Graph

end SymplecticForm

end TauCeti
