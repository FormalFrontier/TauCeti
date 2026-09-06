/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearPMap
import TauCeti.LinearAlgebra.LinearPMap.Basic

/-!
# Restriction of scalars for partial linear maps

A partial linear map `A : E →ₗ.[R] F` over a ring `R` is in particular linear over any ring `S`
acting compatibly through `R`, with the same domain and the same values.  This file records that
restriction, `LinearPMap.restrictScalars S A`, the partial-map analogue of
`Submodule.restrictScalars` and `LinearMap.restrictScalars`.  Its purpose is to let operator
properties defined over a smaller scalar ring be applied to operators over a larger one; the
motivating case is `S = ℝ`, `R = ℂ`, where the real-Banach-first semigroup development of Tau Ceti
(dissipativity, generation of C₀-semigroups) is applied to operators on a complex Hilbert space.
Since domain and action are preserved, membership and evaluation transport back and forth without
change, and negation commutes with the restriction.

## Main declarations

* `LinearPMap.restrictScalars`: the restriction of a partial linear map to a smaller scalar ring.
* `LinearPMap.mem_restrictScalars_domain` and `LinearPMap.restrictScalars_apply`: domain
  membership and evaluation agree with those of the original map.
* `LinearPMap.restrictScalars_neg` and `LinearPMap.restrictScalars_smul`: restriction of scalars
  commutes with negation and with scalar multiplication of the map.
* `LinearPMap.restrictScalars_graph` and `LinearPMap.congr_fun_restrictScalars`: the graph is the
  restriction of scalars of the graph, and a map equal to a restriction takes the restricted map's
  values.
-/

public section

noncomputable section

namespace LinearPMap

variable (S : Type*) {R E F : Type*} [Ring R] [Ring S] [AddCommGroup E] [AddCommGroup F]
  [Module R E] [Module R F] [Module S E] [Module S F] [SMul S R] [IsScalarTower S R E]
  [IsScalarTower S R F]

/-- A partial linear map over `R`, regarded as a partial linear map over the smaller scalar ring
`S`, with the same domain and values. -/
def restrictScalars (A : E →ₗ.[R] F) : E →ₗ.[S] F where
  domain := A.domain.restrictScalars S
  toFun := A.toFun.restrictScalars S

@[simp]
theorem restrictScalars_domain (A : E →ₗ.[R] F) :
    (A.restrictScalars S).domain = A.domain.restrictScalars S :=
  (rfl)

/-- Membership in the domain of the restriction is membership in the domain of `A`.  This is
what `simp` proves from `restrictScalars_domain`, packaged for use in proof terms. -/
theorem mem_restrictScalars_domain (A : E →ₗ.[R] F) {x : E} :
    x ∈ (A.restrictScalars S).domain ↔ x ∈ A.domain := by
  rw [restrictScalars_domain, Submodule.restrictScalars_mem]

/-- The restriction takes the values of `A`. -/
@[simp]
theorem restrictScalars_apply (A : E →ₗ.[R] F) (x : (A.restrictScalars S).domain) :
    A.restrictScalars S x = A ⟨x, (A.mem_restrictScalars_domain S).mp x.property⟩ :=
  (rfl)

/-- Restriction of scalars commutes with negation. -/
@[simp]
theorem restrictScalars_neg (A : E →ₗ.[R] F) :
    (-A).restrictScalars S = -(A.restrictScalars S) :=
  LinearPMap.ext rfl fun _ _ _ => rfl

/-- Restriction of scalars commutes with scalar multiplication of the map. -/
@[simp]
theorem restrictScalars_smul {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass R M F]
    [SMulCommClass S M F] (a : M) (A : E →ₗ.[R] F) :
    (a • A).restrictScalars S = a • A.restrictScalars S :=
  LinearPMap.ext rfl fun _ _ _ => rfl


/-- The graph of the restriction of scalars is the restriction of scalars of the graph. -/
@[simp]
theorem restrictScalars_graph (A : E →ₗ.[R] F) :
    (A.restrictScalars S).graph = A.graph.restrictScalars S := by
  ext p
  simp only [Submodule.restrictScalars_mem, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨x, hx1, hx2⟩
    rw [A.restrictScalars_apply S] at hx2
    exact ⟨⟨x, (A.mem_restrictScalars_domain S).mp x.property⟩, hx1, hx2⟩
  · rintro ⟨x, hx1, hx2⟩
    exact ⟨⟨x, (A.mem_restrictScalars_domain S).mpr x.property⟩, hx1,
      by rw [A.restrictScalars_apply S]; exact hx2⟩

/-- Restricting scalars does not change the graph, as a set. -/
theorem restrictScalars_coe_graph (A : E →ₗ.[R] F) :
    ((A.restrictScalars S).graph : Set (E × F)) = (A.graph : Set (E × F)) := by
  rw [restrictScalars_graph, Submodule.coe_restrictScalars]

/-- A partial linear map equal to a restriction of scalars takes the values of the restricted
map. -/
theorem congr_fun_restrictScalars {B : E →ₗ.[S] F} {A : E →ₗ.[R] F}
    (h : B = A.restrictScalars S) {x : E} (hx : x ∈ B.domain) (hxA : x ∈ A.domain) :
    B ⟨x, hx⟩ = A ⟨x, hxA⟩ :=
  (congr_fun h hx ((A.mem_restrictScalars_domain S).mpr hxA)).trans
    (A.restrictScalars_apply S _)

end LinearPMap

end
