/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.Finiteness.Prod
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Basis
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise

/-!
# Dimension of the componentwise zigzag algebra

The public zigzag algebra of a finite simple graph is a product over connected components.  A
component containing an edge uses the path-algebra quotient, whose vertex--arrow--volume basis is
already available, while an isolated vertex uses the dual numbers.  Both cases have dimension
twice the number of vertices plus twice the number of edges.

Summing the component dimensions gives the uniform formula

```text
dim_k Z_k(G) = 2 |V(G)| + 2 |E(G)|
```

for every finite simple graph, including the empty graph and graphs with isolated vertices.  The
proof counts vertices and oriented edges componentwise; this makes explicit why replacing the
coefficient ring by dual numbers on singleton components restores the missing volume class.

## Main results

* `TauCeti.finrank_zigzagComponentAlgebra`: the dimension of one component factor.
* `TauCeti.finrank_zigzagAlgebra`: the dimension of the public componentwise zigzag algebra.
* `TauCeti.finrank_zigzagAlgebra_A1`: the rank-one zigzag algebra has dimension two.

## References

See Huerfano--Khovanov, *A category for the adjoint representation*, Section 3, and
Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.
-/

public section

namespace TauCeti

open SimpleGraph

universe u w

variable (k : Type w) {V : Type u} (G : SimpleGraph V)

section Component

variable [CommRing k] [Finite V]

/-- Each component factor of a finite graph's zigzag algebra is free over the coefficient ring. -/
noncomputable instance instFreeZigzagComponentAlgebra (C : G.ConnectedComponent) :
    Module.Free k (zigzagComponentAlgebra k G C) := by
  classical
  by_cases hC : Nontrivial C
  · let _ : Nontrivial C := hC
    rw [zigzagComponentAlgebra_eq_nonisolated]
    exact Module.Free.of_basis <| zigzagBasis k C.toSimpleGraph fun i =>
      exists_adj_iff_not_isIsolated.mpr
        (C.connected_toSimpleGraph.preconnected.not_isIsolated i)
  · let _ : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
    rw [zigzagComponentAlgebra_eq_uliftDualNumber]
    -- Mathlib exposes `DualNumber k` as `TrivSqZeroExt k k`, whose carrier is `k × k`, and defines
    -- its module structure as `inferInstanceAs <| Module k (k × k)`; both definitions are public
    -- and marked `@[expose]`.  There is no `Module.Free`/`Module.Finite` instance or linear
    -- equivalence for `TrivSqZeroExt` in Mathlib, so this public representation is the only route.
    change Module.Free k (ULift (k × k))
    infer_instance

/-- Each component factor of a finite graph's zigzag algebra is finite over the coefficient ring. -/
noncomputable instance instFiniteZigzagComponentAlgebra (C : G.ConnectedComponent) :
    Module.Finite k (zigzagComponentAlgebra k G C) := by
  classical
  by_cases hC : Nontrivial C
  · let _ : Nontrivial C := hC
    rw [zigzagComponentAlgebra_eq_nonisolated]
    let _ : Fintype C := Fintype.ofFinite C
    let _ : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    let _ : Fintype C.toSimpleGraph.Dart := Dart.fintype
    exact Module.Finite.of_basis <| zigzagBasis k C.toSimpleGraph fun i =>
      exists_adj_iff_not_isIsolated.mpr
        (C.connected_toSimpleGraph.preconnected.not_isIsolated i)
  · let _ : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
    rw [zigzagComponentAlgebra_eq_uliftDualNumber]
    -- Mathlib exposes `DualNumber k` as `TrivSqZeroExt k k`, whose carrier is `k × k`, and defines
    -- its module structure as `inferInstanceAs <| Module k (k × k)`; both definitions are public
    -- and marked `@[expose]`.  There is no `Module.Free`/`Module.Finite` instance or linear
    -- equivalence for `TrivSqZeroExt` in Mathlib, so this public representation is the only route.
    change Module.Finite k (ULift (k × k))
    infer_instance

variable [Nontrivial k]

/-- The component factor of a zigzag algebra has dimension twice its number of vertices plus its
number of darts, equivalently twice its number of edges.  On a nontrivial component this is the
vertex--arrow--volume basis count; on a singleton component it is the two-dimensional dual-number
factor. -/
@[simp]
theorem finrank_zigzagComponentAlgebra (C : G.ConnectedComponent) :
    Module.finrank k (zigzagComponentAlgebra k G C) =
      2 * Nat.card C + Nat.card C.toSimpleGraph.Dart := by
  classical
  by_cases hC : Nontrivial C
  · let _ : Nontrivial C := hC
    rw [zigzagComponentAlgebra_eq_nonisolated]
    let _ : Fintype C := Fintype.ofFinite C
    let _ : Fintype C.toSimpleGraph.Dart := Dart.fintype
    rw [finrank_nonisolatedZigzagQuotient_of_preconnected k C.toSimpleGraph
      C.connected_toSimpleGraph.preconnected,
      ← C.toSimpleGraph.dart_card_eq_twice_card_edges]
    simp only [Nat.card_eq_fintype_card]
  · let _ : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
    rw [zigzagComponentAlgebra_eq_uliftDualNumber, finrank_ulift]
    let c : C := ⟨C.nonempty_supp.some, C.nonempty_supp.some_mem⟩
    let _ : Inhabited C := ⟨c⟩
    let _ : Unique C := Unique.mk' C
    let _ : IsEmpty C.toSimpleGraph.Dart :=
      ⟨fun d => d.fst_ne_snd (Subsingleton.elim d.fst d.snd)⟩
    -- As above, `DualNumber k` is `TrivSqZeroExt k k`, whose exposed carrier is `k × k`, so this
    -- reduction uses Mathlib's public representation.
    change Module.finrank k (k × k) = _
    rw [Module.finrank_prod]
    simp

end Component

section FiniteGraph

variable [CommRing k] [Finite V]

private noncomputable def zigzagAlgebraLinearEquiv :
    (zigzagAlgebra k G).carrier ≃ₗ[k]
      (∀ C : G.ConnectedComponent, zigzagComponentAlgebra k G C) :=
  { toFun := fun x C => zigzagComponentProjection k G C x
    invFun := zigzagAlgebraMk k G
    left_inv := zigzagAlgebra.mk_projections k G
    right_inv := fun _ => funext fun _ => zigzagComponentProjection_zigzagAlgebraMk k G _ _
    map_add' := fun x y => funext fun C => (zigzagComponentProjection k G C).map_add x y
    map_smul' := fun r x => funext fun C =>
      (zigzagComponentProjection k G C).toLinearMap.map_smul r x }

/-- The zigzag algebra of a finite graph is free over the coefficient ring. -/
noncomputable instance instFreeZigzagAlgebra : Module.Free k (zigzagAlgebra k G) :=
  Module.Free.of_equiv (zigzagAlgebraLinearEquiv k G).symm

/-- The zigzag algebra of a finite graph is finite over the coefficient ring. -/
noncomputable instance instFiniteZigzagAlgebra : Module.Finite k (zigzagAlgebra k G) :=
  Module.Finite.equiv (zigzagAlgebraLinearEquiv k G).symm

variable [Nontrivial k] [Fintype V] [DecidableRel G.Adj]

/-- **Dimension of the public zigzag algebra.**  For every finite simple graph, including graphs
with isolated vertices, `dim Z(G) = 2|V| + 2|E|`.  Every vertex contributes an idempotent and a
volume class, while every undirected edge contributes its two orientations. -/
@[simp]
theorem finrank_zigzagAlgebra :
    Module.finrank k (zigzagAlgebra k G) =
      2 * Fintype.card V + 2 * G.edgeFinset.card := by
  classical
  have hvertex : ∑ C : G.ConnectedComponent, Nat.card C = Nat.card V := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv G.connectedComponentMk)
  let fiberEquiv (C : G.ConnectedComponent) :
      C.toSimpleGraph.Dart ≃ {d : G.Dart // G.connectedComponentMk d.fst = C} :=
    { toFun := fun d => ⟨⟨(d.fst.1, d.snd.1), d.adj⟩, d.fst.property⟩
      invFun := fun d =>
        ⟨(⟨d.1.fst, d.property⟩,
          ⟨d.1.snd, C.mem_supp_of_adj_mem_supp d.property d.1.adj⟩), d.1.adj⟩
      left_inv := fun d => by
        apply Dart.ext
        rfl
      right_inv := fun d => by
        apply Subtype.ext
        apply Dart.ext
        rfl }
  have hdart :
      ∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.Dart = Nat.card G.Dart := by
    let e : (Σ C : G.ConnectedComponent, C.toSimpleGraph.Dart) ≃ G.Dart :=
      (Equiv.sigmaCongrRight fiberEquiv).trans (Equiv.sigmaFiberEquiv fun d : G.Dart =>
        G.connectedComponentMk d.fst)
    let _ (C : G.ConnectedComponent) : Finite C.toSimpleGraph.Dart :=
      Finite.of_equiv {d : G.Dart // G.connectedComponentMk d.fst = C} (fiberEquiv C).symm
    rw [← Nat.card_sigma]
    exact Nat.card_congr e
  -- `zigzagAlgebra` is opaque across the public import, so use its public projections and
  -- reconstruction map to expose the dependent product to the standard finrank theorem.
  change Module.finrank k (zigzagAlgebra k G).carrier = _
  rw [(zigzagAlgebraLinearEquiv k G).finrank_eq, Module.finrank_pi_fintype]
  simp_rw [finrank_zigzagComponentAlgebra k G]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hvertex, hdart, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, G.dart_card_eq_twice_card_edges]

/-- The public zigzag algebra of the one-vertex graph has dimension two.  This is the dimension
check for the `A₁` convention: its unique component is the dual numbers, not the coefficient
field produced by the uniform path quotient. -/
theorem finrank_zigzagAlgebra_A1 :
    Module.finrank k (zigzagAlgebra k (⊥ : SimpleGraph (Fin 1))) = 2 := by
  rw [finrank_zigzagAlgebra]
  simp

end FiniteGraph

end TauCeti
