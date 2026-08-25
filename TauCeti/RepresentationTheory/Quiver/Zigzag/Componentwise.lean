/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.DualNumber
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Connected
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Isomorphism

/-!
# The componentwise zigzag algebra

The uniform path-algebra quotient `TauCeti.nonisolatedZigzagQuotient` gives the intended zigzag
algebra on a connected graph with an edge, but gives only the coefficient field on an isolated
vertex.  The Huerfano--Khovanov convention instead assigns the dual numbers to a one-vertex
component.  This file makes that distinction in the public definition: `TauCeti.zigzagAlgebra`
is the product of the appropriate algebra over the connected components of the graph.

The component algebra is packaged in `AlgCat` because its carrier changes between the singleton
and non-singleton cases.  The public algebra is the product of those carriers, exposed through
component projections and extensionality.  For a connected nontrivial graph, the product has one
factor and is canonically isomorphic to the landed relation quotient.  For the one-vertex graph it
is canonically the dual numbers from Mathlib.

## Main definitions

* `TauCeti.zigzagComponentAlgebra`: the algebra assigned to one connected component.
* `TauCeti.zigzagAlgebra`: the public zigzag algebra of an arbitrary finite simple graph.
* `TauCeti.zigzagAlgebraEquivNonisolated`: comparison with the relation quotient for a connected
  graph with at least two vertices.
* `TauCeti.zigzagAlgebraEquivA1`: the one-vertex zigzag algebra is the dual numbers.

## References

This is the componentwise public-algebra target in Layers 0 and 1 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`.  The low-rank convention follows
Huerfano--Khovanov, *A category for the adjoint representation*, Section 3.  The dual-number
implementation is Mathlib's `DualNumber`, rather than a duplicate polynomial-quotient model.
-/

public section

namespace TauCeti

universe u v w

open SimpleGraph

variable (k : Type w) [Field k] {V : Type u} [Finite V] (G : SimpleGraph V)

/-- The zigzag algebra assigned to one connected component.  A singleton component carries the
dual numbers; a component with more than one vertex carries the uniform zigzag relation quotient
of its induced graph. -/
noncomputable def zigzagComponentAlgebra (C : G.ConnectedComponent) : AlgCat k :=
  by
    classical
    exact if Nontrivial C then
      AlgCat.of k (nonisolatedZigzagQuotient k C.toSimpleGraph)
    else
      AlgCat.of k (ULift.{u} (DualNumber k))

/-- On a nontrivial connected component, the component algebra is the uniform relation quotient. -/
@[simp]
theorem zigzagComponentAlgebra_eq_nonisolated (C : G.ConnectedComponent) [Nontrivial C] :
    zigzagComponentAlgebra k G C =
      AlgCat.of k (nonisolatedZigzagQuotient k C.toSimpleGraph) := by
  rw [zigzagComponentAlgebra]
  split
  · rfl
  · rename_i h
    exact (h inferInstance).elim

/-- On a singleton connected component, the component algebra is a universe lift of the dual
numbers. -/
@[simp]
theorem zigzagComponentAlgebra_eq_uliftDualNumber (C : G.ConnectedComponent) [Subsingleton C] :
    zigzagComponentAlgebra k G C = AlgCat.of k (ULift.{u} (DualNumber k)) := by
  rw [zigzagComponentAlgebra]
  split
  · rename_i h
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance h).elim
  · rfl

/-- The component algebra of a nontrivial component, as an algebra equivalence rather than an
equality of bundled objects. -/
noncomputable def zigzagComponentAlgebraEquivNonisolated (C : G.ConnectedComponent)
    [Nontrivial C] :
    zigzagComponentAlgebra k G C ≃ₐ[k] nonisolatedZigzagQuotient k C.toSimpleGraph :=
  CategoryTheory.Iso.toAlgEquiv <|
    CategoryTheory.eqToIso (zigzagComponentAlgebra_eq_nonisolated k G C)

/-- The component algebra of a singleton component is a universe lift of the dual numbers. -/
noncomputable def zigzagComponentAlgebraEquivULiftDualNumber (C : G.ConnectedComponent)
    [Subsingleton C] : zigzagComponentAlgebra k G C ≃ₐ[k] ULift.{u} (DualNumber k) :=
  CategoryTheory.Iso.toAlgEquiv <|
    CategoryTheory.eqToIso (zigzagComponentAlgebra_eq_uliftDualNumber k G C)

/-- The public zigzag algebra of a finite simple graph: the product of its component algebras,
using dual numbers precisely on singleton components. -/
noncomputable def zigzagAlgebra : AlgCat k :=
  AlgCat.of k (∀ C : G.ConnectedComponent, zigzagComponentAlgebra k G C)

/-- Projection from the public zigzag algebra to the factor indexed by a connected component. -/
noncomputable def zigzagComponentProjection (C : G.ConnectedComponent) :
    zigzagAlgebra k G →ₐ[k] zigzagComponentAlgebra k G C := by
  unfold zigzagAlgebra
  exact Pi.evalAlgHom k (fun C : G.ConnectedComponent ↦ zigzagComponentAlgebra k G C) C

/-- Elements of the public zigzag algebra are equal when all their component projections agree. -/
@[ext]
theorem zigzagAlgebra_ext {x y : zigzagAlgebra k G}
    (h : ∀ C, zigzagComponentProjection k G C x = zigzagComponentProjection k G C y) : x = y := by
  unfold zigzagAlgebra at x y
  exact funext h

/-- Evaluation identifies a dependent product of algebras over a one-point index type with its
unique factor. -/
private noncomputable def algEquivPiUnique {ι : Type*} [Unique ι] (A : ι → AlgCat k) :
    (∀ i, A i) ≃ₐ[k] A default :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.piUnique fun i ↦ A i) (by intro; rfl)

/-- The unique structure on the connected-component type of a connected graph, based at a
specified witness vertex. -/
private noncomputable abbrev connectedComponentUnique (hconn : G.Connected) :
    Unique G.ConnectedComponent where
  default := G.connectedComponentMk hconn.nonempty.some
  uniq _ := hconn.preconnected.subsingleton_connectedComponent.elim _ _

/-- For a connected graph, the induced graph on any one of its connected components is
canonically isomorphic to the original graph by forgetting the membership proof. -/
noncomputable def connectedComponentGraphIso (hconn : G.Connected)
    (C : G.ConnectedComponent) : C.toSimpleGraph ≃g G where
  toEquiv :=
    { toFun := Subtype.val
      invFun := fun v ↦ ⟨v, by
        obtain ⟨w, hw⟩ := C.nonempty_supp
        exact (ConnectedComponent.sound (hconn.preconnected v w)).trans hw⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  map_rel_iff' := Iff.rfl

omit [Finite V] in
/-- Every connected component of a connected graph on a nontrivial vertex type is nontrivial. -/
theorem connectedComponent_nontrivial (hconn : G.Connected) [Nontrivial V]
    (C : G.ConnectedComponent) : Nontrivial C := by
  let e := (connectedComponentGraphIso G hconn C).toEquiv
  exact (Equiv.nontrivial_congr e).mpr inferInstance

/-! ### Invariance under graph isomorphism -/

/-- A graph isomorphism restricts to an isomorphism between the induced graphs on corresponding
connected components. -/
private def connectedComponentGraphIsoOfIso {W : Type v} {H : SimpleGraph W} (e : G ≃g H)
    (C : G.ConnectedComponent) :
    C.toSimpleGraph ≃g (e.connectedComponentEquiv C).toSimpleGraph where
  toEquiv := C.isoEquivSupp e
  map_rel_iff' := e.map_rel_iff

/-- The algebras attached to corresponding connected components are invariant under graph
isomorphism.  In the nontrivial case this is the landed invariance of the relation quotient; in
the singleton case both sides are universe lifts of Mathlib's dual numbers. -/
noncomputable def zigzagComponentAlgebraEquiv {W : Type v} [Finite W]
    {H : SimpleGraph W} (e : G ≃g H) (C : G.ConnectedComponent) :
    zigzagComponentAlgebra k G C ≃ₐ[k]
      zigzagComponentAlgebra k H (e.connectedComponentEquiv C) := by
  classical
  by_cases hC : Nontrivial C
  · letI : Nontrivial C := hC
    letI : Nontrivial (e.connectedComponentEquiv C) :=
      (Equiv.nontrivial_congr (C.isoEquivSupp e)).mp hC
    exact (zigzagComponentAlgebraEquivNonisolated k G C).trans <|
      (nonisolatedZigzagQuotientEquiv k (connectedComponentGraphIsoOfIso G e C)).trans <|
        (zigzagComponentAlgebraEquivNonisolated k H (e.connectedComponentEquiv C)).symm
  · letI : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
    letI : Subsingleton (e.connectedComponentEquiv C) :=
      (Equiv.subsingleton_congr (C.isoEquivSupp e)).mp inferInstance
    exact (zigzagComponentAlgebraEquivULiftDualNumber k G C).trans <|
      (ULift.algEquiv (R := k) (A := DualNumber k)).trans <|
        ((ULift.algEquiv (R := k) (A := DualNumber k)).symm.trans <|
          (zigzagComponentAlgebraEquivULiftDualNumber k H
            (e.connectedComponentEquiv C)).symm)

/-- **The public zigzag algebra is invariant under graph isomorphism.**  The isomorphism relabels
the connected-component factors and applies the corresponding component-algebra isomorphism in
each factor. -/
noncomputable def zigzagAlgebraEquiv {W : Type v} [Finite W] {H : SimpleGraph W} (e : G ≃g H) :
    zigzagAlgebra k G ≃ₐ[k] zigzagAlgebra k H := by
  unfold zigzagAlgebra
  exact (AlgEquiv.piCongrRight fun C ↦ zigzagComponentAlgebraEquiv k G e C).trans <|
    AlgEquiv.piCongrLeft k (fun D : H.ConnectedComponent ↦ zigzagComponentAlgebra k H D)
      e.connectedComponentEquiv

/-- The graph-isomorphism comparison acts on a corresponding component through the component
algebra isomorphism. -/
@[simp]
theorem zigzagAlgebraEquiv_apply_component {W : Type v} [Finite W] {H : SimpleGraph W}
    (e : G ≃g H) (x : zigzagAlgebra k G) (C : G.ConnectedComponent) :
    zigzagComponentProjection k H (e.connectedComponentEquiv C) (zigzagAlgebraEquiv k G e x) =
      zigzagComponentAlgebraEquiv k G e C (zigzagComponentProjection k G C x) := by
  unfold zigzagAlgebra at x
  unfold zigzagComponentProjection zigzagAlgebraEquiv zigzagAlgebra
  simp

/-- On a connected graph with at least two vertices, the public componentwise zigzag algebra is
canonically isomorphic to the uniform relation quotient. -/
noncomputable def zigzagAlgebraEquivNonisolated (hconn : G.Connected) [Nontrivial V] :
    zigzagAlgebra k G ≃ₐ[k] nonisolatedZigzagQuotient k G := by
  unfold zigzagAlgebra
  letI := connectedComponentUnique G hconn
  letI : Nontrivial (default : G.ConnectedComponent) :=
    connectedComponent_nontrivial G hconn default
  refine (algEquivPiUnique k (fun C : G.ConnectedComponent ↦
    zigzagComponentAlgebra k G C)).trans <|
      (zigzagComponentAlgebraEquivNonisolated k G default).trans ?_
  exact nonisolatedZigzagQuotientEquiv k (connectedComponentGraphIso G hconn default)

/-- The connected nonisolated comparison evaluates through any connected-component factor and
the canonical graph isomorphism from that factor to the original graph. -/
theorem zigzagAlgebraEquivNonisolated_apply (hconn : G.Connected) [Nontrivial V]
    (x : zigzagAlgebra k G) (C : G.ConnectedComponent) :
    zigzagAlgebraEquivNonisolated k G hconn x =
      let _ := connectedComponent_nontrivial G hconn C
      nonisolatedZigzagQuotientEquiv k (connectedComponentGraphIso G hconn C)
        (zigzagComponentAlgebraEquivNonisolated k G C
          (zigzagComponentProjection k G C x)) := by
  let _ := connectedComponentUnique G hconn
  have hC : C = default := Subsingleton.elim _ _
  subst C
  unfold zigzagAlgebra at x
  rfl

/-- The inverse connected nonisolated comparison is computed componentwise by the inverse graph
and component equivalences. -/
@[simp]
theorem zigzagAlgebraEquivNonisolated_symm_apply_component (hconn : G.Connected)
    [Nontrivial V] (x : nonisolatedZigzagQuotient k G) (C : G.ConnectedComponent) :
    zigzagComponentProjection k G C ((zigzagAlgebraEquivNonisolated k G hconn).symm x) =
      let _ := connectedComponent_nontrivial G hconn C
      (zigzagComponentAlgebraEquivNonisolated k G C).symm
        ((nonisolatedZigzagQuotientEquiv k
          (connectedComponentGraphIso G hconn C)).symm x) := by
  let _ := connectedComponent_nontrivial G hconn C
  apply (zigzagComponentAlgebraEquivNonisolated k G C).injective
  rw [AlgEquiv.apply_symm_apply]
  apply (nonisolatedZigzagQuotientEquiv k
    (connectedComponentGraphIso G hconn C)).injective
  rw [AlgEquiv.apply_symm_apply, ← zigzagAlgebraEquivNonisolated_apply]
  exact (zigzagAlgebraEquivNonisolated k G hconn).apply_symm_apply x

/-- The public zigzag algebra of the one-vertex graph is the algebra of dual numbers. -/
noncomputable def zigzagAlgebraEquivA1 :
    zigzagAlgebra k (⊥ : SimpleGraph (Fin 1)) ≃ₐ[k] DualNumber k := by
  unfold zigzagAlgebra
  let A := fun C : (⊥ : SimpleGraph (Fin 1)).ConnectedComponent ↦
    zigzagComponentAlgebra k (⊥ : SimpleGraph (Fin 1)) C
  refine (algEquivPiUnique k A).trans <|
    (zigzagComponentAlgebraEquivULiftDualNumber k (⊥ : SimpleGraph (Fin 1)) default).trans ?_
  exact ULift.algEquiv (R := k) (A := DualNumber k)

/-- The rank-one comparison evaluates the unique component and then lowers the universe lift. -/
@[simp]
theorem zigzagAlgebraEquivA1_apply (x : zigzagAlgebra k (⊥ : SimpleGraph (Fin 1))) :
    zigzagAlgebraEquivA1 k x =
      ULift.down (zigzagComponentAlgebraEquivULiftDualNumber k
        (⊥ : SimpleGraph (Fin 1)) default
          (zigzagComponentProjection k (⊥ : SimpleGraph (Fin 1)) default x)) := by
  unfold zigzagAlgebra at x
  rfl

/-- The inverse rank-one comparison inserts a dual number into the unique lifted component. -/
@[simp]
theorem zigzagAlgebraEquivA1_symm_apply_component (x : DualNumber k)
    (C : (⊥ : SimpleGraph (Fin 1)).ConnectedComponent) :
    zigzagComponentProjection k (⊥ : SimpleGraph (Fin 1)) C
        ((zigzagAlgebraEquivA1 k).symm x) =
      (zigzagComponentAlgebraEquivULiftDualNumber k
        (⊥ : SimpleGraph (Fin 1)) C).symm (ULift.up x) := by
  have hC : C = default := Subsingleton.elim _ _
  subst C
  apply (zigzagComponentAlgebraEquivULiftDualNumber k
    (⊥ : SimpleGraph (Fin 1)) default).injective
  rw [AlgEquiv.apply_symm_apply]
  apply (ULift.algEquiv (R := k) (A := DualNumber k)).injective
  rw [ULift.algEquiv_apply, ULift.down_up, ← zigzagAlgebraEquivA1_apply]
  exact (zigzagAlgebraEquivA1 k).apply_symm_apply x

end TauCeti
