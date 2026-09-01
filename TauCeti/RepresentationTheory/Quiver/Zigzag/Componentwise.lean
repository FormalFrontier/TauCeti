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
algebra on a connected graph with an edge, but gives only the coefficient ring on an isolated
vertex.  The Huerfano--Khovanov convention instead assigns the dual numbers to a one-vertex
component.  This file makes that distinction in the public definition: `TauCeti.zigzagAlgebra`
is the product of the appropriate algebra over the connected components of the graph.

The component algebra is packaged in `AlgCat` because its carrier changes between the singleton
and non-singleton cases.  The public algebra is the product of those carriers, exposed through
component projections and extensionality.  For a connected nontrivial graph, the product has one
factor and is canonically isomorphic to the landed relation quotient.  For the one-vertex graph it
is canonically the dual numbers from Mathlib.  The relabelling isomorphism
`TauCeti.zigzagAlgebraEquiv` is coherent: it takes identity relabellings to identities, composites
to composites and inverses to inverses.

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

variable (k : Type w) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

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

/-- Construct an element of the public zigzag algebra from one element in each connected-component
factor. -/
noncomputable def zigzagAlgebraMk
    (x : ∀ C : G.ConnectedComponent, zigzagComponentAlgebra k G C) : zigzagAlgebra k G := by
  unfold zigzagAlgebra
  exact x

/-- Projection from the public zigzag algebra to the factor indexed by a connected component. -/
noncomputable def zigzagComponentProjection (C : G.ConnectedComponent) :
    zigzagAlgebra k G →ₐ[k] zigzagComponentAlgebra k G C := by
  unfold zigzagAlgebra
  exact Pi.evalAlgHom k (fun C : G.ConnectedComponent ↦ zigzagComponentAlgebra k G C) C

/-- Projecting a componentwise-constructed element recovers the specified component. -/
@[simp]
theorem zigzagComponentProjection_zigzagAlgebraMk
    (x : ∀ C : G.ConnectedComponent, zigzagComponentAlgebra k G C)
    (C : G.ConnectedComponent) :
    zigzagComponentProjection k G C (zigzagAlgebraMk k G x) = x C := by
  rfl

/-- Elements of the public zigzag algebra are equal when all their component projections agree. -/
@[ext]
theorem zigzagAlgebra.ext {x y : zigzagAlgebra k G}
    (h : ∀ C, zigzagComponentProjection k G C x = zigzagComponentProjection k G C y) : x = y := by
  unfold zigzagAlgebra at x y
  exact funext h

/-- Reconstructing a public zigzag-algebra element from its component projections returns the
original element. -/
@[simp]
theorem zigzagAlgebra.mk_projections (x : zigzagAlgebra k G) :
    zigzagAlgebraMk k G (fun C ↦ zigzagComponentProjection k G C x) = x := by
  apply zigzagAlgebra.ext
  intro C
  rw [zigzagComponentProjection_zigzagAlgebraMk]

/-- Evaluation identifies a dependent product of algebras over a one-point index type with its
unique factor. -/
private noncomputable def algEquivPiUnique {ι : Type*} [Unique ι] (A : ι → AlgCat k) :
    (∀ i, A i) ≃ₐ[k] A default :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.piUnique fun i ↦ A i) (by intro; rfl)

/-- The product evaluation equivalence evaluates at the unique index. -/
private theorem algEquivPiUnique_apply {ι : Type*} [Unique ι] (A : ι → AlgCat k)
    (x : ∀ i, A i) : algEquivPiUnique k A x = x default := by
  rfl

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
theorem nontrivial_connectedComponent (hconn : G.Connected) [Nontrivial V]
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

/-- On a nontrivial component, the invariance equivalence is the landed quotient isomorphism
conjugated by the two component presentations. -/
private theorem zigzagComponentAlgebraEquiv_of_nontrivial {W : Type v} [Finite W]
    {H : SimpleGraph W} (e : G ≃g H) (C : G.ConnectedComponent) [hC : Nontrivial C]
    [Nontrivial (e.connectedComponentEquiv C)] :
    zigzagComponentAlgebraEquiv k G e C =
      (zigzagComponentAlgebraEquivNonisolated k G C).trans
        ((nonisolatedZigzagQuotientEquiv k (connectedComponentGraphIsoOfIso G e C)).trans
          (zigzagComponentAlgebraEquivNonisolated k H (e.connectedComponentEquiv C)).symm) := by
  unfold zigzagComponentAlgebraEquiv
  rw [dite_eq_left hC]

/-- On a singleton component, the invariance equivalence is the identity of the dual numbers
conjugated by the two component presentations and the two universe lifts. -/
private theorem zigzagComponentAlgebraEquiv_of_subsingleton {W : Type v} [Finite W]
    {H : SimpleGraph W} (e : G ≃g H) (C : G.ConnectedComponent) [hC : Subsingleton C]
    [Subsingleton (e.connectedComponentEquiv C)] :
    zigzagComponentAlgebraEquiv k G e C =
      (zigzagComponentAlgebraEquivULiftDualNumber k G C).trans
        ((ULift.algEquiv (R := k) (A := DualNumber k)).trans
          ((ULift.algEquiv (R := k) (A := DualNumber k)).symm.trans
            (zigzagComponentAlgebraEquivULiftDualNumber k H
              (e.connectedComponentEquiv C)).symm)) := by
  unfold zigzagComponentAlgebraEquiv
  rw [dite_eq_right (not_nontrivial_iff_subsingleton.mpr hC)]

/-- The identity relabelling acts as the identity on each component algebra.  Stated at a vertex
representative, where the index `(Iso.refl).connectedComponentEquiv (G.connectedComponentMk v)`
is definitionally `G.connectedComponentMk v`. -/
private theorem zigzagComponentAlgebraEquiv_refl_apply (v : V)
    (y : zigzagComponentAlgebra k G (G.connectedComponentMk v)) :
    zigzagComponentAlgebraEquiv k G (SimpleGraph.Iso.refl (G := G))
      (G.connectedComponentMk v) y = y := by
  classical
  by_cases hC : Nontrivial (G.connectedComponentMk v : G.ConnectedComponent)
  · let _ : Nontrivial (G.connectedComponentMk v : G.ConnectedComponent) := hC
    let _ : Nontrivial ((SimpleGraph.Iso.refl (G := G)).connectedComponentEquiv
      (G.connectedComponentMk v)) := hC
    rw [zigzagComponentAlgebraEquiv_of_nontrivial]
    have h : (zigzagComponentAlgebraEquivNonisolated k G (G.connectedComponentMk v)).symm
        (nonisolatedZigzagQuotientEquiv k (SimpleGraph.Iso.refl
            (G := (G.connectedComponentMk v : G.ConnectedComponent).toSimpleGraph))
          (zigzagComponentAlgebraEquivNonisolated k G (G.connectedComponentMk v) y)) = y := by
      rw [nonisolatedZigzagQuotientEquiv_refl]
      exact AlgEquiv.symm_apply_apply _ _
    exact h
  · let _ : Subsingleton (G.connectedComponentMk v : G.ConnectedComponent) :=
      not_nontrivial_iff_subsingleton.mp hC
    let _ : Subsingleton ((SimpleGraph.Iso.refl (G := G)).connectedComponentEquiv
      (G.connectedComponentMk v)) := not_nontrivial_iff_subsingleton.mp hC
    rw [zigzagComponentAlgebraEquiv_of_subsingleton]
    have h : (zigzagComponentAlgebraEquivULiftDualNumber k G (G.connectedComponentMk v)).symm
        ((ULift.algEquiv (R := k) (A := DualNumber k)).symm
          ((ULift.algEquiv (R := k) (A := DualNumber k))
            (zigzagComponentAlgebraEquivULiftDualNumber k G
              (G.connectedComponentMk v) y))) = y := by
      rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
    exact h

/-- Composing conjugated equivalences composes the conjugating equivalence: if `pA`, `pB` and `pD`
present three algebras through models, and the model equivalences compose as `eMN.trans eNP =
eMP`, then conjugating `eNP` after conjugating `eMN` conjugates `eMP`.  Both branches of
`zigzagComponentAlgebraEquiv` are conjugations of this shape, so this lemma carries the
composition argument for each of them. -/
private theorem conj_trans_apply {A B D M N P : Type*} [Semiring A] [Semiring B] [Semiring D]
    [Semiring M] [Semiring N] [Semiring P] [Algebra k A] [Algebra k B] [Algebra k D]
    [Algebra k M] [Algebra k N] [Algebra k P] (pA : A ≃ₐ[k] M) (pB : B ≃ₐ[k] N) (pD : D ≃ₐ[k] P)
    (eMN : M ≃ₐ[k] N) (eNP : N ≃ₐ[k] P) (eMP : M ≃ₐ[k] P) (hcomp : eMN.trans eNP = eMP) (x : A) :
    pB.trans (eNP.trans pD.symm) (pA.trans (eMN.trans pB.symm) x) =
      pA.trans (eMP.trans pD.symm) x := by
  subst hcomp
  simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]

/-- Composing two relabellings composes the component-algebra equivalences.  Stated at a vertex
representative, where the two indices `f.connectedComponentEquiv (e.connectedComponentEquiv C)`
and `(e.trans f).connectedComponentEquiv C` are definitionally equal. -/
private theorem zigzagComponentAlgebraEquiv_trans_apply {W : Type v} [Finite W]
    {H : SimpleGraph W} {X : Type*} [Finite X] {K : SimpleGraph X} (e : G ≃g H) (f : H ≃g K)
    (v : V) (y : zigzagComponentAlgebra k G (G.connectedComponentMk v)) :
    zigzagComponentAlgebraEquiv k H f (e.connectedComponentEquiv (G.connectedComponentMk v))
        (zigzagComponentAlgebraEquiv k G e (G.connectedComponentMk v) y) =
      zigzagComponentAlgebraEquiv k G (e.trans f) (G.connectedComponentMk v) y := by
  classical
  by_cases hC : Nontrivial (G.connectedComponentMk v : G.ConnectedComponent)
  · let _ : Nontrivial (G.connectedComponentMk v : G.ConnectedComponent) := hC
    let _ : Nontrivial (e.connectedComponentEquiv (G.connectedComponentMk v)) :=
      (Equiv.nontrivial_congr ((G.connectedComponentMk v).isoEquivSupp e)).mp hC
    let _ : Nontrivial (f.connectedComponentEquiv
        (e.connectedComponentEquiv (G.connectedComponentMk v))) :=
      (Equiv.nontrivial_congr ((e.connectedComponentEquiv
        (G.connectedComponentMk v)).isoEquivSupp f)).mp inferInstance
    let _ : Nontrivial (SimpleGraph.Iso.connectedComponentEquiv (e.trans f)
        (G.connectedComponentMk v)) :=
      (Equiv.nontrivial_congr ((G.connectedComponentMk v).isoEquivSupp (e.trans f))).mp hC
    rw [zigzagComponentAlgebraEquiv_of_nontrivial k G e,
      zigzagComponentAlgebraEquiv_of_nontrivial k H f,
      zigzagComponentAlgebraEquiv_of_nontrivial k G (e.trans f)]
    exact conj_trans_apply k _ _ _
      (nonisolatedZigzagQuotientEquiv k
        (connectedComponentGraphIsoOfIso G e (G.connectedComponentMk v)))
      (nonisolatedZigzagQuotientEquiv k (connectedComponentGraphIsoOfIso H f
        (e.connectedComponentEquiv (G.connectedComponentMk v)))) _
      (nonisolatedZigzagQuotientEquiv_trans k _ _).symm y
  · let _ : Subsingleton (G.connectedComponentMk v : G.ConnectedComponent) :=
      not_nontrivial_iff_subsingleton.mp hC
    let _ : Subsingleton (e.connectedComponentEquiv (G.connectedComponentMk v)) :=
      (Equiv.subsingleton_congr ((G.connectedComponentMk v).isoEquivSupp e)).mp inferInstance
    let _ : Subsingleton (f.connectedComponentEquiv
        (e.connectedComponentEquiv (G.connectedComponentMk v))) :=
      (Equiv.subsingleton_congr ((e.connectedComponentEquiv
        (G.connectedComponentMk v)).isoEquivSupp f)).mp inferInstance
    let _ : Subsingleton (SimpleGraph.Iso.connectedComponentEquiv (e.trans f)
        (G.connectedComponentMk v)) :=
      (Equiv.subsingleton_congr ((G.connectedComponentMk v).isoEquivSupp (e.trans f))).mp
        inferInstance
    rw [zigzagComponentAlgebraEquiv_of_subsingleton k G e,
      zigzagComponentAlgebraEquiv_of_subsingleton k H f,
      zigzagComponentAlgebraEquiv_of_subsingleton k G (e.trans f)]
    exact conj_trans_apply k
      (zigzagComponentAlgebraEquivULiftDualNumber k G (G.connectedComponentMk v))
      (zigzagComponentAlgebraEquivULiftDualNumber k H
        (e.connectedComponentEquiv (G.connectedComponentMk v)))
      (zigzagComponentAlgebraEquivULiftDualNumber k K (f.connectedComponentEquiv
        (e.connectedComponentEquiv (G.connectedComponentMk v))))
      ((ULift.algEquiv (R := k) (A := DualNumber k)).trans
        (ULift.algEquiv (R := k) (A := DualNumber k)).symm)
      ((ULift.algEquiv (R := k) (A := DualNumber k)).trans
        (ULift.algEquiv (R := k) (A := DualNumber k)).symm)
      ((ULift.algEquiv (R := k) (A := DualNumber k)).trans
        (ULift.algEquiv (R := k) (A := DualNumber k)).symm)
      (AlgEquiv.ext fun z ↦ by
        simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]) y

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

/-- **The identity relabelling induces the identity of the public zigzag algebra.** -/
@[simp]
theorem zigzagAlgebraEquiv_refl :
    zigzagAlgebraEquiv k G (SimpleGraph.Iso.refl (G := G)) = AlgEquiv.refl := by
  refine AlgEquiv.ext fun x ↦ zigzagAlgebra.ext k G fun D ↦ ?_
  induction D using SimpleGraph.ConnectedComponent.ind with
  | _ v =>
    exact (zigzagAlgebraEquiv_apply_component k G (SimpleGraph.Iso.refl (G := G)) x
      (G.connectedComponentMk v)).trans (zigzagComponentAlgebraEquiv_refl_apply k G v _)

/-- **The public zigzag algebra is functorial in the graph**: composing two relabellings composes
the induced isomorphisms of public zigzag algebras. -/
theorem zigzagAlgebraEquiv_trans {W : Type v} [Finite W] {H : SimpleGraph W} {X : Type*}
    [Finite X] {K : SimpleGraph X} (e : G ≃g H) (f : H ≃g K) :
    zigzagAlgebraEquiv k G (e.trans f) =
      (zigzagAlgebraEquiv k G e).trans (zigzagAlgebraEquiv k H f) := by
  refine AlgEquiv.ext fun x ↦ zigzagAlgebra.ext k K fun D ↦ ?_
  obtain ⟨C, rfl⟩ := (SimpleGraph.Iso.connectedComponentEquiv (e.trans f)).surjective D
  induction C using SimpleGraph.ConnectedComponent.ind with
  | _ v =>
    refine ((zigzagAlgebraEquiv_apply_component k G (e.trans f) x
      (G.connectedComponentMk v)).trans ?_).trans
        (zigzagAlgebraEquiv_apply_component k H f (zigzagAlgebraEquiv k G e x)
          (e.connectedComponentEquiv (G.connectedComponentMk v))).symm
    rw [zigzagAlgebraEquiv_apply_component k G e x (G.connectedComponentMk v)]
    exact (zigzagComponentAlgebraEquiv_trans_apply k G e f v _).symm

/-- **The inverse relabelling induces the inverse isomorphism of public zigzag algebras.** -/
@[simp]
theorem zigzagAlgebraEquiv_symm {W : Type v} [Finite W] {H : SimpleGraph W} (e : G ≃g H) :
    (zigzagAlgebraEquiv k G e).symm = zigzagAlgebraEquiv k H e.symm := by
  have h : (zigzagAlgebraEquiv k G e).trans (zigzagAlgebraEquiv k H e.symm) = AlgEquiv.refl := by
    rw [← zigzagAlgebraEquiv_trans, RelIso.self_trans_symm]
    exact zigzagAlgebraEquiv_refl k G
  refine AlgEquiv.ext fun x ↦ ?_
  have hx := DFunLike.congr_fun h ((zigzagAlgebraEquiv k G e).symm x)
  rw [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply] at hx
  exact hx.symm

/-- On a connected graph with at least two vertices, the public componentwise zigzag algebra is
canonically isomorphic to the uniform relation quotient. -/
noncomputable def zigzagAlgebraEquivNonisolated (hconn : G.Connected) [Nontrivial V] :
    zigzagAlgebra k G ≃ₐ[k] nonisolatedZigzagQuotient k G :=
  letI := connectedComponentUnique G hconn
  letI : Nontrivial (default : G.ConnectedComponent) :=
    nontrivial_connectedComponent G hconn default
  (algEquivPiUnique k fun C : G.ConnectedComponent ↦ zigzagComponentAlgebra k G C).trans <|
    (zigzagComponentAlgebraEquivNonisolated k G default).trans <|
      nonisolatedZigzagQuotientEquiv k (connectedComponentGraphIso G hconn default)

/-- The connected nonisolated comparison evaluates through any connected-component factor and
the canonical graph isomorphism from that factor to the original graph. -/
theorem zigzagAlgebraEquivNonisolated_apply (hconn : G.Connected) [Nontrivial V]
    (x : zigzagAlgebra k G) (C : G.ConnectedComponent) :
    zigzagAlgebraEquivNonisolated k G hconn x =
      let _ := nontrivial_connectedComponent G hconn C
      nonisolatedZigzagQuotientEquiv k (connectedComponentGraphIso G hconn C)
        (zigzagComponentAlgebraEquivNonisolated k G C
          (zigzagComponentProjection k G C x)) := by
  let _ := connectedComponentUnique G hconn
  let _ : Nontrivial (default : G.ConnectedComponent) :=
    nontrivial_connectedComponent G hconn default
  have hC : C = default := Subsingleton.elim _ _
  subst C
  unfold zigzagAlgebra at x
  -- `zigzagAlgebra k G` is the bundled `AlgCat` object on the dependent product, so the semiring
  -- and algebra instances it carries are the `AlgCat` ones rather than the `Pi` ones that
  -- `algEquivPiUnique` is stated with.  The two are definitionally equal but not syntactically,
  -- so `rw [zigzagAlgebraEquivNonisolated]` produces a goal that is rejected at `implicit`
  -- transparency; this `change` is the single place where the two presentations of the same
  -- product are identified, after which the computation is ordinary rewriting.
  change
    ((algEquivPiUnique k (fun C : G.ConnectedComponent ↦
      zigzagComponentAlgebra k G C)).trans
        ((zigzagComponentAlgebraEquivNonisolated k G default).trans
          (nonisolatedZigzagQuotientEquiv k
            (connectedComponentGraphIso G hconn default)))) x =
      nonisolatedZigzagQuotientEquiv k (connectedComponentGraphIso G hconn default)
        (zigzagComponentAlgebraEquivNonisolated k G default (x default))
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, algEquivPiUnique_apply]

/-- The inverse connected nonisolated comparison is computed componentwise by the inverse graph
and component equivalences. -/
@[simp]
theorem zigzagAlgebraEquivNonisolated_symm_apply_component (hconn : G.Connected)
    [Nontrivial V] (x : nonisolatedZigzagQuotient k G) (C : G.ConnectedComponent) :
    zigzagComponentProjection k G C ((zigzagAlgebraEquivNonisolated k G hconn).symm x) =
      let _ := nontrivial_connectedComponent G hconn C
      (zigzagComponentAlgebraEquivNonisolated k G C).symm
        ((nonisolatedZigzagQuotientEquiv k
          (connectedComponentGraphIso G hconn C)).symm x) := by
  let _ := nontrivial_connectedComponent G hconn C
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
  -- As in `TauCeti.zigzagAlgebraEquivNonisolated_apply`, this `change` only replaces the `AlgCat`
  -- instances carried by `zigzagAlgebra k (⊥ : SimpleGraph (Fin 1))` by the definitionally equal
  -- `Pi` instances that `algEquivPiUnique` is stated with; rewriting cannot cross that gap.
  change
    ((algEquivPiUnique k (fun C : (⊥ : SimpleGraph (Fin 1)).ConnectedComponent ↦
      zigzagComponentAlgebra k (⊥ : SimpleGraph (Fin 1)) C)).trans
        ((zigzagComponentAlgebraEquivULiftDualNumber k
          (⊥ : SimpleGraph (Fin 1)) default).trans
            (ULift.algEquiv (R := k) (A := DualNumber k)))) x =
      ULift.down (zigzagComponentAlgebraEquivULiftDualNumber k
        (⊥ : SimpleGraph (Fin 1)) default (x default))
  calc
    _ = ((zigzagComponentAlgebraEquivULiftDualNumber k
        (⊥ : SimpleGraph (Fin 1)) default).trans
          (ULift.algEquiv (R := k) (A := DualNumber k))) (x default) :=
      (AlgEquiv.trans_apply _ _ x).trans (congrArg _ (algEquivPiUnique_apply k _ x))
    _ = _ := by rw [AlgEquiv.trans_apply, ULift.algEquiv_apply]

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
