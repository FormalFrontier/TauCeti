/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Map
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Relations

/-!
# The nonisolated zigzag quotient is an invariant of the graph

An isomorphism `e : G ≃g H` of simple graphs relabels the doubled quiver of `G` as the doubled
quiver of `H`, hence relabels the path basis of `k(DoubledQuiver G)` as the path basis of
`k(DoubledQuiver H)`. This file carries that relabelling through the zigzag relations: it is an
isomorphism of path algebras, it matches the two relation families, and it therefore descends to an
isomorphism of the two `TauCeti.nonisolatedZigzagQuotient`s.

That quotient is, as its own docstring records, the intended zigzag algebra only for a graph
without an isolated vertex; the componentwise public algebra remains to be built, and its
invariance is not established here.

Nothing here is specific to the *uniform* relation family beyond the fact that it is described by
path lengths and by the endpoints of paths, both of which a relabelling preserves. That is exactly
what the transport lemmas below say, one constructor at a time.

## Main definitions

* `TauCeti.DoubledQuiver.pathAlgebraEquiv`: the isomorphism of doubled path algebras induced by a
  graph isomorphism.
* `TauCeti.nonisolatedZigzagQuotientEquiv`: the induced isomorphism of nonisolated zigzag
  quotients.

## Main results

* `TauCeti.DoubledQuiver.pathAlgebraEquiv_vertexIdempotent`,
  `TauCeti.DoubledQuiver.pathAlgebraEquiv_ofArrow` and
  `TauCeti.DoubledQuiver.pathAlgebraEquiv_backtrackElem`: the relabelling on the three families of
  elements the zigzag relations are written in.
* `TauCeti.isQuadraticZigzagRelator_pathAlgebraEquiv` and
  `TauCeti.isZigzagRelator_pathAlgebraEquiv`: **the relators are matched**.
* `TauCeti.nonisolatedZigzagQuotientEquiv_zigzagMk`: the induced isomorphism of quotients sends the
  class of an element to the class of its relabelling.
* `TauCeti.nonisolatedZigzagQuotientEquiv_refl` and
  `TauCeti.nonisolatedZigzagQuotientEquiv_trans`: **functoriality**, the identity relabelling and a
  composite of relabellings behaving as they should.

## References

This discharges the "functoriality under graph/quiver isomorphism" clause of Layer 0 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`. It covers the "invariance under graph isomorphism"
clause of Layer 1 only in part: the uniform relation quotient is transported, while the
skew-parameter statements of that clause — extension along a field homomorphism, the resulting
scalar-extension comparison, and injectivity on units — are untouched. See Huerfano--Khovanov,
*A category for the adjoint representation*, Section 3.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u v w

namespace DoubledQuiver

variable {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}

variable (k : Type w) [CommSemiring k] [Finite V] [Finite W]

/-- **The isomorphism of doubled path algebras induced by a graph isomorphism**: it relabels the
basis path by path of the doubled quiver. -/
noncomputable def pathAlgebraEquiv (e : G ≃g H) :
    pathAlgebra k (DoubledQuiver G) ≃ₐ[k] pathAlgebra k (DoubledQuiver H) :=
  PathAlgebra.mapAlgEquiv k (map e.toHom) (map e.symm.toHom) (map_toHom_comp_symm_toHom e)
    (map_symm_toHom_comp_toHom e)

/-- The relabelling sends the basis element of a path of the doubled quiver of `G` to the basis
element of the relabelled path of the doubled quiver of `H`. -/
@[simp]
theorem pathAlgebraEquiv_ofPath (e : G ≃g H) (x : Quiver.TotalPath (DoubledQuiver G)) :
    pathAlgebraEquiv k e (ofPath x) = ofPath ((map e.toHom).mapTotalPath x) := by
  rw [pathAlgebraEquiv, PathAlgebra.mapAlgEquiv_apply, mapAlgHom_ofPath]

/-- The relabelling carries the idempotent of a vertex of `G` to the idempotent of the image
vertex of `H`. -/
@[simp]
theorem pathAlgebraEquiv_vertexIdempotent (e : G ≃g H) (i : V) :
    pathAlgebraEquiv k e (vertexIdempotent k (vertex G i)) =
      vertexIdempotent k (vertex H (e i)) := by
  rw [pathAlgebraEquiv, PathAlgebra.mapAlgEquiv_apply, mapAlgHom_vertexIdempotent, map_obj]
  simp only [SimpleGraph.Embedding.coe_toHom, RelIso.coe_toRelEmbedding]

/-- The relabelling carries an arrow along an edge of `G` to the arrow along the image edge of `H`.
Deliberately not a `simp` lemma, `TauCeti.PathAlgebra.ofArrow_eq_ofPath` already rewriting its
left-hand side. -/
theorem pathAlgebraEquiv_ofArrow (e : G ≃g H) {i j : V} (h : G.Adj i j) :
    pathAlgebraEquiv k e (ofArrow (arrow G h)) = ofArrow (arrow H (e.map_adj_iff.mpr h)) := by
  rw [pathAlgebraEquiv, PathAlgebra.mapAlgEquiv_apply, mapAlgHom_ofArrow, map_arrow,
    PathAlgebra.ofArrow_homOfEq]

/-- The relabelling carries the backtrack element along an edge of `G` to the backtrack element
along the image edge of `H`: it traverses the image edge and returns along it. -/
@[simp]
theorem pathAlgebraEquiv_backtrackElem (e : G ≃g H) {i j : V} (h : G.Adj i j) :
    pathAlgebraEquiv k e (backtrackElem G k h) = backtrackElem H k (e.map_adj_iff.mpr h) := by
  rw [← ofArrow_symm_mul_ofArrow, map_mul, pathAlgebraEquiv_ofArrow, pathAlgebraEquiv_ofArrow,
    ofArrow_symm_mul_ofArrow]

/-- **The relabelling is functorial**: composing two graph isomorphisms composes the induced
isomorphisms of path algebras. -/
theorem pathAlgebraEquiv_trans {X : Type*} [Finite X] {K : SimpleGraph X} (e : G ≃g H)
    (f : H ≃g K) :
    pathAlgebraEquiv k (e.trans f) = (pathAlgebraEquiv k e).trans (pathAlgebraEquiv k f) := by
  have hsymm : map (SimpleGraph.Iso.symm (e.trans f)).toHom =
      map f.symm.toHom ⋙q map e.symm.toHom := map_trans f.symm e.symm
  rw [pathAlgebraEquiv, pathAlgebraEquiv, pathAlgebraEquiv,
    PathAlgebra.mapAlgEquiv_congr k (map_trans e f) hsymm _ _
      (by rw [← map_trans e f, ← hsymm]; exact map_toHom_comp_symm_toHom _)
      (by rw [← map_trans e f, ← hsymm]; exact map_symm_toHom_comp_toHom _),
    PathAlgebra.mapAlgEquiv_comp k _ _ _ _ (map_toHom_comp_symm_toHom e)
      (map_symm_toHom_comp_toHom e) (map_toHom_comp_symm_toHom f)
      (map_symm_toHom_comp_toHom f)]

/-- **The identity relabelling induces the identity.** -/
@[simp]
theorem pathAlgebraEquiv_refl :
    pathAlgebraEquiv k (SimpleGraph.Iso.refl (G := G)) = AlgEquiv.refl := by
  have hsymm : map (SimpleGraph.Iso.refl (G := G)).symm.toHom = Prefunctor.id (DoubledQuiver G) :=
    map_refl
  have hid := Prefunctor.comp_id (Prefunctor.id (DoubledQuiver G))
  rw [pathAlgebraEquiv, PathAlgebra.mapAlgEquiv_congr k map_refl hsymm _ _ hid hid,
    PathAlgebra.mapAlgEquiv_id]

/-- The inverse of the induced isomorphism is the isomorphism induced by the inverse
relabelling. -/
@[simp]
theorem pathAlgebraEquiv_symm (e : G ≃g H) :
    (pathAlgebraEquiv k e).symm = pathAlgebraEquiv k e.symm := by
  have hsymm : map e.symm.symm.toHom = map e.toHom := rfl
  rw [pathAlgebraEquiv, PathAlgebra.mapAlgEquiv_symm, pathAlgebraEquiv,
    PathAlgebra.mapAlgEquiv_congr k rfl hsymm _ _ (map_toHom_comp_symm_toHom e.symm)
      (map_symm_toHom_comp_toHom e.symm)]

end DoubledQuiver

variable (k : Type w) [CommRing k] {V : Type u} {W : Type v} [Finite V] [Finite W]
  {G : SimpleGraph V} {H : SimpleGraph W}

/-! ### The relators are matched -/

/-- **A graph isomorphism carries the quadratic zigzag relators of `G` to those of `H`**: it
preserves the length of a path and, being injective on vertices, whether its endpoints agree. -/
theorem isQuadraticZigzagRelator_pathAlgebraEquiv (e : G ≃g H)
    {x : pathAlgebra k (DoubledQuiver G)} (hx : IsQuadraticZigzagRelator k G x) :
    IsQuadraticZigzagRelator k H (pathAlgebraEquiv k e x) := by
  cases hx with
  | nonreturn p hlen hne =>
    rw [pathAlgebraEquiv_ofPath, Prefunctor.mapTotalPath_mk]
    exact IsQuadraticZigzagRelator.nonreturn _
      (((map e.toHom).length_mapPath p).trans hlen)
      fun h ↦ hne ((map_obj_bijective e).1 h)
  | equal_backtracks p q hp hq =>
    rw [map_sub, pathAlgebraEquiv_ofPath, pathAlgebraEquiv_ofPath,
      Prefunctor.mapTotalPath_mk, Prefunctor.mapTotalPath_mk]
    exact IsQuadraticZigzagRelator.equal_backtracks _ _
      (((map e.toHom).length_mapPath p).trans hp) (((map e.toHom).length_mapPath q).trans hq)

/-- **A graph isomorphism carries the uniform zigzag relators of `G` to those of `H`.** -/
theorem isZigzagRelator_pathAlgebraEquiv (e : G ≃g H) {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsZigzagRelator k G x) : IsZigzagRelator k H (pathAlgebraEquiv k e x) := by
  cases hx with
  | quadratic hq => exact .quadratic (isQuadraticZigzagRelator_pathAlgebraEquiv k e hq)
  | long_path x h3 =>
    rw [pathAlgebraEquiv_ofPath]
    exact IsZigzagRelator.long_path _ ((map e.toHom).length_mapTotalPath x ▸ h3)

/-! ### The quotients are isomorphic -/

/-- The map of nonisolated zigzag quotients induced by a graph isomorphism. This is only the
forward direction of `TauCeti.nonisolatedZigzagQuotientEquiv`, which is the public API; it is
private so as not to duplicate it. -/
private noncomputable def nonisolatedZigzagQuotientHom (e : G ≃g H) :
    nonisolatedZigzagQuotient k G →ₐ[k] nonisolatedZigzagQuotient k H :=
  zigzagLift k G ((zigzagMk k H).comp (pathAlgebraEquiv k e).toAlgHom) fun x hx ↦ by
    rw [AlgHom.comp_apply]
    exact zigzagMk_eq_zero_of_isZigzagRelator k H (isZigzagRelator_pathAlgebraEquiv k e hx)

/-- The induced map of quotients sends the class of an element to the class of its relabelling. -/
private theorem nonisolatedZigzagQuotientHom_zigzagMk (e : G ≃g H)
    (x : pathAlgebra k (DoubledQuiver G)) :
    nonisolatedZigzagQuotientHom k e (zigzagMk k G x) = zigzagMk k H (pathAlgebraEquiv k e x) :=
  zigzagLift_zigzagMk k G _ _ x

/-- **The nonisolated zigzag quotient is an invariant of the graph**: an isomorphism of simple
graphs induces an isomorphism of the uniform relation quotients of their doubled path algebras.
This is invariance of `TauCeti.nonisolatedZigzagQuotient`, which is the intended zigzag algebra
only for a graph without an isolated vertex; the componentwise public algebra is not treated
here. -/
noncomputable def nonisolatedZigzagQuotientEquiv (e : G ≃g H) :
    nonisolatedZigzagQuotient k G ≃ₐ[k] nonisolatedZigzagQuotient k H :=
  AlgEquiv.ofAlgHom (nonisolatedZigzagQuotientHom k e) (nonisolatedZigzagQuotientHom k e.symm)
    (Ideal.Quotient.algHom_ext k (AlgHom.ext fun y ↦ by
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← zigzagMk_apply,
        nonisolatedZigzagQuotientHom_zigzagMk, ← pathAlgebraEquiv_symm, AlgEquiv.apply_symm_apply,
        AlgHom.id_apply]))
    (Ideal.Quotient.algHom_ext k (AlgHom.ext fun x ↦ by
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← zigzagMk_apply,
        nonisolatedZigzagQuotientHom_zigzagMk, ← pathAlgebraEquiv_symm, AlgEquiv.symm_apply_apply,
        AlgHom.id_apply]))

/-- The induced isomorphism of quotients sends the class of an element to the class of its
relabelling. -/
@[simp]
theorem nonisolatedZigzagQuotientEquiv_zigzagMk (e : G ≃g H)
    (x : pathAlgebra k (DoubledQuiver G)) :
    nonisolatedZigzagQuotientEquiv k e (zigzagMk k G x) =
      zigzagMk k H (pathAlgebraEquiv k e x) := by
  rw [nonisolatedZigzagQuotientEquiv, AlgEquiv.ofAlgHom_apply,
    nonisolatedZigzagQuotientHom_zigzagMk]

/-- The inverse quotient isomorphism is induced by the inverse graph relabelling. -/
@[simp]
theorem nonisolatedZigzagQuotientEquiv_symm (e : G ≃g H) :
    (nonisolatedZigzagQuotientEquiv k e).symm = nonisolatedZigzagQuotientEquiv k e.symm := by
  refine AlgEquiv.ext fun z ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply (nonisolatedZigzagQuotientEquiv k e).injective
  rw [AlgEquiv.apply_symm_apply, ← zigzagMk_apply, nonisolatedZigzagQuotientEquiv_zigzagMk,
    nonisolatedZigzagQuotientEquiv_zigzagMk, ← pathAlgebraEquiv_symm, AlgEquiv.apply_symm_apply]

/-- **The identity relabelling induces the identity of quotients.** -/
@[simp]
theorem nonisolatedZigzagQuotientEquiv_refl :
    nonisolatedZigzagQuotientEquiv k (SimpleGraph.Iso.refl (G := G)) = AlgEquiv.refl := by
  refine AlgEquiv.ext fun z ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [← zigzagMk_apply, nonisolatedZigzagQuotientEquiv_zigzagMk, pathAlgebraEquiv_refl]
  rfl

/-- **The isomorphism of quotients is functorial**: composing two graph isomorphisms composes the
induced isomorphisms of nonisolated zigzag quotients. -/
theorem nonisolatedZigzagQuotientEquiv_trans {X : Type*} [Finite X] {K : SimpleGraph X} (e : G ≃g H)
    (f : H ≃g K) :
    nonisolatedZigzagQuotientEquiv k (e.trans f) =
      (nonisolatedZigzagQuotientEquiv k e).trans (nonisolatedZigzagQuotientEquiv k f) := by
  refine AlgEquiv.ext fun z ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [← zigzagMk_apply, nonisolatedZigzagQuotientEquiv_zigzagMk, pathAlgebraEquiv_trans,
    AlgEquiv.trans_apply, AlgEquiv.trans_apply, nonisolatedZigzagQuotientEquiv_zigzagMk,
    nonisolatedZigzagQuotientEquiv_zigzagMk]

end TauCeti
