/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Quiver.Prefunctor
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# Path algebras are functorial in the quiver

A prefunctor `φ : Q ⥤q R` pushes a path of `Q` to a path of `R`, hence a basis element of `kQ` to a
basis element of `kR`. This file extends that assignment to an algebra homomorphism
`TauCeti.PathAlgebra.mapAlgHom`, and shows that it is an isomorphism when `φ` is one.

A uniform condition sufficient for this construction is that `φ` be bijective on vertices. The
unit of `kQ` is the sum of *all* the vertex idempotents, so surjectivity ensures that their images
sum to the unit of `kR`. Injectivity ensures that two paths which do not meet still do not meet
after mapping, so their product remains zero. Thus `mapAlgHom` assumes vertex bijectivity, which
the intended source of prefunctors — an isomorphism of the underlying graph or quiver — supplies.
Nothing is asked of `φ` on arrows: a prefunctor which is not injective on arrows still gives an
algebra homomorphism, just not an injective one.

## Main definitions

* `Prefunctor.mapTotalPath`: the indexed path obtained by pushing an indexed path along a
  prefunctor.
* `TauCeti.PathAlgebra.mapAlgHom`: the algebra homomorphism `kQ →ₐ[k] kR` induced by a prefunctor
  bijective on vertices.
* `TauCeti.PathAlgebra.mapAlgEquiv`: the algebra isomorphism induced by a pair of mutually inverse
  prefunctors.

## Main results

* `TauCeti.PathAlgebra.mapAlgHom_ofPath`, `TauCeti.PathAlgebra.mapAlgHom_vertexIdempotent` and
  `TauCeti.PathAlgebra.mapAlgHom_ofArrow`: the homomorphism on paths, vertex idempotents and
  arrows.
* `TauCeti.PathAlgebra.mapAlgHom_id` and `TauCeti.PathAlgebra.mapAlgHom_comp`: **functoriality**.
* `TauCeti.PathAlgebra.mapAlgEquiv_id`, `TauCeti.PathAlgebra.mapAlgEquiv_comp` and
  `TauCeti.PathAlgebra.mapAlgEquiv_symm`: the same laws for the induced isomorphism, together
  with the congruence lemma `TauCeti.PathAlgebra.mapAlgEquiv_congr`.

## References

This is the "functoriality under graph/quiver isomorphism" clause of Layer 0 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`, at the level of the ambient path algebra; the
relation quotients are carried along it in
`TauCeti/RepresentationTheory/Quiver/Zigzag/Isomorphism.lean`.
-/

public section

namespace TauCeti

universe u u' u'' v v' v'' w

end TauCeti

namespace Prefunctor

variable {Q : Type u} {R : Type u'} {S : Type u''} [Quiver.{v} Q] [Quiver.{v'} R] [Quiver.{v''} S]

/-- The indexed path of `R` obtained by pushing an indexed path of `Q` along a prefunctor. This is
the map on the path bases which `TauCeti.PathAlgebra.mapAlgHom` extends. -/
def mapTotalPath (φ : Q ⥤q R) (x : TauCeti.Quiver.TotalPath Q) :
    TauCeti.Quiver.TotalPath R :=
  ⟨φ.obj x.1, φ.obj x.2.1, φ.mapPath x.2.2⟩

/-- Pushing an indexed path along a prefunctor pushes its two endpoints and its path. -/
@[simp]
theorem mapTotalPath_mk (φ : Q ⥤q R) {a b : Q} (p : Quiver.Path a b) :
    φ.mapTotalPath ⟨a, b, p⟩ = ⟨φ.obj a, φ.obj b, φ.mapPath p⟩ := (rfl)

/-- The source of a pushed indexed path is the image of the source. -/
@[simp]
theorem mapTotalPath_fst (φ : Q ⥤q R) (x : TauCeti.Quiver.TotalPath Q) :
    (φ.mapTotalPath x).1 = φ.obj x.1 := (rfl)

/-- The target of a pushed indexed path is the image of the target. -/
@[simp]
theorem mapTotalPath_snd_fst (φ : Q ⥤q R) (x : TauCeti.Quiver.TotalPath Q) :
    (φ.mapTotalPath x).2.1 = φ.obj x.2.1 := (rfl)

/-- Pushing an indexed path along a prefunctor preserves its length. -/
@[simp]
theorem length_mapTotalPath (φ : Q ⥤q R) (x : TauCeti.Quiver.TotalPath Q) :
    (φ.mapTotalPath x).2.2.length = x.2.2.length :=
  φ.length_mapPath x.2.2

/-- The identity prefunctor leaves an indexed path unchanged. -/
@[simp]
theorem mapTotalPath_id (x : TauCeti.Quiver.TotalPath Q) :
    (Prefunctor.id Q).mapTotalPath x = x := by
  obtain ⟨a, b, p⟩ := x
  rw [mapTotalPath_mk, Prefunctor.mapPath_id]
  rfl

/-- Pushing along a composite of prefunctors is pushing along each in turn. The name follows
`Prefunctor.mapPath_comp_apply`, `Prefunctor.mapPath_comp` being reserved for concatenation. -/
@[simp]
theorem mapTotalPath_comp_apply (φ : Q ⥤q R) (ψ : R ⥤q S) (x : TauCeti.Quiver.TotalPath Q) :
    (φ.comp ψ).mapTotalPath x = ψ.mapTotalPath (φ.mapTotalPath x) := by
  obtain ⟨a, b, p⟩ := x
  rw [mapTotalPath_mk, mapTotalPath_mk, mapTotalPath_mk, Prefunctor.mapPath_comp_apply]
  rfl

end Prefunctor

namespace TauCeti

namespace PathAlgebra

section Map

open Prefunctor

variable {Q : Type u} {R : Type u'} {S : Type u''} [Quiver.{v} Q] [Quiver.{v'} R] [Quiver.{v''} S]

variable (k : Type w) [CommSemiring k] [Finite Q] [Finite R] [Finite S]

omit [Finite Q] [Finite R] in
/-- Pushing paths along a prefunctor turns concatenation into concatenation. This is the `hcomp`
hypothesis of `TauCeti.PathAlgebra.liftAlgHom` for `TauCeti.PathAlgebra.mapAlgHom`. -/
private theorem mapAlgHom_hcomp (φ : Q ⥤q R) {a b c : Q} (p : Quiver.Path a b)
    (q : Quiver.Path c a) :
    (ofPath (mapTotalPath φ ⟨a, b, p⟩) : pathAlgebra k R) * ofPath (mapTotalPath φ ⟨c, a, q⟩) =
      ofPath (mapTotalPath φ ⟨c, b, q.comp p⟩) := by
  rw [mapTotalPath_mk, mapTotalPath_mk, ofPath_mul_ofPath_of_comp, mapTotalPath_mk,
    Prefunctor.mapPath_comp]

omit [Finite Q] in
/-- Paths that do not meet stay apart after being pushed along a prefunctor injective on vertices.
This is the `hzero` hypothesis of `TauCeti.PathAlgebra.liftAlgHom` for
`TauCeti.PathAlgebra.mapAlgHom`. -/
private theorem mapAlgHom_hzero (φ : Q ⥤q R) (hφ : Function.Injective φ.obj)
    {x y : Quiver.TotalPath Q} (h : y.2.1 ≠ x.1) :
    (ofPath (mapTotalPath φ x) : pathAlgebra k R) * ofPath (mapTotalPath φ y) = 0 :=
  ofPath_mul_ofPath_of_not_composable fun hc ↦ h (hφ (by
    simpa only [Prefunctor.mapTotalPath_snd_fst, Prefunctor.mapTotalPath_fst] using hc))

/-- The images of the trivial paths under a prefunctor bijective on vertices enumerate the vertex
idempotents of the target without repetition, so their sum is its unit. This is the `hone`
hypothesis of
`TauCeti.PathAlgebra.liftAlgHom` for `TauCeti.PathAlgebra.mapAlgHom`. -/
private theorem mapAlgHom_hone (φ : Q ⥤q R) (hφ : Function.Bijective φ.obj) :
    letI := Fintype.ofFinite Q
    ∑ v : Q, (ofPath (mapTotalPath φ ⟨v, v, Quiver.Path.nil⟩) : pathAlgebra k R) = 1 := by
  let _ := Fintype.ofFinite Q
  let _ := Fintype.ofFinite R
  rw [one_def]
  refine Fintype.sum_bijective _ hφ _ _ fun v ↦ ?_
  rw [mapTotalPath_mk, Prefunctor.mapPath_nil, vertexIdempotent_eq_single, ofPath_eq_single]

/-- **The algebra homomorphism of path algebras induced by a prefunctor** bijective on vertices: it
sends the basis element of a path to the basis element of the image path. -/
noncomputable def mapAlgHom (φ : Q ⥤q R) (hφ : Function.Bijective φ.obj) :
    pathAlgebra k Q →ₐ[k] pathAlgebra k R :=
  liftAlgHom k (fun x ↦ ofPath (mapTotalPath φ x)) (mapAlgHom_hcomp k φ)
    (mapAlgHom_hzero k φ hφ.1) (mapAlgHom_hone k φ hφ)

/-- The induced homomorphism sends the basis element of an indexed path to the basis element of the
pushed-forward path. -/
@[simp]
theorem mapAlgHom_ofPath (φ : Q ⥤q R) (hφ : Function.Bijective φ.obj)
    (x : Quiver.TotalPath Q) :
    mapAlgHom k φ hφ (ofPath x) = ofPath (mapTotalPath φ x) :=
  liftAlgHom_ofPath k _ (mapAlgHom_hcomp k φ) (mapAlgHom_hzero k φ hφ.1) (mapAlgHom_hone k φ hφ) x

/-- The induced homomorphism sends a scalar multiple of a basis path to the same scalar multiple of
the pushed-forward basis path. -/
@[simp]
theorem mapAlgHom_single (φ : Q ⥤q R) (hφ : Function.Bijective φ.obj)
    (x : Quiver.TotalPath Q) (c : k) :
    mapAlgHom k φ hφ (single x c) = single (mapTotalPath φ x) c :=
  (liftAlgHom_single k _ (mapAlgHom_hcomp k φ) (mapAlgHom_hzero k φ hφ.1)
    (mapAlgHom_hone k φ hφ) x c).trans (by
      rw [ofPath_eq_single, smul_single, mul_one])

/-- The induced homomorphism sends the idempotent of a vertex to the idempotent of the image
vertex. -/
@[simp]
theorem mapAlgHom_vertexIdempotent (φ : Q ⥤q R) (hφ : Function.Bijective φ.obj) (v : Q) :
    mapAlgHom k φ hφ (vertexIdempotent k v) = vertexIdempotent k (φ.obj v) := by
  rw [vertexIdempotent_eq_single, ← ofPath_eq_single, mapAlgHom_ofPath, mapTotalPath_mk,
    Prefunctor.mapPath_nil, ofPath_eq_single, ← vertexIdempotent_eq_single]

/-- Pushing an arrow along `mapAlgHom` carries it to the image arrow. Deliberately not a `simp`
lemma, `TauCeti.PathAlgebra.ofArrow_eq_ofPath` already rewriting its left-hand side. -/
theorem mapAlgHom_ofArrow (φ : Q ⥤q R) (hφ : Function.Bijective φ.obj) {a b : Q} (e : a ⟶ b) :
    mapAlgHom k φ hφ (ofArrow e) = ofArrow (φ.map e) := by
  rw [ofArrow_eq_ofPath, mapAlgHom_ofPath, mapTotalPath_mk, Prefunctor.mapPath_toPath,
    ofArrow_eq_ofPath]

/-- Equal prefunctors induce equal homomorphisms; the bijectivity hypotheses are propositions, so
they need not be compared. -/
theorem mapAlgHom_congr {φ φ' : Q ⥤q R} (h : φ = φ') (hφ : Function.Bijective φ.obj)
    (hφ' : Function.Bijective φ'.obj) : mapAlgHom k φ hφ = mapAlgHom k φ' hφ' := by
  subst h; rfl

-- The generated object projections of `Prefunctor.id` and `Prefunctor.comp` do not unfold at
-- implicit transparency, so the `change`s below expose the functions handled by the generic API.

/-- **The identity prefunctor induces the identity**. -/
@[simp]
theorem mapAlgHom_id :
    mapAlgHom k (Prefunctor.id Q) (by
      change Function.Bijective (id : Q → Q)
      exact Function.bijective_id) =
      AlgHom.id k (pathAlgebra k Q) :=
  algHom_ext k fun x ↦ by rw [mapAlgHom_ofPath, mapTotalPath_id, AlgHom.id_apply]

/-- **Composition of prefunctors induces composition**. The bijectivity of the composite is that
of the two factors. -/
theorem mapAlgHom_comp (φ : Q ⥤q R) (ψ : R ⥤q S) (hφ : Function.Bijective φ.obj)
    (hψ : Function.Bijective ψ.obj) :
    mapAlgHom k (φ.comp ψ) (by
      change Function.Bijective (ψ.obj ∘ φ.obj)
      exact hψ.comp hφ) =
      (mapAlgHom k ψ hψ).comp (mapAlgHom k φ hφ) :=
  algHom_ext k fun x ↦ by
    rw [mapAlgHom_ofPath, AlgHom.comp_apply, mapAlgHom_ofPath, mapAlgHom_ofPath,
      mapTotalPath_comp_apply]

/-- The composite of the two homomorphisms induced by mutually inverse prefunctors is the
identity. This is the pair of coherence hypotheses of `AlgEquiv.ofAlgHom` for
`TauCeti.PathAlgebra.mapAlgEquiv`. -/
private theorem mapAlgHom_comp_eq_id (φ : Q ⥤q R) (ψ : R ⥤q Q) (hφ : Function.Bijective φ.obj)
    (hψ : Function.Bijective ψ.obj) (hφψ : φ.comp ψ = Prefunctor.id Q) :
    (mapAlgHom k ψ hψ).comp (mapAlgHom k φ hφ) = AlgHom.id k (pathAlgebra k Q) :=
  (mapAlgHom_comp k φ ψ hφ hψ).symm.trans
    ((mapAlgHom_congr k hφψ
      (by
        change Function.Bijective (ψ.obj ∘ φ.obj)
        exact hψ.comp hφ)
      (by
        change Function.Bijective (id : Q → Q)
        exact Function.bijective_id)).trans
      (mapAlgHom_id k))

/-- **The algebra isomorphism of path algebras induced by an isomorphism of quivers**, presented as
a pair of mutually inverse prefunctors. -/
noncomputable def mapAlgEquiv (φ : Q ⥤q R) (ψ : R ⥤q Q) (hφψ : φ.comp ψ = Prefunctor.id Q)
    (hψφ : ψ.comp φ = Prefunctor.id R) : pathAlgebra k Q ≃ₐ[k] pathAlgebra k R :=
  AlgEquiv.ofAlgHom (mapAlgHom k φ (φ.obj_bijective_of_comp_eq_id ψ hφψ hψφ))
    (mapAlgHom k ψ (ψ.obj_bijective_of_comp_eq_id φ hψφ hφψ))
    (mapAlgHom_comp_eq_id k ψ φ _ _ hψφ) (mapAlgHom_comp_eq_id k φ ψ _ _ hφψ)

/-- The induced isomorphism acts as the homomorphism induced by the forward prefunctor. -/
@[simp]
theorem mapAlgEquiv_apply (φ : Q ⥤q R) (ψ : R ⥤q Q) (hφψ : φ.comp ψ = Prefunctor.id Q)
    (hψφ : ψ.comp φ = Prefunctor.id R) (x : pathAlgebra k Q) :
    mapAlgEquiv k φ ψ hφψ hψφ x = mapAlgHom k φ (φ.obj_bijective_of_comp_eq_id ψ hφψ hψφ) x := by
  rw [mapAlgEquiv, AlgEquiv.ofAlgHom_apply]

/-- The inverse of the induced isomorphism acts as the homomorphism induced by the inverse
prefunctor. Deliberately not a `simp` lemma: `TauCeti.PathAlgebra.mapAlgEquiv_symm` followed by
`TauCeti.PathAlgebra.mapAlgEquiv_apply` already rewrites its left-hand side, and `simpNF` rejects
the pair. -/
theorem mapAlgEquiv_symm_apply (φ : Q ⥤q R) (ψ : R ⥤q Q) (hφψ : φ.comp ψ = Prefunctor.id Q)
    (hψφ : ψ.comp φ = Prefunctor.id R) (y : pathAlgebra k R) :
    (mapAlgEquiv k φ ψ hφψ hψφ).symm y =
      mapAlgHom k ψ (ψ.obj_bijective_of_comp_eq_id φ hψφ hφψ) y := by
  rw [mapAlgEquiv, AlgEquiv.ofAlgHom_symm, AlgEquiv.ofAlgHom_apply]

/-- Equal pairs of prefunctors induce equal isomorphisms; the coherence hypotheses are
propositions, so they need not be compared. -/
theorem mapAlgEquiv_congr {φ φ' : Q ⥤q R} {ψ ψ' : R ⥤q Q} (hφ : φ = φ') (hψ : ψ = ψ')
    (hφψ : φ.comp ψ = Prefunctor.id Q) (hψφ : ψ.comp φ = Prefunctor.id R)
    (hφψ' : φ'.comp ψ' = Prefunctor.id Q) (hψφ' : ψ'.comp φ' = Prefunctor.id R) :
    mapAlgEquiv k φ ψ hφψ hψφ = mapAlgEquiv k φ' ψ' hφψ' hψφ' := by
  subst hφ; subst hψ; rfl

/-- **The identity prefunctor induces the identity isomorphism**. -/
@[simp]
theorem mapAlgEquiv_id :
    mapAlgEquiv k (Prefunctor.id Q) (Prefunctor.id Q) (Prefunctor.comp_id (Prefunctor.id Q))
      (Prefunctor.comp_id (Prefunctor.id Q)) = AlgEquiv.refl :=
  algEquiv_ext k fun x ↦ by
    rw [mapAlgEquiv_apply, mapAlgHom_ofPath, mapTotalPath_id]
    rfl

/-- **The inverse isomorphism is the one induced by the reversed pair**. -/
@[simp]
theorem mapAlgEquiv_symm (φ : Q ⥤q R) (ψ : R ⥤q Q) (hφψ : φ.comp ψ = Prefunctor.id Q)
    (hψφ : ψ.comp φ = Prefunctor.id R) :
    (mapAlgEquiv k φ ψ hφψ hψφ).symm = mapAlgEquiv k ψ φ hψφ hφψ :=
  AlgEquiv.ext fun y ↦ by rw [mapAlgEquiv_symm_apply, mapAlgEquiv_apply]

/-- **Composition of prefunctors induces composition of the isomorphisms**. The two inverse laws
of the composite pair are those of the two factor pairs, by
`Prefunctor.comp_comp_comp_eq_id`. -/
theorem mapAlgEquiv_comp (φ : Q ⥤q R) (ψ : R ⥤q Q) (φ' : R ⥤q S) (ψ' : S ⥤q R)
    (hφψ : φ.comp ψ = Prefunctor.id Q) (hψφ : ψ.comp φ = Prefunctor.id R)
    (hφψ' : φ'.comp ψ' = Prefunctor.id R) (hψφ' : ψ'.comp φ' = Prefunctor.id S) :
    mapAlgEquiv k (φ.comp φ') (ψ'.comp ψ) (φ.comp_comp_comp_eq_id ψ φ' ψ' hφψ hφψ')
        (ψ'.comp_comp_comp_eq_id φ' ψ φ hψφ' hψφ) =
      (mapAlgEquiv k φ ψ hφψ hψφ).trans (mapAlgEquiv k φ' ψ' hφψ' hψφ') :=
  algEquiv_ext k fun x ↦ by
    rw [AlgEquiv.trans_apply, mapAlgEquiv_apply, mapAlgEquiv_apply, mapAlgEquiv_apply,
      mapAlgHom_ofPath, mapAlgHom_ofPath, mapAlgHom_ofPath, mapTotalPath_comp_apply]

end Map

end PathAlgebra

end TauCeti
