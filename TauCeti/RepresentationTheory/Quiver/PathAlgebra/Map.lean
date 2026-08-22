/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

public section

/-!
# Path algebras are functorial in the quiver

A prefunctor `φ : Q ⥤q R` pushes a path of `Q` to a path of `R`, hence a basis element of `kQ` to a
basis element of `kR`. This file extends that assignment to an algebra homomorphism
`TauCeti.PathAlgebra.mapAlgHom`, and shows that it is an isomorphism when `φ` is one.

Two features of the path algebra bound what can be asked of `φ`. The unit of `kQ` is the sum of
*all* the vertex idempotents, so the assignment sends `1` to `∑ v : Q, e_{φ v}`, and that is the
unit of `kR` only when `φ` is **surjective** on vertices. Two paths of `Q` which do not meet
multiply to `0`, while their images multiply to `0` only when they still do not meet, and that is
guaranteed by **injectivity** on vertices. So `mapAlgHom` asks that `φ` be bijective on vertices,
which is what the intended source of prefunctors — an isomorphism of the underlying graph or
quiver — supplies. Nothing is asked of `φ` on arrows: a prefunctor which is not injective on
arrows still gives an algebra homomorphism, just not an injective one.

## Main definitions

* `TauCeti.PathAlgebra.mapTotalPath`: the indexed path obtained by pushing an indexed path along a
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
* `TauCeti.PathAlgebra.algEquiv_ext`: an algebra isomorphism out of a path algebra is determined by
  its values on the paths.
* `TauCeti.PathAlgebra.ofArrow_homOfEq`: transporting an arrow along equalities of its endpoints
  does not change the basis element it names.
* `Prefunctor.length_mapPath`: pushing a path along a prefunctor preserves its length.
* `Prefunctor.bijective_obj_of_comp_eq_id`: mutually inverse prefunctors are bijective on
  vertices, which is what feeds `TauCeti.PathAlgebra.mapAlgEquiv`.

## References

This is the "functoriality under graph/quiver isomorphism" clause of Layer 0 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`, at the level of the ambient path algebra; the
relation quotients are carried along it in
`TauCeti/RepresentationTheory/Quiver/Zigzag/Isomorphism.lean`.
-/

namespace TauCeti

universe u u' u'' v v' v'' w

/-- **Pushing a path along a prefunctor preserves its length**: the image path traverses the image
of each arrow of the original, in order. -/
theorem _root_.Prefunctor.length_mapPath {Q : Type u} {R : Type u'} [Quiver.{v} Q] [Quiver.{v'} R]
    (φ : Q ⥤q R) {a b : Q} (p : Quiver.Path a b) : (φ.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => rw [Prefunctor.mapPath_cons, Quiver.Path.length_cons, ih,
      Quiver.Path.length_cons]

/-- **Mutually inverse prefunctors are bijective on vertices.** -/
theorem _root_.Prefunctor.bijective_obj_of_comp_eq_id {Q : Type u} {R : Type u'} [Quiver.{v} Q]
    [Quiver.{v'} R] (φ : Q ⥤q R) (ψ : R ⥤q Q) (hφψ : φ.comp ψ = Prefunctor.id Q)
    (hψφ : ψ.comp φ = Prefunctor.id R) : Function.Bijective φ.obj :=
  Function.bijective_iff_has_inverse.mpr
    ⟨ψ.obj, fun a ↦ congrArg (fun F : Q ⥤q Q ↦ F.obj a) hφψ,
      fun b ↦ congrArg (fun F : R ⥤q R ↦ F.obj b) hψφ⟩

namespace PathAlgebra

section Map

variable {Q : Type u} {R : Type u'} {S : Type u''} [Quiver.{v} Q] [Quiver.{v'} R] [Quiver.{v''} S]

/-- The indexed path of `R` obtained by pushing an indexed path of `Q` along a prefunctor. This is
the map on the path bases which `TauCeti.PathAlgebra.mapAlgHom` extends. It is exposed so that its
three components reduce, which is what the projection lemmas below record. -/
@[expose] def mapTotalPath (φ : Q ⥤q R) (x : Quiver.TotalPath Q) : Quiver.TotalPath R :=
  ⟨φ.obj x.1, φ.obj x.2.1, φ.mapPath x.2.2⟩

@[simp]
theorem mapTotalPath_mk (φ : Q ⥤q R) {a b : Q} (p : Quiver.Path a b) :
    mapTotalPath φ ⟨a, b, p⟩ = ⟨φ.obj a, φ.obj b, φ.mapPath p⟩ := rfl

@[simp]
theorem mapTotalPath_fst (φ : Q ⥤q R) (x : Quiver.TotalPath Q) :
    (mapTotalPath φ x).1 = φ.obj x.1 := rfl

@[simp]
theorem mapTotalPath_snd_fst (φ : Q ⥤q R) (x : Quiver.TotalPath Q) :
    (mapTotalPath φ x).2.1 = φ.obj x.2.1 := rfl

@[simp]
theorem length_mapTotalPath (φ : Q ⥤q R) (x : Quiver.TotalPath Q) :
    (mapTotalPath φ x).2.2.length = x.2.2.length :=
  φ.length_mapPath x.2.2

@[simp]
theorem mapTotalPath_id (x : Quiver.TotalPath Q) : mapTotalPath (Prefunctor.id Q) x = x := by
  obtain ⟨a, b, p⟩ := x
  rw [mapTotalPath_mk, Prefunctor.mapPath_id]
  rfl

theorem mapTotalPath_comp (φ : Q ⥤q R) (ψ : R ⥤q S) (x : Quiver.TotalPath Q) :
    mapTotalPath (φ.comp ψ) x = mapTotalPath ψ (mapTotalPath φ x) := by
  obtain ⟨a, b, p⟩ := x
  rw [mapTotalPath_mk, mapTotalPath_mk, mapTotalPath_mk, Prefunctor.mapPath_comp_apply]
  rfl

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
  ofPath_mul_ofPath_of_not_composable fun hc ↦ h (hφ hc)

/-- The images of the trivial paths under a prefunctor surjective on vertices are all the vertex
idempotents of the target, so they decompose its unit. This is the `hone` hypothesis of
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

@[simp]
theorem mapAlgHom_ofPath (φ : Q ⥤q R) (hφ : Function.Bijective φ.obj)
    (x : Quiver.TotalPath Q) :
    mapAlgHom k φ hφ (ofPath x) = ofPath (mapTotalPath φ x) :=
  liftAlgHom_ofPath k _ (mapAlgHom_hcomp k φ) (mapAlgHom_hzero k φ hφ.1) (mapAlgHom_hone k φ hφ) x

@[simp]
theorem mapAlgHom_single (φ : Q ⥤q R) (hφ : Function.Bijective φ.obj)
    (x : Quiver.TotalPath Q) (c : k) :
    mapAlgHom k φ hφ (single x c) = single (mapTotalPath φ x) c := by
  have hx : (single x c : pathAlgebra k Q) = c • ofPath x := by
    rw [ofPath_eq_single, smul_single, mul_one]
  rw [hx, map_smul, mapAlgHom_ofPath, ofPath_eq_single, smul_single, mul_one]

@[simp]
theorem mapAlgHom_vertexIdempotent (φ : Q ⥤q R) (hφ : Function.Bijective φ.obj) (v : Q) :
    mapAlgHom k φ hφ (vertexIdempotent k v) = vertexIdempotent k (φ.obj v) := by
  rw [vertexIdempotent_eq_single, mapAlgHom_single, mapTotalPath_mk, Prefunctor.mapPath_nil,
    vertexIdempotent_eq_single]

@[simp]
theorem mapAlgHom_ofArrow (φ : Q ⥤q R) (hφ : Function.Bijective φ.obj) {a b : Q} (e : a ⟶ b) :
    mapAlgHom k φ hφ (ofArrow e) = ofArrow (φ.map e) := by
  rw [ofArrow_eq_ofPath, mapAlgHom_ofPath, mapTotalPath_mk, Prefunctor.mapPath_toPath,
    ofArrow_eq_ofPath]

omit [Finite Q] in
/-- Transporting an arrow along equalities of its source and target does not change the basis
element it names, the endpoints of a path being recorded in the path itself. -/
theorem ofArrow_homOfEq {a b a' b' : Q} (f : a ⟶ b) (ha : a = a') (hb : b = b') :
    (ofArrow (Quiver.homOfEq f ha hb) : pathAlgebra k Q) = ofArrow f := by
  subst ha
  subst hb
  rfl

/-- Equal prefunctors induce equal homomorphisms; the bijectivity hypotheses are propositions, so
they need not be compared. -/
theorem mapAlgHom_congr {φ φ' : Q ⥤q R} (h : φ = φ') (hφ : Function.Bijective φ.obj)
    (hφ' : Function.Bijective φ'.obj) : mapAlgHom k φ hφ = mapAlgHom k φ' hφ' := by
  subst h; rfl

/-- **The identity prefunctor induces the identity**. -/
theorem mapAlgHom_id (hφ : Function.Bijective (Prefunctor.id Q).obj) :
    mapAlgHom k (Prefunctor.id Q) hφ = AlgHom.id k (pathAlgebra k Q) :=
  algHom_ext k fun x ↦ by rw [mapAlgHom_ofPath, mapTotalPath_id, AlgHom.id_apply]

/-- **Composition of prefunctors induces composition**. -/
theorem mapAlgHom_comp (φ : Q ⥤q R) (ψ : R ⥤q S) (hφ : Function.Bijective φ.obj)
    (hψ : Function.Bijective ψ.obj) (hφψ : Function.Bijective (φ.comp ψ).obj) :
    mapAlgHom k (φ.comp ψ) hφψ = (mapAlgHom k ψ hψ).comp (mapAlgHom k φ hφ) :=
  algHom_ext k fun x ↦ by
    rw [mapAlgHom_ofPath, AlgHom.comp_apply, mapAlgHom_ofPath, mapAlgHom_ofPath,
      mapTotalPath_comp]

/-- **The algebra isomorphism of path algebras induced by an isomorphism of quivers**, presented as
a pair of mutually inverse prefunctors. -/
noncomputable def mapAlgEquiv (φ : Q ⥤q R) (ψ : R ⥤q Q) (hφψ : φ.comp ψ = Prefunctor.id Q)
    (hψφ : ψ.comp φ = Prefunctor.id R) : pathAlgebra k Q ≃ₐ[k] pathAlgebra k R :=
  AlgEquiv.ofAlgHom (mapAlgHom k φ (φ.bijective_obj_of_comp_eq_id ψ hφψ hψφ))
    (mapAlgHom k ψ (ψ.bijective_obj_of_comp_eq_id φ hψφ hφψ))
    (algHom_ext k fun y ↦ by
      rw [AlgHom.comp_apply, mapAlgHom_ofPath, mapAlgHom_ofPath, ← mapTotalPath_comp, hψφ,
        mapTotalPath_id, AlgHom.id_apply])
    (algHom_ext k fun x ↦ by
      rw [AlgHom.comp_apply, mapAlgHom_ofPath, mapAlgHom_ofPath, ← mapTotalPath_comp, hφψ,
        mapTotalPath_id, AlgHom.id_apply])

@[simp]
theorem mapAlgEquiv_apply (φ : Q ⥤q R) (ψ : R ⥤q Q) (hφψ : φ.comp ψ = Prefunctor.id Q)
    (hψφ : ψ.comp φ = Prefunctor.id R) (x : pathAlgebra k Q) :
    mapAlgEquiv k φ ψ hφψ hψφ x = mapAlgHom k φ (φ.bijective_obj_of_comp_eq_id ψ hφψ hψφ) x := by
  rw [mapAlgEquiv, AlgEquiv.ofAlgHom_apply]

/-- **Algebra isomorphisms out of a path algebra are determined by their values on the paths.** -/
theorem algEquiv_ext {B : Type*} [Semiring B] [Algebra k B]
    {f g : pathAlgebra k Q ≃ₐ[k] B} (h : ∀ x, f (ofPath x) = g (ofPath x)) : f = g :=
  AlgEquiv.ext fun y ↦
    congrArg (fun F : pathAlgebra k Q →ₐ[k] B ↦ F y)
      (algHom_ext k (f := (f : pathAlgebra k Q →ₐ[k] B)) (g := (g : pathAlgebra k Q →ₐ[k] B)) h)

@[simp]
theorem mapAlgEquiv_symm_apply (φ : Q ⥤q R) (ψ : R ⥤q Q) (hφψ : φ.comp ψ = Prefunctor.id Q)
    (hψφ : ψ.comp φ = Prefunctor.id R) (y : pathAlgebra k R) :
    (mapAlgEquiv k φ ψ hφψ hψφ).symm y =
      mapAlgHom k ψ (ψ.bijective_obj_of_comp_eq_id φ hψφ hφψ) y := by
  rw [mapAlgEquiv, AlgEquiv.ofAlgHom_symm, AlgEquiv.ofAlgHom_apply]

end Map

end PathAlgebra

end TauCeti
