/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.Basic
public import TauCeti.RepresentationTheory.Quiver.Reflection.DimensionVector
public import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# Reflecting a representation at a sink

For a sink `i` of a quiver `Q` -- a vertex no arrow leaves -- the Bernstein-Gelfand-Ponomarev
construction turns a representation `M` of `Q` into a representation of the reflected quiver
`TauCeti.Quiver.Reflect Q i`, in which every arrow at `i` points the other way. Away from `i`
nothing changes; at `i` the vector space `Mᵢ` is replaced by the kernel of the map

`⨁_{a : b ⟶ i} M_b → Mᵢ`

that sums the actions of the arrows into `i`, and each reversed arrow acts by the corresponding
coordinate projection out of that kernel. This file builds that representation and computes its
dimension vector, and bundles the construction as a functor on representations.

The content of the computation is that on dimension vectors the construction realizes the simple
reflection `sᵢ` of `TauCeti.RepresentationTheory.Quiver.Reflection.DimensionVector`, provided the
summing map is surjective: the reflected space at `i` then has dimension
`∑_b #(b ⟶ i) · dim M_b - dim Mᵢ`, which is exactly `sᵢ` applied to the dimension vector of `M`,
because a sink has no outgoing arrow. Surjectivity is the honest hypothesis here and it is not
automatic: it fails exactly the way `TauCeti.incomingSum_not_surjective` records, for a
representation concentrated at `i` whose space at `i` is nontrivial, of which the vertex simple
`Sᵢ` is the example. The reflection has zero vertex space at `i` in this boundary case, by
`TauCeti.subsingleton_reflectRep_obj_self`; in particular, it kills the vertex simple `Sᵢ`.

## Main definitions

* `TauCeti.incomingSum`: the map `⨁_{a : b ⟶ i} M_b → Mᵢ` summing the arrows into a vertex,
  defined at every vertex of every representation, whose range contains the image of every arrow
  into that vertex (`TauCeti.map_toPath_mem_range_incomingSum`).
* `TauCeti.reflectRep`: the reflection `C⁺ᵢ M` of a representation at a sink `i`, a
  representation of `TauCeti.Quiver.Reflect Q i`.
* `TauCeti.reflectionFunctor`: the BGP reflection functor at a sink.

## Main results

* `TauCeti.incomingSum_single`: the incoming sum of a family supported at one arrow is the action
  of that arrow.
* `TauCeti.incomingSum_naturality`: the incoming sum is natural in the representation.
* `TauCeti.reflectRep_obj_self` and `TauCeti.reflectRep_obj_of_ne`: the vertex spaces of `C⁺ᵢ M`.
* `TauCeti.reflectRep_map_reflectArrow` and `TauCeti.reflectRep_map_reflectArrowOfNeOfNe`: the
  action of a reversed arrow, by a coordinate projection out of the kernel, and of an arrow away
  from `i`, unchanged.
* `TauCeti.reflectionFunctor_obj`: the functor sends `M` to `TauCeti.reflectRep M`, so the whole
  `reflectRep` interface computes its objects.
* `TauCeti.reflectionFunctor_map_app_self_apply` and
  `TauCeti.reflectionFunctor_map_app_of_ne`: the action of reflection on morphisms.
* `TauCeti.reflectionFunctor_additive`: the reflection functor is additive.
* `TauCeti.dimVector_reflectRep_of_ne` and `TauCeti.dimVector_reflectRep_self_add`: the dimension
  vector of `C⁺ᵢ M`, away from `i` and at `i`.
* `TauCeti.dimVector_reflectRep`: `dim (C⁺ᵢ M) = sᵢ (dim M)` when the summing map is surjective.
* `TauCeti.incomingSum_not_surjective`: that surjectivity fails for a representation concentrated
  at `i` with nontrivial space there, and `TauCeti.subsingleton_reflectRep_obj_self`: the reflected
  space at `i` vanishes under the same source-vanishing hypothesis. Together they describe the
  vertex simple `Sᵢ`, the boundary case of the previous result.

## Implementation notes

The vertex spaces branch on equality with `i`, so they are written with an `if` and decided
classically; no `DecidableEq Q` instance therefore appears in the interface of the construction,
exactly as for `TauCeti.simpleRep`. Only the statements naming `TauCeti.vertexPreReflection` assume
`DecidableEq Q`, because `Pi.single` needs one.

The vertex spaces, the prefunctor that `TauCeti.reflectRep` lifts, and the kernel maps underlying
the action on morphisms are private. The `reflectRep_obj_*`, `reflectRep_map_*`,
`reflectionFunctor_obj`, and `reflectionFunctor_map_app_*` theorems provide the interface
downstream files should use. The body of `TauCeti.reflectionFunctor` is not exposed outside this
module, so `reflectionFunctor_obj` cannot be proved by `rfl` where it is stated; it restates a
private unfolding lemma. A vertex space of a functor object is therefore computed by
`reflectionFunctor_obj` followed by the matching `reflectRep_obj_*` result, and that composite is
exactly the transport appearing in the `reflectionFunctor_map_app_*` statements.

The arrows of `TauCeti.Quiver.Reflect Q i` are given by `TauCeti.Quiver.reflectHom`, which is
again an `if` on equality with `i`, so an arrow of the reflected quiver is a *cast* of an arrow of
`Q`: `TauCeti.Quiver.reflectArrow` and `TauCeti.Quiver.reflectArrowOfNeOfNe` name the two casts, and
the computation rules for the action are stated on them. Both branches at `i` that a general vertex
would allow are impossible at a sink -- the reflected quiver has no arrow into `i` and `i` carries
no loop -- and the definition discharges them from `TauCeti.Quiver.IsSink`.

The universes are constrained the least the construction allows: the vertex spaces of `M` are
taken in `max v w x` for the vertex universe `v`, the arrow universe `w` and an arbitrary `x`,
because the reflected space at `i` is cut out of a product indexed by the arrows into `i`, which
lives in `max v w` together with the vertex spaces. The universe of the field is unconstrained.

A vertex `i : Q` is used below as an object of the free category `CategoryTheory.Paths Q`, which
is `Q` itself only by unfolding a semireducible definition; as in the neighbouring files, the
`CategoryTheory.Paths.of` annotations record that identification where a proof needs it.

## References

This implements the reflection at a sink of the reflection functors of Layer 4 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See
Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's theorem*, and
Derksen--Weyman, *An Introduction to Quiver Representations*, Ch. 2.
-/

public section

namespace TauCeti

open CategoryTheory
open _root_.TauCeti.Quiver

universe u v w x

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

/-! ### The sum of the arrows into a vertex -/

section IncomingSum

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

open scoped Classical in
/-- **The sum of the arrows into a vertex.** For a representation `M` of a finite quiver and a
vertex `i`, this is the linear map `⨁_{a : b ⟶ i} M_b → Mᵢ` sending a family of vectors, indexed
by the arrows into `i`, to the sum of their images under the corresponding arrows. Its kernel is
the vector space that `TauCeti.reflectRep` puts at `i`. It is `LinearMap.lsum` applied to the
actions of the arrows into `i`; the decidable equality that combinator needs is supplied
classically, so none appears in the interface.

No hypothesis on `i` is imposed: the map is defined at every vertex, and it is the reflection that
needs `i` to be a sink. -/
noncomputable def incomingSum (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q) :
    ((e : Σ b : Q, (b ⟶ i)) → M.obj e.1) →ₗ[k] M.obj i :=
  LinearMap.lsum k (fun e : Σ b : Q, (b ⟶ i) ↦ M.obj e.1) k fun e ↦ (M.map e.2.toPath).hom

/-- `TauCeti.incomingSum` sends a family of vectors indexed by the arrows into `i` to the sum,
over those arrows, of the images of its coordinates under the corresponding arrow actions. -/
@[simp]
theorem incomingSum_apply (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q)
    (f : (e : Σ b : Q, (b ⟶ i)) → M.obj e.1) :
    incomingSum M i f = ∑ e : Σ b : Q, (b ⟶ i), (M.map e.2.toPath).hom (f e) := by
  simp [incomingSum]

open scoped Classical in
/-- **The incoming sum of a family supported at one arrow** is the action of that arrow: every
other summand vanishes. -/
theorem incomingSum_single (M : QuiverRep.{u, v, w, max v w x} k Q) {b i : Q} (e : b ⟶ i)
    (y : M.obj b) :
    incomingSum M i (Pi.single (⟨b, e⟩ : Σ b : Q, (b ⟶ i)) y) = (M.map e.toPath).hom y := by
  rw [incomingSum_apply, Finset.sum_eq_single_of_mem ⟨b, e⟩ (Finset.mem_univ _)]
  · simp
  · intro c _ hc
    simp [Pi.single_eq_of_ne hc]

/-- **The image of an arrow into `i` lies in the range of `TauCeti.incomingSum`.** -/
theorem map_toPath_mem_range_incomingSum (M : QuiverRep.{u, v, w, max v w x} k Q) {b i : Q}
    (e : b ⟶ i) (y : M.obj b) :
    (M.map e.toPath).hom y ∈ LinearMap.range (incomingSum M i) := by
  classical
  exact ⟨Pi.single ⟨b, e⟩ y, incomingSum_single M e y⟩

/-- The source of `TauCeti.incomingSum` has dimension `∑_b #(b ⟶ i) · dim M_b`. Only the vertex
spaces at the sources of arrows into `i` need be finite-dimensional; they are the only ones the
domain is built from. -/
theorem finrank_pi_incoming (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q)
    (hM : ∀ e : Σ b : Q, (b ⟶ i), FiniteDimensional k (M.obj e.1)) :
    Module.finrank k ((e : Σ b : Q, (b ⟶ i)) → M.obj e.1)
      = ∑ b : Q, Fintype.card (b ⟶ i) * Module.finrank k (M.obj b) := by
  -- The summand depends only on the source vertex, so record first, for an arbitrary
  -- `g : Q → ℕ`, that summing `g` over the arrows into `i` weights each vertex by its arrow
  -- count. Stating that for a function on `Q` keeps the identification of `Q` with
  -- `CategoryTheory.Paths Q` out of the way: `M.obj e.1` is type-correct only up to unfolding
  -- `CategoryTheory.Paths`, which blocks a rewrite under the sigma projection.
  have key : ∀ g : Q → ℕ,
      (∑ e : Σ b : Q, (b ⟶ i), g e.1) = ∑ b : Q, Fintype.card (b ⟶ i) * g b := fun g ↦ by
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun b _ ↦ by simp
  rw [Module.finrank_pi_fintype]
  exact key fun b ↦ Module.finrank k (M.obj b)

end IncomingSum

/-! ### The reflected representation -/

section ReflectRep

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

open scoped Classical in
/-- The vertex spaces of the reflected representation: the kernel of `TauCeti.incomingSum` at `i`,
and the vertex spaces of `M` everywhere else. An implementation helper for
`TauCeti.reflectRep`, whose vertex spaces are described by `TauCeti.reflectRep_obj_self` and
`TauCeti.reflectRep_obj_of_ne`. -/
private noncomputable def reflectRepObj (M : QuiverRep.{u, v, w, max v w x} k Q) (i j : Q) :
    ModuleCat.{max v w x} k :=
  if j = i then ModuleCat.of k (LinearMap.ker (incomingSum M i)) else M.obj j

/-- At the reflected vertex the vertex space is the kernel of `TauCeti.incomingSum`. -/
private theorem reflectRepObj_self (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q) :
    reflectRepObj M i i = ModuleCat.of k (LinearMap.ker (incomingSum M i)) :=
  ite_eq_left rfl

/-- Away from the reflected vertex the vertex spaces are those of `M`. -/
private theorem reflectRepObj_of_ne (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q) {j : Q}
    (h : j ≠ i) : reflectRepObj M i j = M.obj j :=
  ite_eq_right h

open scoped Classical in
/-- The prefunctor underlying the reflection at a sink: the vertex spaces of `reflectRepObj`,
together with the action of a single arrow of the reflected quiver. A reversed arrow acts by the
matching coordinate projection out of the kernel at `i`; every other arrow acts as it does in `M`.

At a sink the reflected quiver has no arrow into `i` and no loop at `i`, so those two branches are
impossible and are discharged from the hypothesis.

An implementation helper for `TauCeti.reflectRep`, whose action is described by
`TauCeti.reflectRep_map_reflectArrow` and `TauCeti.reflectRep_map_reflectArrowOfNeOfNe`. -/
private noncomputable def reflectPrefunctor (M : QuiverRep.{u, v, w, max v w x} k Q) {i : Q}
    (hi : IsSink i) : Reflect Q i ⥤q ModuleCat.{max v w x} k where
  obj j := reflectRepObj M i j
  map {a b} e :=
    if hb : b = i then
      (hi.isEmpty_hom a).elim
        (cast (((hom_reflect i a b).trans
          (congrArg (reflectHom i a) hb)).trans (reflectHom_right i a)) e)
    else if ha : a = i then
      eqToHom ((congrArg (reflectRepObj M i) ha).trans (reflectRepObj_self M i)) ≫
        ModuleCat.ofHom ((LinearMap.proj
            (⟨b, cast (((hom_reflect i a b).trans
              (congrArg (fun z ↦ reflectHom i z b) ha)).trans (reflectHom_left i b)) e⟩ :
              Σ b : Q, (b ⟶ i))).comp
          (LinearMap.ker (incomingSum M i)).subtype) ≫
        eqToHom (reflectRepObj_of_ne M i hb).symm
    else
      eqToHom (reflectRepObj_of_ne M i ha) ≫
        M.map (cast ((hom_reflect i a b).trans (reflectHom_of_ne_of_ne ha hb)) e).toPath ≫
        eqToHom (reflectRepObj_of_ne M i hb).symm

/-- **The reflection of a representation at a sink** `i`: the representation `C⁺ᵢ M` of the
reflected quiver `TauCeti.Quiver.Reflect Q i` that agrees with `M` away from `i`, puts the kernel
of `TauCeti.incomingSum` at `i`, and lets each reversed arrow act by the matching coordinate
projection out of that kernel. -/
noncomputable def reflectRep (M : QuiverRep.{u, v, w, max v w x} k Q) {i : Q}
    (hi : IsSink i) : QuiverRep k (Reflect Q i) :=
  Paths.lift (reflectPrefunctor M hi)

variable (M : QuiverRep.{u, v, w, max v w x} k Q) {i : Q} (hi : IsSink i)

/-- The vertex spaces of the reflection are those of the prefunctor it is lifted from. -/
private theorem reflectRep_obj (j : Reflect Q i) : (reflectRep M hi).obj j = reflectRepObj M i j :=
  rfl

/-- A single arrow of the reflected quiver acts through the prefunctor. -/
private theorem reflectRep_map_toPath {a b : Reflect Q i} (e : a ⟶ b) :
    (reflectRep M hi).map e.toPath = (reflectPrefunctor M hi).map e :=
  Paths.lift_toPath _ e

/-- **The reflected representation at the reflected vertex** is the kernel of the sum of the
arrows into `i`. -/
@[simp]
theorem reflectRep_obj_self :
    (reflectRep M hi).obj i = ModuleCat.of k (LinearMap.ker (incomingSum M i)) :=
  (reflectRep_obj M hi i).trans (reflectRepObj_self M i)

/-- Away from `i` the reflected representation is unchanged. -/
@[simp]
theorem reflectRep_obj_of_ne {j : Q} (h : j ≠ i) : (reflectRep M hi).obj j = M.obj j :=
  (reflectRep_obj M hi j).trans (reflectRepObj_of_ne M i h)

/-- **A reversed arrow acts by a coordinate projection.** The arrow `i ⟶ b` of the reflected
quiver coming from an arrow `e : b ⟶ i` of `Q` sends an element of the kernel at `i` to its
coordinate at `e`. The source `b` of such an arrow is automatically distinct from `i`, since a
sink carries no loop. -/
@[simp]
theorem reflectRep_map_reflectArrow {b : Q} (e : b ⟶ i) :
    (reflectRep M hi).map (reflectArrow i e).toPath
      = eqToHom (reflectRep_obj_self M hi) ≫
        ModuleCat.ofHom ((LinearMap.proj (⟨b, e⟩ : Σ b : Q, (b ⟶ i))).comp
          (LinearMap.ker (incomingSum M i)).subtype) ≫
        eqToHom (reflectRep_obj_of_ne M hi (hi.ne_of_hom e)).symm := by
  classical
  refine ((reflectRep_map_toPath M hi (reflectArrow i e)).trans
    (dite_eq_right (hi.ne_of_hom e))).trans ?_
  refine (dite_eq_left rfl).trans ?_
  conv_lhs => rw [cast_reflectArrow]
  rfl

/-- **An arrow away from the reflected vertex acts unchanged.** -/
@[simp]
theorem reflectRep_map_reflectArrowOfNeOfNe {a b : Q} (ha : a ≠ i) (hb : b ≠ i) (e : a ⟶ b) :
    (reflectRep M hi).map (reflectArrowOfNeOfNe ha hb e).toPath
      = eqToHom (reflectRep_obj_of_ne M hi ha) ≫ M.map e.toPath ≫
        eqToHom (reflectRep_obj_of_ne M hi hb).symm := by
  classical
  refine ((reflectRep_map_toPath (a := a) (b := b) M hi
    (reflectArrowOfNeOfNe ha hb e)).trans (dite_eq_right hb)).trans ?_
  refine (dite_eq_right ha).trans ?_
  conv_lhs => rw [cast_reflectArrowOfNeOfNe]
  rfl

omit [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)] in
/-- The pointwise map between the products indexed by arrows into `i`. -/
private def incomingMap {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) (i : Q) :
    ((e : Σ b : Q, (b ⟶ i)) → M.obj e.1) →ₗ[k]
      ((e : Σ b : Q, (b ⟶ i)) → N.obj e.1) where
  toFun f e := η.app e.1 (f e)
  map_add' f g := by ext e; simp
  map_smul' r f := by ext e; simp

omit [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)] in
/-- `TauCeti.incomingMap` applies its morphism in each coordinate. -/
private theorem incomingMap_apply {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) (i : Q)
    (f : (e : Σ b : Q, (b ⟶ i)) → M.obj e.1) :
    incomingMap η i f = fun e ↦ η.app e.1 (f e) :=
  rfl

/-- **The sum of the arrows into a vertex is natural in the representation.** Applying a morphism
`η` coordinatewise to a family indexed by the arrows into `i` and then summing is the same as
summing first and applying `η` at `i`; it is the naturality of `η` along those arrows, read off one
coordinate at a time. -/
theorem incomingSum_naturality {M N : QuiverRep.{u, v, w, max v w x} k Q}
    (η : M ⟶ N) (i : Q) (f : (e : Σ b : Q, (b ⟶ i)) → M.obj e.1) :
    incomingSum N i (fun e ↦ η.app e.1 (f e)) = η.app i (incomingSum M i f) := by
  rw [incomingSum_apply, incomingSum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact congrArg (fun g : M.obj e.1 ⟶ N.obj i ↦ g.hom (f e))
    (η.naturality e.2.toPath).symm

/-- The map between the kernels of the incoming sums induced by a morphism of representations. -/
private noncomputable def incomingKerMap {M N : QuiverRep.{u, v, w, max v w x} k Q}
    (η : M ⟶ N) (i : Q) :
    LinearMap.ker (incomingSum M i) →ₗ[k] LinearMap.ker (incomingSum N i) :=
  LinearMap.codRestrict (LinearMap.ker (incomingSum N i))
    ((incomingMap η i).domRestrict (LinearMap.ker (incomingSum M i))) fun f ↦ by
      rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, incomingMap_apply,
        incomingSum_naturality, f.property, map_zero]

@[simp]
private theorem incomingKerMap_id (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q) :
    incomingKerMap (𝟙 M) i = LinearMap.id := by
  ext f e
  rfl

@[simp]
private theorem incomingKerMap_comp {M N P : QuiverRep.{u, v, w, max v w x} k Q}
    (η : M ⟶ N) (θ : N ⟶ P) (i : Q) :
    incomingKerMap (η ≫ θ) i = (incomingKerMap θ i).comp (incomingKerMap η i) := by
  ext f e
  rfl

open scoped Classical in
/-- The component at a vertex of the reflected morphism. -/
private noncomputable def reflectRepMapApp
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSink i)
    (j : Reflect Q i) : (reflectRep M hi).obj j ⟶ (reflectRep N hi).obj j :=
  if hj : j = i then
    eqToHom ((congrArg (reflectRep M hi).obj hj).trans (reflectRep_obj_self M hi)) ≫
      ModuleCat.ofHom (incomingKerMap η i) ≫
      eqToHom ((congrArg (reflectRep N hi).obj hj).trans (reflectRep_obj_self N hi)).symm
  else
    eqToHom (reflectRep_obj_of_ne M hi hj) ≫ η.app j ≫
      eqToHom (reflectRep_obj_of_ne N hi hj).symm

@[simp]
private theorem reflectRepMapApp_self
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSink i) :
    reflectRepMapApp η hi i =
      eqToHom (reflectRep_obj_self M hi) ≫ ModuleCat.ofHom (incomingKerMap η i) ≫
        eqToHom (reflectRep_obj_self N hi).symm := by
  classical
  unfold reflectRepMapApp
  split
  · rfl
  · rename_i h
    exact (h rfl).elim

@[simp]
private theorem reflectRepMapApp_of_ne
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSink i)
    {j : Reflect Q i} (hj : j ≠ i) :
    reflectRepMapApp η hi j =
      eqToHom (reflectRep_obj_of_ne M hi hj) ≫ η.app j ≫
        eqToHom (reflectRep_obj_of_ne N hi hj).symm := by
  classical
  simp [reflectRepMapApp, hj]

/-! The components of the reflected morphism are transports of components of the original one, so
every identity about them is an identity of the original conjugated by `eqToHom`. The next five
lemmas are those conjugations, stated generically. They are what the proofs below use instead of
`simp`: the vertex `i` is used both as a vertex of `Q` and as an object of `CategoryTheory.Paths`
of the reflected quiver, so a goal about the reflected representation is type-correct only up to
unfolding the semireducible `CategoryTheory.Paths` and `TauCeti.Quiver.Reflect`, which is more than
the transparency `rw` and `simp` use to build a motive. Conjugation is stripped by `subst` inside
these lemmas, where no such identification is in play.

The first and the last of them are public: that obstruction, and this remedy for it, recur wherever
the reflection functor is used, so they are available to `TauCeti.reflectionFunctor`'s consumers
rather than copied by each of them. -/

/-- Transporting a morphism along object equalities and then back leaves it unchanged. -/
theorem eqToHom_conjugate_cancel {C : Type*} [Category* C] {X X' Y Y' : C}
    (hX : X = X') (hY : Y = Y') (f : X' ⟶ Y') :
    eqToHom hX.symm ≫ (eqToHom hX ≫ f ≫ eqToHom hY.symm) ≫ eqToHom hY = f := by
  subst X'
  subst Y'
  simp

/-- A conjugated identity is the identity. -/
private theorem eqToHom_conjugate_eq_id {C : Type*} [Category* C] {X Y : C} (h : X = Y)
    (f : Y ⟶ Y) (hf : f = 𝟙 Y) : eqToHom h ≫ f ≫ eqToHom h.symm = 𝟙 X := by
  subst h
  simp [hf]

/-- Conjugation distributes over composition. -/
private theorem eqToHom_conjugate_eq_comp {C : Type*} [Category* C] {X X' Y Y' Z Z' : C}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (f : X' ⟶ Z') (g : X' ⟶ Y') (h : Y' ⟶ Z')
    (hf : f = g ≫ h) :
    eqToHom hX ≫ f ≫ eqToHom hZ.symm =
      (eqToHom hX ≫ g ≫ eqToHom hY.symm) ≫ eqToHom hY ≫ h ≫ eqToHom hZ.symm := by
  subst hX
  subst hY
  subst hZ
  simp [hf]

/-- Conjugation by object equalities is additive. -/
private theorem eqToHom_conjugate_add {C : Type*} [Category* C] [Preadditive C] {X X' Y Y' : C}
    (hX : X = X') (hY : Y' = Y) {f g h : X' ⟶ Y'} (hfgh : f = g + h) :
    eqToHom hX ≫ f ≫ eqToHom hY
      = (eqToHom hX ≫ g ≫ eqToHom hY) + (eqToHom hX ≫ h ≫ eqToHom hY) := by
  subst hX
  subst hY
  simp [hfgh]

/-- **Conjugating a commuting square by object equalities leaves it commuting**, and nothing else
becomes commuting that way: the square of transported edges commutes exactly when the original
one does. -/
theorem eqToHom_conjugate_square {C : Type*} [Category* C] {X X' Y Y' Z Z' W W' : C}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (hW : W = W')
    (f : X' ⟶ Y') (g : Y' ⟶ Z') (f' : X' ⟶ W') (g' : W' ⟶ Z') :
    (eqToHom hX ≫ f ≫ eqToHom hY.symm) ≫ eqToHom hY ≫ g ≫ eqToHom hZ.symm =
        (eqToHom hX ≫ f' ≫ eqToHom hW.symm) ≫ eqToHom hW ≫ g' ≫ eqToHom hZ.symm ↔
      f ≫ g = f' ≫ g' := by
  subst hX
  subst hY
  subst hZ
  subst hW
  simp

/-- The components of the reflected morphism are natural for every arrow of the reflected
quiver. -/
private theorem reflectRepMapApp_naturality_arrow
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSink i)
    {a b : Reflect Q i} (e : a ⟶ b) :
    (reflectRep M hi).map e.toPath ≫ reflectRepMapApp η hi b =
      reflectRepMapApp η hi a ≫ (reflectRep N hi).map e.toPath := by
  classical
  by_cases hb : b = i
  · subst b
    exact (hi.isSource_reflect.isEmpty_hom a).elim e
  by_cases ha : a = i
  · subst a
    let e' : @_root_.Quiver.Hom Q _ b i :=
      cast ((@hom_reflect Q _ i i b).trans (@reflectHom_left Q _ i b)) e
    have he : @reflectArrow Q _ i b e' = e := @reflectArrow_cast Q _ i b e _
    rw [← he]
    rw [reflectRep_map_reflectArrow M hi e', reflectRep_map_reflectArrow N hi e']
    rw [reflectRepMapApp_of_ne η hi hb, reflectRepMapApp_self η hi]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    ext f
    rfl
  · let e' : @_root_.Quiver.Hom Q _ a b :=
      cast ((@hom_reflect Q _ i a b).trans (@reflectHom_of_ne_of_ne Q _ i a b ha hb)) e
    have he : @reflectArrowOfNeOfNe Q _ i a b ha hb e' = e :=
      @reflectArrowOfNeOfNe_cast Q _ i a b ha hb e _
    rw [← he]
    rw [reflectRep_map_reflectArrowOfNeOfNe M hi ha hb e',
      reflectRep_map_reflectArrowOfNeOfNe N hi ha hb e']
    rw [reflectRepMapApp_of_ne η hi ha, reflectRepMapApp_of_ne η hi hb]
    exact (eqToHom_conjugate_square _ _ (reflectRep_obj_of_ne N hi hb) _ _ _ _ _).mpr
      (η.naturality e'.toPath)

/-- The morphism between reflected representations induced by a morphism of representations. -/
private noncomputable def reflectRepMap
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSink i) :
    reflectRep M hi ⟶ reflectRep N hi :=
  Paths.liftNatTrans (reflectRepMapApp η hi) (reflectRepMapApp_naturality_arrow η hi)

/-- **The BGP reflection functor at a sink.** It sends a representation to
`TauCeti.reflectRep` and a morphism to the induced map between the kernels at the reflected vertex,
while leaving its components away from that vertex unchanged. -/
noncomputable def reflectionFunctor (i : Q) (hi : IsSink i) :
    QuiverRep.{u, v, w, max v w x} k Q ⥤ QuiverRep k (Reflect Q i) where
  obj M := reflectRep M hi
  map η := reflectRepMap η hi
  map_id M := by
    apply NatTrans.ext
    funext j
    classical
    change reflectRepMapApp (𝟙 M) hi j = 𝟙 _
    by_cases hj : j = i
    · subst j
      rw [reflectRepMapApp_self]
      exact eqToHom_conjugate_eq_id _ _ (by simp)
    · rw [reflectRepMapApp_of_ne _ _ hj]
      exact eqToHom_conjugate_eq_id _ _ rfl
  map_comp η θ := by
    apply NatTrans.ext
    funext j
    classical
    change reflectRepMapApp (η ≫ θ) hi j =
      reflectRepMapApp η hi j ≫ reflectRepMapApp θ hi j
    by_cases hj : j = i
    · subst j
      rw [reflectRepMapApp_self, reflectRepMapApp_self, reflectRepMapApp_self]
      exact eqToHom_conjugate_eq_comp _ _ (reflectRep_obj_self _ hi) _ _ _ (by simp)
    · rw [reflectRepMapApp_of_ne _ _ hj, reflectRepMapApp_of_ne _ _ hj,
        reflectRepMapApp_of_ne _ _ hj]
      exact eqToHom_conjugate_eq_comp _ _ (reflectRep_obj_of_ne _ hi hj) _ _ _ rfl

/-- The vertex components of the map supplied by `TauCeti.reflectionFunctor`. The functor sends a
morphism to `reflectRepMap`, a `CategoryTheory.Paths.liftNatTrans` of `reflectRepMapApp`, so this
is `rfl`; the two definitions are not exposed outside this module, so nothing public says it. -/
private theorem reflectionFunctor_map_app
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSink i)
    (j : Reflect Q i) :
    ((reflectionFunctor i hi).map η).app j = reflectRepMapApp η hi j :=
  rfl

/-- The induced map between the kernels is additive in the morphism, coordinate by coordinate. -/
private theorem incomingKerMap_add {M N : QuiverRep.{u, v, w, max v w x} k Q} (η θ : M ⟶ N)
    (i : Q) : incomingKerMap (η + θ) i = incomingKerMap η i + incomingKerMap θ i := by
  ext f e
  rfl

/-- **The BGP reflection functor is additive.** Away from the reflected vertex its components are
transports of the components of the given morphism, and at the reflected vertex the coordinatewise
map between the two kernels; both are additive in the morphism. -/
instance reflectionFunctor_additive (i : Q) (hi : IsSink i) :
    (reflectionFunctor (k := k) i hi).Additive where
  map_add {M N η θ} := by
    apply NatTrans.ext
    funext j
    classical
    rw [NatTrans.app_add, reflectionFunctor_map_app (η + θ) hi j, reflectionFunctor_map_app η hi j,
      reflectionFunctor_map_app θ hi j]
    by_cases hj : j = i
    · subst j
      rw [reflectRepMapApp_self, reflectRepMapApp_self, reflectRepMapApp_self]
      exact eqToHom_conjugate_add _ _ (by rw [incomingKerMap_add, ModuleCat.ofHom_add])
    · rw [reflectRepMapApp_of_ne _ _ hj, reflectRepMapApp_of_ne _ _ hj,
        reflectRepMapApp_of_ne _ _ hj]
      exact eqToHom_conjugate_add _ _ rfl

/-- Unfolding `TauCeti.reflectionFunctor` on objects. The body of the functor is not exposed
outside this module, so the public `TauCeti.reflectionFunctor_obj` below cannot itself be proved
by `rfl`; it restates this lemma. -/
private theorem reflectionFunctor_obj_def (i : Q) (hi : IsSink i)
    (M : QuiverRep.{u, v, w, max v w x} k Q) :
    (reflectionFunctor i hi).obj M = reflectRep M hi :=
  rfl

/-- **The objects of the BGP reflection functor.** The representation supplied by
`TauCeti.reflectionFunctor` is `TauCeti.reflectRep`, so the whole `TauCeti.reflectRep` interface --
its vertex spaces, the action of the reflected arrows, and its dimension vector -- describes it. -/
@[simp]
theorem reflectionFunctor_obj (i : Q) (hi : IsSink i)
    (M : QuiverRep.{u, v, w, max v w x} k Q) :
    (reflectionFunctor i hi).obj M = reflectRep M hi :=
  reflectionFunctor_obj_def i hi M

/-- At the reflected vertex, the map supplied by `TauCeti.reflectionFunctor`, transported to the
two kernels, is the induced kernel map. -/
private theorem reflectionFunctor_map_app_self
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSink i) :
    eqToHom (reflectRep_obj_self M hi).symm ≫
        ((reflectionFunctor i hi).map η).app i ≫ eqToHom (reflectRep_obj_self N hi) =
      ModuleCat.ofHom (incomingKerMap η i) := by
  rw [reflectionFunctor_map_app η hi i, reflectRepMapApp_self]
  exact eqToHom_conjugate_cancel _ _ _

/-- At the reflected vertex, reflection sends a morphism to the coordinatewise map between the
kernels of the incoming sums. The two vertex spaces are read off by `TauCeti.reflectionFunctor_obj`
followed by `TauCeti.reflectRep_obj_self`, which is the transport in the statement. -/
theorem reflectionFunctor_map_app_self_apply
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSink i)
    (f : LinearMap.ker (incomingSum M i)) (e : Σ b : Q, (b ⟶ i)) :
    ((eqToHom ((congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj i)
          (reflectionFunctor_obj i hi M)).trans (reflectRep_obj_self M hi)).symm ≫
        ((reflectionFunctor i hi).map η).app i ≫
        eqToHom ((congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj i)
          (reflectionFunctor_obj i hi N)).trans (reflectRep_obj_self N hi))) f).1 e
      = η.app e.1 (f.1 e) := by
  have hM : (congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj i)
      (reflectionFunctor_obj i hi M)).trans (reflectRep_obj_self M hi)
      = reflectRep_obj_self M hi := Subsingleton.elim _ _
  have hN : (congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj i)
      (reflectionFunctor_obj i hi N)).trans (reflectRep_obj_self N hi)
      = reflectRep_obj_self N hi := Subsingleton.elim _ _
  rw [hM, hN]
  exact congrArg (fun g : ModuleCat.of k (LinearMap.ker (incomingSum M i)) ⟶
      ModuleCat.of k (LinearMap.ker (incomingSum N i)) ↦ (g f).1 e)
    (reflectionFunctor_map_app_self η hi)

/-- Away from the reflected vertex, reflection leaves the components of a morphism unchanged. The
two vertex spaces are read off by `TauCeti.reflectionFunctor_obj` followed by
`TauCeti.reflectRep_obj_of_ne`, which is the transport in the statement. -/
@[simp]
theorem reflectionFunctor_map_app_of_ne
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSink i)
    {j : Q} (hj : j ≠ i) :
    ((reflectionFunctor i hi).map η).app j =
      eqToHom ((congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj j)
          (reflectionFunctor_obj i hi M)).trans (reflectRep_obj_of_ne M hi hj)) ≫ η.app j ≫
        eqToHom ((congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj j)
          (reflectionFunctor_obj i hi N)).trans (reflectRep_obj_of_ne N hi hj)).symm := by
  have hM : (congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj j)
      (reflectionFunctor_obj i hi M)).trans (reflectRep_obj_of_ne M hi hj)
      = reflectRep_obj_of_ne M hi hj := Subsingleton.elim _ _
  have hN : (congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj j)
      (reflectionFunctor_obj i hi N)).trans (reflectRep_obj_of_ne N hi hj)
      = reflectRep_obj_of_ne N hi hj := Subsingleton.elim _ _
  rw [hM, hN]
  exact reflectRepMapApp_of_ne η hi hj

end ReflectRep

/-! ### The dimension vector of the reflection -/

section DimVector

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]
variable (M : QuiverRep.{u, v, w, max v w x} k Q) {i : Q} (hi : IsSink i)

/-- Away from the reflected vertex the dimension vector is unchanged. -/
@[simp]
theorem dimVector_reflectRep_of_ne {j : Q} (h : j ≠ i) :
    dimVector (reflectRep M hi) j = dimVector M j := by
  rw [dimVector_apply (M := reflectRep M hi) (i := j), dimVector_apply]
  exact congrArg (fun X : ModuleCat.{max v w x} k ↦ Module.finrank k X)
    (reflectRep_obj_of_ne M hi h)

/-- **The dimension of the reflected space at the sink.** When the sum of the arrows into `i` is
onto, rank-nullity turns the kernel that the reflection puts at `i` into the arrow count
`∑_b #(b ⟶ i) · dim M_b` less the old dimension at `i`. Only the vertex spaces at the sources of
arrows into `i` need be assumed finite-dimensional; surjectivity exhibits `Mᵢ` as a quotient of
the resulting finite-dimensional domain. -/
theorem dimVector_reflectRep_self_add
    (hM : ∀ e : Σ b : Q, (b ⟶ i), FiniteDimensional k (M.obj e.1))
    (hs : Function.Surjective (incomingSum M i)) :
    dimVector (reflectRep M hi) i + dimVector M i
      = ∑ b : Q, Fintype.card (b ⟶ i) * dimVector M b := by
  have hker : dimVector (reflectRep M hi) i
      = Module.finrank k (LinearMap.ker (incomingSum M i)) := by
    rw [dimVector_apply (M := reflectRep M hi) (i := i)]
    exact congrArg (fun X : ModuleCat.{max v w x} k ↦ Module.finrank k X)
      (reflectRep_obj_self M hi)
  have hrange : Module.finrank k (LinearMap.range (incomingSum M i)) = dimVector M i := by
    rw [LinearMap.range_eq_top.mpr hs, dimVector_apply]
    exact finrank_top _ _
  have hsum := LinearMap.finrank_range_add_finrank_ker (incomingSum M i)
  rw [hker, hrange.symm, add_comm, hsum, finrank_pi_incoming M i hM]
  exact Finset.sum_congr rfl fun b _ ↦ congrArg (Fintype.card (b ⟶ i) * ·)
    (dimVector_apply M b).symm

/-- **The reflection acts on dimension vectors by the simple reflection at the sink.** The
hypothesis is that the sum of the arrows into `i` is onto; it is exactly what makes the kernel at
`i` have the dimension the reflection `sᵢ` predicts, and it fails for the vertex simple `Sᵢ`. As
in `TauCeti.dimVector_reflectRep_self_add`, only the vertex spaces at the sources of arrows into
`i` need be finite-dimensional; away from `i` the dimension vector is unchanged. -/
theorem dimVector_reflectRep [DecidableEq Q]
    (hM : ∀ e : Σ b : Q, (b ⟶ i), FiniteDimensional k (M.obj e.1))
    (hs : Function.Surjective (incomingSum M i)) :
    (fun j : Q ↦ (dimVector (reflectRep M hi) j : ℤ))
      = vertexPreReflection Q i (fun j ↦ (dimVector M j : ℤ)) := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · have hzero : ∀ v : Q, Fintype.card (j ⟶ v) = 0 := fun v ↦
      Fintype.card_eq_zero_iff.mpr (hi.isEmpty_hom v)
    rw [vertexPreReflection_apply_self]
    have h := dimVector_reflectRep_self_add M hi hM hs
    have h' : ((dimVector (reflectRep M hi) j : ℤ)) + (dimVector M j : ℤ)
        = ∑ b : Q, ((Fintype.card (b ⟶ j) : ℤ) * (dimVector M b : ℤ)) := by
      exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℤ)) h
    have hsimp : ∑ v : Q, ((Fintype.card (j ⟶ v) : ℤ) + (Fintype.card (v ⟶ j) : ℤ))
          * (dimVector M v : ℤ)
        = ∑ v : Q, (Fintype.card (v ⟶ j) : ℤ) * (dimVector M v : ℤ) :=
      Finset.sum_congr rfl fun v _ ↦ by simp [hzero v]
    rw [hsimp]
    linarith [h']
  · rw [vertexPreReflection_apply_of_ne Q i _ hj, dimVector_reflectRep_of_ne M hi hj]

end DimVector

/-! ### The boundary case: a representation concentrated at the sink -/

section Concentrated

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]
variable (M : QuiverRep.{u, v, w, max v w x} k Q)

/-- If every vertex space at the source of an arrow into `i` vanishes, then the sum of the arrows
into `i` is the zero map. -/
theorem incomingSum_eq_zero (i : Q) (h : ∀ b : Q, (b ⟶ i) → Subsingleton (M.obj b)) :
    incomingSum M i = 0 := by
  ext f
  rw [incomingSum_apply]
  refine Finset.sum_eq_zero fun e _ ↦ ?_
  have := h e.1 e.2
  rw [Subsingleton.elim (f e) 0, map_zero]

/-- **The sum of the arrows into `i` need not be onto.** It fails to be whenever every vertex
space at the source of an arrow into `i` vanishes while the space at `i` does not, which is what
the vertex simple `Sᵢ` does at a sink: no arrow into a sink is a loop, so `Sᵢ` vanishes at every
source of such an arrow. This is why the surjectivity hypothesis of
`TauCeti.dimVector_reflectRep` cannot be dropped. -/
theorem incomingSum_not_surjective (i : Q) (h : ∀ b : Q, (b ⟶ i) → Subsingleton (M.obj b))
    (hne : Nontrivial (M.obj i)) : ¬ Function.Surjective (incomingSum M i) := by
  have := hne
  obtain ⟨y, hy⟩ := exists_ne (0 : M.obj i)
  intro hs
  obtain ⟨f, hf⟩ := hs y
  rw [incomingSum_eq_zero M i h] at hf
  exact hy hf.symm

/-- **The reflected space at the sink vanishes when all incoming sources vanish.** If every vertex
space at the source of an arrow into `i` vanishes, then the reflected space at `i` vanishes too.
In particular, this is the sink-vertex computation showing that reflection annihilates the vertex
simple `Sᵢ`. -/
theorem subsingleton_reflectRep_obj_self {i : Q} (hi : IsSink i)
    (h : ∀ b : Q, (b ⟶ i) → Subsingleton (M.obj b)) :
    Subsingleton ((reflectRep M hi).obj i) := by
  -- The domain of `TauCeti.incomingSum` is a product of the vanishing spaces, hence vanishes,
  -- and the kernel is a subtype of it.
  have hdom : Subsingleton ((e : Σ b : Q, (b ⟶ i)) → M.obj e.1) :=
    have : ∀ e : Σ b : Q, (b ⟶ i), Subsingleton (M.obj e.1) := fun e ↦ h e.1 e.2
    inferInstance
  have hker : Subsingleton (LinearMap.ker (incomingSum M i)) :=
    ⟨fun a b ↦ Subtype.ext (hdom.elim _ _)⟩
  exact reflectRep_obj_self M hi ▸ hker

/-- If every source of an arrow into the sink vanishes, the reflected dimension at the sink is
zero. -/
theorem dimVector_reflectRep_self_eq_zero {i : Q} (hi : IsSink i)
    (h : ∀ b : Q, (b ⟶ i) → Subsingleton (M.obj b)) :
    dimVector (reflectRep M hi) i = 0 := by
  rw [dimVector_apply (M := reflectRep M hi) (i := i)]
  let : Subsingleton ((reflectRep M hi).obj ((Paths.of (Reflect Q i)).obj i)) :=
    subsingleton_reflectRep_obj_self M hi h
  exact Module.finrank_zero_of_subsingleton (R := k)

end Concentrated

end TauCeti
