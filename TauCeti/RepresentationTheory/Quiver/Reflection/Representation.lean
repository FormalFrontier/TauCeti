/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.Basic
public import TauCeti.RepresentationTheory.Quiver.Reflection.DimensionVector
public import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Reflecting a representation at a sink

For a sink `i` of a quiver `Q` -- a vertex no arrow leaves -- the Bernstein-Gelfand-Ponomarev
construction turns a representation `M` of `Q` into a representation of the reflected quiver
`TauCeti.Quiver.Reflect Q i`, in which every arrow at `i` points the other way. Away from `i`
nothing changes; at `i` the vector space `Mᵢ` is replaced by the kernel of the map

`⨁_{a : b ⟶ i} M_b → Mᵢ`

that sums the actions of the arrows into `i`, and each reversed arrow acts by the corresponding
coordinate projection out of that kernel. This file builds that representation and computes its
dimension vector.

The content of the computation is that on dimension vectors the construction realizes the simple
reflection `sᵢ` of `TauCeti.RepresentationTheory.Quiver.Reflection.DimensionVector`, provided the
summing map is surjective: the reflected space at `i` then has dimension
`∑_b #(b ⟶ i) · dim M_b - dim Mᵢ`, which is exactly `sᵢ` applied to the dimension vector of `M`,
because a sink has no outgoing arrow. Surjectivity is the honest hypothesis here and it is not
automatic: it fails exactly the way `TauCeti.incomingSum_not_surjective` records, for a
representation concentrated at `i`, of which the vertex simple `Sᵢ` is the example. The reflection
kills such a representation, by `TauCeti.subsingleton_reflectRep_obj_self`.

## Main definitions

* `TauCeti.incomingSum`: the map `⨁_{a : b ⟶ i} M_b → Mᵢ` summing the arrows into a vertex,
  defined at every vertex of every representation.
* `TauCeti.reflectRep`: the reflection `C⁺ᵢ M` of a representation at a sink `i`, a
  representation of `TauCeti.Quiver.Reflect Q i`.

## Main results

* `TauCeti.reflectRep_obj_self` and `TauCeti.reflectRep_obj_of_ne`: the vertex spaces of `C⁺ᵢ M`.
* `TauCeti.reflectRep_map_reflectArrow` and `TauCeti.reflectRep_map_reflectArrowOfNe`: the action
  of a reversed arrow, by a coordinate projection out of the kernel, and of an arrow away from `i`,
  unchanged.
* `TauCeti.dimVector_reflectRep_of_ne` and `TauCeti.dimVector_reflectRep_self_add`: the dimension
  vector of `C⁺ᵢ M`, away from `i` and at `i`.
* `TauCeti.dimVector_reflectRep`: `dim (C⁺ᵢ M) = sᵢ (dim M)` when the summing map is surjective.
* `TauCeti.incomingSum_not_surjective`: that surjectivity fails for a representation concentrated
  at `i`, and `TauCeti.subsingleton_reflectRep_obj_self`: the reflection kills such a
  representation. Together they are the vertex simple `Sᵢ`, the boundary case of the previous
  result.

## Implementation notes

The vertex spaces branch on equality with `i`, so they are written with an `if` and decided
classically; no `DecidableEq Q` instance therefore appears in the interface of the construction,
exactly as for `TauCeti.simpleRep`. Only the statements naming `TauCeti.vertexPreReflection` assume
`DecidableEq Q`, because `Pi.single` needs one.

The vertex spaces and the prefunctor that `TauCeti.reflectRep` lifts are private, and
`TauCeti.reflectRep` does not expose its body: the `reflectRep_obj_*` and `reflectRep_map_*`
theorems are the whole interface, and they are what downstream files should use.

The arrows of `TauCeti.Quiver.Reflect Q i` are given by `TauCeti.Quiver.reflectHom`, which is
again an `if` on equality with `i`, so an arrow of the reflected quiver is a *cast* of an arrow of
`Q`: `TauCeti.Quiver.reflectArrow` and `TauCeti.Quiver.reflectArrowOfNe` name the two casts, and
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
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`; functoriality in `M` is not
proved here. See Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's theorem*, and
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

/-- **The sum of the arrows into a vertex.** For a representation `M` of a finite quiver and a
vertex `i`, this is the linear map `⨁_{a : b ⟶ i} M_b → Mᵢ` sending a family of vectors, indexed
by the arrows into `i`, to the sum of their images under the corresponding arrows. Its kernel is
the vector space that `TauCeti.reflectRep` puts at `i`.

No hypothesis on `i` is imposed: the map is defined at every vertex, and it is the reflection that
needs `i` to be a sink. -/
noncomputable def incomingSum (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q) :
    ((e : Σ b : Q, (b ⟶ i)) → M.obj e.1) →ₗ[k] M.obj i :=
  ∑ e : Σ b : Q, (b ⟶ i), (M.map e.2.toPath).hom ∘ₗ LinearMap.proj e

@[simp]
theorem incomingSum_apply (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q)
    (f : (e : Σ b : Q, (b ⟶ i)) → M.obj e.1) :
    incomingSum M i f = ∑ e : Σ b : Q, (b ⟶ i), (M.map e.2.toPath).hom (f e) := by
  simp [incomingSum]

/-- The source of `TauCeti.incomingSum` has dimension `∑_b #(b ⟶ i) · dim M_b`. Only the vertex
spaces at the sources of arrows into `i` need be finite-dimensional; they are the only ones the
domain is built from. -/
theorem finrank_forall_incoming (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q)
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
  if_pos rfl

/-- Away from the reflected vertex the vertex spaces are those of `M`. -/
private theorem reflectRepObj_of_ne (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q) {j : Q}
    (h : j ≠ i) : reflectRepObj M i j = M.obj j :=
  if_neg h

open scoped Classical in
/-- The prefunctor underlying the reflection at a sink: the vertex spaces of `reflectRepObj`,
together with the action of a single arrow of the reflected quiver. A reversed arrow acts by the
matching coordinate projection out of the kernel at `i`; every other arrow acts as it does in `M`.

At a sink the reflected quiver has no arrow into `i` and no loop at `i`, so those two branches are
impossible and are discharged from the hypothesis.

An implementation helper for `TauCeti.reflectRep`, whose action is described by
`TauCeti.reflectRep_map_reflectArrow` and `TauCeti.reflectRep_map_reflectArrowOfNe`. -/
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
    (dif_neg (hi.ne_of_hom e))).trans ?_
  refine (dif_pos rfl).trans ?_
  conv_lhs => rw [cast_reflectArrow]
  rfl

/-- **An arrow away from the reflected vertex acts unchanged.** -/
@[simp]
theorem reflectRep_map_reflectArrowOfNe {a b : Q} (ha : a ≠ i) (hb : b ≠ i) (e : a ⟶ b) :
    (reflectRep M hi).map (reflectArrowOfNe ha hb e).toPath
      = eqToHom (reflectRep_obj_of_ne M hi ha) ≫ M.map e.toPath ≫
        eqToHom (reflectRep_obj_of_ne M hi hb).symm := by
  classical
  refine ((reflectRep_map_toPath (a := a) (b := b) M hi
    (reflectArrowOfNe ha hb e)).trans (dif_neg hb)).trans ?_
  refine (dif_neg ha).trans ?_
  conv_lhs => rw [cast_reflectArrowOfNe]
  rfl

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
  rw [hker, hrange.symm, add_comm, hsum, finrank_forall_incoming M i hM]
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

/-- **The reflection kills a representation concentrated at the sink.** If every vertex space at
the source of an arrow into `i` vanishes then the reflected space at `i` vanishes too; combined
with `TauCeti.dimVector_reflectRep_of_ne` this says that the reflection annihilates the vertex
simple `Sᵢ`. -/
theorem subsingleton_reflectRep_obj_self {i : Q} (hi : IsSink i)
    (h : ∀ b : Q, (b ⟶ i) → Subsingleton (M.obj b)) :
    Subsingleton ((reflectRep M hi).obj i) := by
  have hdom : ∀ e : Σ b : Q, (b ⟶ i), Subsingleton (M.obj e.1) := fun e ↦ h e.1 e.2
  have hker : Subsingleton (LinearMap.ker (incomingSum M i)) :=
    ⟨fun a b ↦ Subtype.ext (Subsingleton.elim _ _)⟩
  exact reflectRep_obj_self M hi ▸ hker

/-- The dimension vector of the reflection of a representation concentrated at the sink vanishes
at the sink. -/
theorem dimVector_reflectRep_self_eq_zero {i : Q} (hi : IsSink i)
    (h : ∀ b : Q, (b ⟶ i) → Subsingleton (M.obj b)) :
    dimVector (reflectRep M hi) i = 0 := by
  rw [dimVector_apply (M := reflectRep M hi) (i := i)]
  let : Subsingleton ((reflectRep M hi).obj ((Paths.of (Reflect Q i)).obj i)) :=
    subsingleton_reflectRep_obj_self M hi h
  exact Module.finrank_zero_of_subsingleton (R := k)

end Concentrated

end TauCeti
