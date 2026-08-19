/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.Indecomposable
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# The reflection functor is fully faithful where the incoming sum is onto

The Bernstein-Gelfand-Ponomarev reflection `C⁺ᵢ` at a sink `i` replaces the vertex space `Mᵢ` by
the kernel of the sum `TauCeti.incomingSum` of the arrows into `i`. It annihilates the vertex
simple `Sᵢ`, so it cannot be an equivalence; what it *is*, is fully faithful on the representations
whose incoming sum at `i` is onto. This file proves that: whenever the sum of the arrows into `i`
is onto for `M`, the map `(M ⟶ N) → (C⁺ᵢ M ⟶ C⁺ᵢ N)` supplied by `TauCeti.reflectionFunctor` is a
bijection. Only the source `M` needs the hypothesis; the target `N` is arbitrary.

Surjectivity of the incoming sum is the hypothesis throughout; it is not equivalent to avoiding
`Sᵢ`. It is `TauCeti.incomingSum_surjective_of_indecomposable` that ties the two together, and only
for an *indecomposable* `M`: such an `M` has its incoming sum at `i` onto as soon as it is not
isomorphic to `Sᵢ`. So the vertex simple names the exceptional case only among indecomposables, and
that is the only place below where it is mentioned.

Both halves are elementary once the incoming sum is available. **Faithfulness** is the surjectivity
of that sum: a morphism reflecting to zero has vanishing components away from `i`, hence, by
`TauCeti.incomingSum_naturality`, its component at `i` kills the range of the incoming sum, which
is everything. **Fullness** is the first isomorphism theorem: a morphism `θ` of the reflected
representations carries the kernel at `i` for `M` into the kernel for `N`, so the composite
`⨁_{a : b ⟶ i} M_b → ⨁_{a : b ⟶ i} N_b → Nᵢ` factors through the incoming sum of `M`, and the
resulting map `Mᵢ → Nᵢ` completes the components of `θ` away from `i` to a morphism `M ⟶ N`
reflecting back to `θ`.

The consequence is the second milestone of the reflection-functor route to Gabriel's theorem:
**reflection at a sink preserves indecomposability**. The reflection functor is additive, so a
bijection on endomorphisms matches idempotents with idempotents; an indecomposable `M` other than
`Sᵢ` therefore reflects to an indecomposable representation of the reflected quiver. No
finite-dimensionality is needed for that. It is needed for the other half of the induction step:
`TauCeti.dimVector_reflectRep_of_indecomposable` computes the dimension vector of the reflection as
`sᵢ · dim M` when the vertex spaces at the sources of the arrows into `i` are finite-dimensional.

## Main results

* `TauCeti.reflectionFunctor_map_injective`, `TauCeti.reflectionFunctor_map_surjective` and
  `TauCeti.reflectionFunctor_map_bijective`: **the reflection functor at a sink is fully faithful**
  on the representations whose incoming sum there is onto.
* `TauCeti.indecomposable_reflectRep`: **reflection at a sink preserves indecomposability**, under
  the same hypothesis.
* `TauCeti.indecomposable_reflectRep_of_not_nonempty_iso_simpleRep`: the same statement with the
  hypothesis discharged, for an indecomposable representation other than the vertex simple `Sᵢ`.

## Implementation notes

The reflection functor's object `(reflectionFunctor i hi).obj M` is only *propositionally* equal to
`TauCeti.reflectRep M hi`, because the body of the functor is not exposed outside the module
defining it. The statements below therefore speak of the functor's map, whose type mentions only
the functor, and the vertex spaces of its objects are named by the two private transports
`reflectObj_self` and `reflectObj_of_ne`, which are exactly the composites appearing in
`TauCeti.reflectionFunctor_map_app_self_apply` and `TauCeti.reflectionFunctor_map_app_of_ne`.
Proof irrelevance makes them interchangeable with the transports written inline there.

As in the neighbouring files, a vertex `i : Q` is used both as an object of `CategoryTheory.Paths`
and as a vertex of `TauCeti.Quiver.Reflect Q i`, identifications that hold only by unfolding
semireducible definitions. Goals mentioning both are therefore not type-correct at the transparency
`rw` and `simp` build motives with, so every step that strips a conjugation by `eqToHom` is
factored through `TauCeti.eqToHom_conjugate_cancel` and `TauCeti.eqToHom_conjugate_square`, which
`subst` the object equalities away before doing anything, or through one of the two rearrangements
of them at the top of the file.

The linear section of the incoming sum used to build the preimage exists because a vector space is
projective; the private `sinkSection` is a choice of one. Nothing downstream depends on which
section is chosen: the private `homSink_incomingSum` pins the resulting map on the whole of `Mᵢ`,
and it is the only property of that map the proofs use.

## References

This is the second milestone of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, that the reflection functor
carries an indecomposable other than `Sᵢ` to an indecomposable. See Bernstein--Gelfand--Ponomarev,
*Coxeter functors and Gabriel's theorem*, and Derksen--Weyman, *An Introduction to Quiver
Representations*, Ch. 2.
-/

public section

namespace TauCeti

open CategoryTheory
open _root_.TauCeti.Quiver

universe u v w x

section General

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q] [Fintype Q]
  [∀ a b : Q, Fintype (a ⟶ b)]
variable {M N : QuiverRep.{u, v, w, max v w x} k Q} {i : Q}

/-! ### Stripping conjugations by `eqToHom`

The two helpers below only move conjugations by `eqToHom` from one pair of edges to another; each
is a rearrangement of `TauCeti.eqToHom_conjugate_cancel`, respectively of
`TauCeti.eqToHom_conjugate_square`, from
`TauCeti.RepresentationTheory.Quiver.Reflection.Representation`, and is proved from it rather than
by unfolding transports again. Like those, they are stated for an abstract category, where a vertex
is not simultaneously an object of `CategoryTheory.Paths` and a vertex of the reflected quiver;
that is what makes them usable on goals where it is. -/

/-- Two morphisms conjugated to the same morphism are equal: conjugating back cancels, by
`TauCeti.eqToHom_conjugate_cancel`, on both sides at once. -/
private theorem eq_of_eqToHom_conj {C : Type*} [Category* C] {X X' Y Y' : C} (hX : X' = X)
    (hY : Y = Y') {f g : X ⟶ Y}
    (h : eqToHom hX ≫ f ≫ eqToHom hY = eqToHom hX ≫ g ≫ eqToHom hY) : f = g :=
  (eqToHom_conjugate_cancel hX hY.symm f).symm.trans
    ((congrArg (fun u : X' ⟶ Y' ↦ eqToHom hX.symm ≫ u ≫ eqToHom hY.symm) h).trans
      (eqToHom_conjugate_cancel hX hY.symm g))

/-- A commuting square whose two horizontal edges are conjugates commutes after the conjugations
are moved onto the vertical edges. This is `TauCeti.eqToHom_conjugate_square` for the square whose
vertical edges are the conjugated ones, whose horizontal edges are then conjugated twice and so, by
`TauCeti.eqToHom_conjugate_cancel`, are the given ones. -/
private theorem eqToHom_strip_square {C : Type*} [Category* C]
    {A A' B B' D D' E E' : C} (hA : A = A') (hB : B = B') (hD : D = D') (hE : E = E')
    (p : A' ⟶ B') (q : E' ⟶ D') (f : B ⟶ D) (g : A ⟶ E)
    (h : (eqToHom hA ≫ p ≫ eqToHom hB.symm) ≫ f = g ≫ eqToHom hE ≫ q ≫ eqToHom hD.symm) :
    p ≫ (eqToHom hB.symm ≫ f ≫ eqToHom hD) = (eqToHom hA.symm ≫ g ≫ eqToHom hE) ≫ q :=
  (eqToHom_conjugate_square hA hB hD hE p _ _ q).mp (by simpa using h)

/-! ### Faithfulness -/

/-- **The reflection functor at a sink is faithful** on the representations whose incoming sum
there is onto. Two morphisms with the same reflection agree away from the sink, because reflection
leaves those components alone; at the sink they then agree on the range of the incoming sum, by
`TauCeti.incomingSum_naturality`, and that range is everything. -/
theorem reflectionFunctor_map_injective (hi : IsSink i)
    (hs : Function.Surjective (incomingSum M i)) :
    Function.Injective fun η : M ⟶ N ↦ (reflectionFunctor i hi).map η := by
  intro η η' h
  have haway : ∀ j : Q, j ≠ i → η.app j = η'.app j := by
    intro j hj
    have h1 := congrArg (fun α : (reflectionFunctor i hi).obj M ⟶ (reflectionFunctor i hi).obj N ↦
      α.app j) h
    simp only at h1
    rw [reflectionFunctor_map_app_of_ne η hi hj, reflectionFunctor_map_app_of_ne η' hi hj] at h1
    exact eq_of_eqToHom_conj _ _ h1
  refine NatTrans.ext (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj
  · refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
    obtain ⟨f, rfl⟩ := hs y
    rw [(incomingSum_naturality η j f).symm, (incomingSum_naturality η' j f).symm]
    exact congrArg (incomingSum N j) (funext fun e ↦
      congrArg (fun g : M.obj e.1 ⟶ N.obj e.1 ↦ g (f e)) (haway e.1 (hi.ne_of_hom e.2)))
  · exact haway j hj

/-! ### Fullness

A morphism `θ` of reflected representations is taken apart into its components away from the sink
and the map it induces between the two kernels there, and those pieces are reassembled into a
morphism of the original representations. -/

variable (M) in
/-- The vertex space of a reflected representation at the sink, named through the functor. This is
the transport appearing in `TauCeti.reflectionFunctor_map_app_self_apply`. -/
private theorem reflectObj_self (hi : IsSink i) :
    ((reflectionFunctor i hi).obj M).obj i
      = ModuleCat.of k (LinearMap.ker (incomingSum M i)) :=
  (congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj i) (reflectionFunctor_obj i hi M)).trans
    (reflectRep_obj_self M hi)

variable (M) in
/-- The vertex spaces of a reflected representation away from the sink, named through the functor.
This is the transport appearing in `TauCeti.reflectionFunctor_map_app_of_ne`. -/
private theorem reflectObj_of_ne (hi : IsSink i) {j : Q} (hj : j ≠ i) :
    ((reflectionFunctor i hi).obj M).obj j = M.obj j :=
  (congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj j) (reflectionFunctor_obj i hi M)).trans
    (reflectRep_obj_of_ne M hi hj)

variable {hi : IsSink i}
  (θ : (reflectionFunctor i hi).obj M ⟶ (reflectionFunctor i hi).obj N)

/-- The component of `θ` at a vertex other than the sink, read back as a map of the original
vertex spaces. -/
private noncomputable def homAway {j : Q} (hj : j ≠ i) : M.obj j ⟶ N.obj j :=
  eqToHom (reflectObj_of_ne M hi hj).symm ≫ θ.app j ≫ eqToHom (reflectObj_of_ne N hi hj)

/-- The component of `θ` at the sink, read back as a map between the two kernels. -/
private noncomputable def homKer :
    LinearMap.ker (incomingSum M i) →ₗ[k] LinearMap.ker (incomingSum N i) :=
  (eqToHom (reflectObj_self M hi).symm ≫ θ.app i ≫ eqToHom (reflectObj_self N hi)).hom

variable (M) in
/-- A reversed arrow acts on a reflected representation, named through the functor, by the matching
coordinate projection out of the kernel at the sink. -/
private theorem functorObj_map_reflectArrow (hi : IsSink i) {b : Q} (ε : b ⟶ i) :
    ((reflectionFunctor i hi).obj M).map (reflectArrow i ε).toPath
      = eqToHom (reflectObj_self M hi) ≫
        ModuleCat.ofHom ((LinearMap.proj (⟨b, ε⟩ : Σ b : Q, (b ⟶ i))).comp
          (LinearMap.ker (incomingSum M i)).subtype) ≫
        eqToHom (reflectObj_of_ne M hi (hi.ne_of_hom ε)).symm := by
  rw [Functor.congr_hom (reflectionFunctor_obj i hi M) (reflectArrow i ε).toPath,
    reflectRep_map_reflectArrow M hi ε]
  simp

variable (M) in
/-- An arrow away from the sink acts on a reflected representation, named through the functor, as
it does on the original one. -/
private theorem functorObj_map_reflectArrowOfNeOfNe (hi : IsSink i) {a b : Q} (ha : a ≠ i)
    (hb : b ≠ i) (e : a ⟶ b) :
    ((reflectionFunctor i hi).obj M).map (reflectArrowOfNeOfNe ha hb e).toPath
      = eqToHom (reflectObj_of_ne M hi ha) ≫ M.map e.toPath ≫
        eqToHom (reflectObj_of_ne M hi hb).symm := by
  rw [Functor.congr_hom (reflectionFunctor_obj i hi M) (reflectArrowOfNeOfNe ha hb e).toPath,
    reflectRep_map_reflectArrowOfNeOfNe M hi ha hb e]
  simp

/-- **The pieces of `θ` fit together coordinatewise.** Naturality of `θ` along the reversed arrow
`e` says that the map it induces between the kernels is, in the coordinate `e`, the component of
`θ` at the source of `e`. -/
private theorem homKer_coe_apply (f : LinearMap.ker (incomingSum M i))
    (e : Σ b : Q, (b ⟶ i)) :
    (homKer θ f).1 e = homAway θ (hi.ne_of_hom e.2) (f.1 e) := by
  have hnat := θ.naturality (reflectArrow i e.2).toPath
  rw [functorObj_map_reflectArrow M hi e.2, functorObj_map_reflectArrow N hi e.2] at hnat
  have hstrip := eqToHom_strip_square (reflectObj_self M hi)
    (reflectObj_of_ne M hi (hi.ne_of_hom e.2)) (reflectObj_of_ne N hi (hi.ne_of_hom e.2))
    (reflectObj_self N hi) _ _ (θ.app e.1) (θ.app i) hnat
  exact (congrArg (fun g : ModuleCat.of k (LinearMap.ker (incomingSum M i)) ⟶ N.obj e.1 ↦ g f)
    hstrip).symm

/-- The components of `θ` away from the sink, assembled into a map between the sources of the two
incoming sums. -/
private noncomputable def homPi :
    ((e : Σ b : Q, (b ⟶ i)) → M.obj e.1) →ₗ[k] ((e : Σ b : Q, (b ⟶ i)) → N.obj e.1) where
  toFun f e := homAway θ (hi.ne_of_hom e.2) (f e)
  map_add' f g := by ext e; simp
  map_smul' r f := by ext e; simp

private theorem homPi_apply (f : (e : Σ b : Q, (b ⟶ i)) → M.obj e.1) (e : Σ b : Q, (b ⟶ i)) :
    homPi θ f e = homAway θ (hi.ne_of_hom e.2) (f e) := rfl

/-- On the kernel of the incoming sum of `M`, `homPi` is the map between the kernels, so in
particular it lands in the kernel of the incoming sum of `N`. -/
private theorem homPi_coe (f : LinearMap.ker (incomingSum M i)) :
    homPi θ f.1 = (homKer θ f).1 :=
  funext fun e ↦ (homKer_coe_apply θ f e).symm

/-- A linear section of the incoming sum, chosen once; a vector space is projective, so a
surjection onto it splits. -/
private noncomputable def sinkSection (hs : Function.Surjective (incomingSum M i)) :
    M.obj i →ₗ[k] ((e : Σ b : Q, (b ⟶ i)) → M.obj e.1) :=
  ((incomingSum M i).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hs)).choose

private theorem incomingSum_sinkSection (hs : Function.Surjective (incomingSum M i))
    (y : M.obj i) : incomingSum M i (sinkSection hs y) = y :=
  DFunLike.congr_fun
    ((incomingSum M i).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hs)).choose_spec y

/-- **The component at the sink of the preimage of `θ`.** It is the map `Mᵢ → Nᵢ` through which
`homPi` followed by the incoming sum of `N` factors, built from a section of the incoming sum of
`M`. -/
private noncomputable def homSink (hs : Function.Surjective (incomingSum M i)) :
    M.obj i →ₗ[k] N.obj i :=
  (incomingSum N i).comp ((homPi θ).comp (sinkSection hs))

/-- **The defining property of `homSink`**, independent of the chosen section: the square formed by
the two incoming sums and `homPi` commutes. -/
private theorem homSink_incomingSum (hs : Function.Surjective (incomingSum M i))
    (f : (e : Σ b : Q, (b ⟶ i)) → M.obj e.1) :
    homSink θ hs (incomingSum M i f) = incomingSum N i (homPi θ f) := by
  set g := sinkSection hs (incomingSum M i f) with hgdef
  have hmem : g - f ∈ LinearMap.ker (incomingSum M i) := by
    rw [LinearMap.mem_ker, map_sub, hgdef, incomingSum_sinkSection, sub_self]
  have h0 : incomingSum N i (homPi θ (g - f)) = 0 := by
    rw [homPi_coe θ ⟨g - f, hmem⟩]
    exact (homKer θ ⟨g - f, hmem⟩).2
  have hsub : incomingSum N i (homPi θ g) - incomingSum N i (homPi θ f) = 0 := by
    rw [← map_sub, ← map_sub]
    exact h0
  exact sub_eq_zero.mp hsub

open scoped Classical in
/-- The vertex components of the preimage of `θ`: the component of `θ` away from the sink, and
`homSink` at the sink. -/
private noncomputable def homPreimageApp (hs : Function.Surjective (incomingSum M i)) (j : Q) :
    M.obj j ⟶ N.obj j :=
  if hj : j = i then
    eqToHom (by rw [hj]) ≫ ModuleCat.ofHom (homSink θ hs) ≫ eqToHom (by rw [hj])
  else homAway θ hj

private theorem homPreimageApp_self (hs : Function.Surjective (incomingSum M i)) :
    homPreimageApp θ hs i = ModuleCat.ofHom (homSink θ hs) := by
  classical
  simp only [homPreimageApp, dite_eq_left rfl, eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem homPreimageApp_of_ne (hs : Function.Surjective (incomingSum M i)) {j : Q}
    (hj : j ≠ i) : homPreimageApp θ hs j = homAway θ hj := by
  classical
  simp only [homPreimageApp, dite_eq_right hj]

/-- The vertex components of the preimage of `θ` are natural along every arrow of `Q`. An arrow
into the sink is the case that uses `TauCeti.homSink_incomingSum`, on the family supported at that
one arrow; no arrow leaves a sink, so the remaining case is an arrow between two vertices other
than the sink, where naturality is that of `θ` itself. -/
private theorem homPreimageApp_naturality (hs : Function.Surjective (incomingSum M i))
    {a b : Q} (e : a ⟶ b) :
    M.map e.toPath ≫ homPreimageApp θ hs b = homPreimageApp θ hs a ≫ N.map e.toPath := by
  rcases eq_or_ne a i with rfl | ha
  · exact (hi.isEmpty_hom b).elim e
  rw [homPreimageApp_of_ne θ hs ha]
  rcases eq_or_ne b i with rfl | hb
  · rw [homPreimageApp_self]
    refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
    classical
    have hpi : homPi θ (Pi.single (⟨a, e⟩ : Σ c : Q, (c ⟶ b)) y)
        = Pi.single (⟨a, e⟩ : Σ c : Q, (c ⟶ b)) (homAway θ ha y) := by
      funext c
      by_cases hc : c = ⟨a, e⟩
      · subst hc
        rw [homPi_apply, Pi.single_eq_same, Pi.single_eq_same]
      · rw [homPi_apply, Pi.single_eq_of_ne hc, Pi.single_eq_of_ne hc, map_zero]
    have hkey := homSink_incomingSum θ hs (Pi.single (⟨a, e⟩ : Σ c : Q, (c ⟶ b)) y)
    rwa [incomingSum_single M e y, hpi, incomingSum_single N e (homAway θ ha y)] at hkey
  · rw [homPreimageApp_of_ne θ hs hb]
    have hnat := θ.naturality (reflectArrowOfNeOfNe ha hb e).toPath
    rw [functorObj_map_reflectArrowOfNeOfNe M hi ha hb e,
      functorObj_map_reflectArrowOfNeOfNe N hi ha hb e] at hnat
    exact eqToHom_strip_square (reflectObj_of_ne M hi ha) (reflectObj_of_ne M hi hb)
      (reflectObj_of_ne N hi hb) (reflectObj_of_ne N hi ha) _ _ (θ.app b) (θ.app a) hnat

/-- **The preimage of `θ` under reflection.** -/
private noncomputable def homPreimage (hs : Function.Surjective (incomingSum M i)) : M ⟶ N :=
  Paths.liftNatTrans (homPreimageApp θ hs) fun e ↦ homPreimageApp_naturality θ hs e

private theorem homPreimage_app (hs : Function.Surjective (incomingSum M i)) (j : Q) :
    (homPreimage θ hs).app j = homPreimageApp θ hs j := rfl

/-- The preimage does reflect to `θ`: away from the sink both are the same component of `θ`
conjugated back and forth, and at the sink both are the coordinatewise map between the kernels. -/
private theorem reflectionFunctor_map_homPreimage (hs : Function.Surjective (incomingSum M i)) :
    (reflectionFunctor i hi).map (homPreimage θ hs) = θ := by
  refine NatTrans.ext (funext fun j ↦ ?_)
  by_cases hj : j = i
  · subst j
    refine eq_of_eqToHom_conj (reflectObj_self M hi).symm (reflectObj_self N hi) ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ Subtype.ext (funext fun e ↦ ?_))
    rw [reflectionFunctor_map_app_self_apply (homPreimage θ hs) hi f e,
      homPreimage_app, homPreimageApp_of_ne θ hs (hi.ne_of_hom e.2)]
    exact (homKer_coe_apply θ f e).symm
  · have happ : (homPreimage θ hs).app j
        = eqToHom (reflectObj_of_ne M hi hj).symm ≫ θ.app j ≫
          eqToHom (reflectObj_of_ne N hi hj) := homPreimageApp_of_ne θ hs hj
    refine (reflectionFunctor_map_app_of_ne (homPreimage θ hs) hi hj).trans ?_
    exact (congrArg (fun g : M.obj j ⟶ N.obj j ↦ eqToHom (reflectObj_of_ne M hi hj) ≫ g ≫
      eqToHom (reflectObj_of_ne N hi hj).symm) happ).trans
      (eqToHom_conjugate_cancel (reflectObj_of_ne M hi hj).symm (reflectObj_of_ne N hi hj).symm
        (θ.app j))

/-! ### Full faithfulness, and indecomposability -/

variable (hi)

/-- **The reflection functor at a sink is full** on the representations whose incoming sum there is
onto. -/
theorem reflectionFunctor_map_surjective (hs : Function.Surjective (incomingSum M i)) :
    Function.Surjective fun η : M ⟶ N ↦ (reflectionFunctor i hi).map η :=
  fun θ ↦ ⟨homPreimage θ hs, reflectionFunctor_map_homPreimage θ hs⟩

/-- **The reflection functor at a sink is fully faithful** on the representations whose incoming
sum there is onto, a class that by `TauCeti.incomingSum_surjective_of_indecomposable` contains
every indecomposable representation other than the vertex simple `Sᵢ`. -/
theorem reflectionFunctor_map_bijective (hs : Function.Surjective (incomingSum M i)) :
    Function.Bijective fun η : M ⟶ N ↦ (reflectionFunctor i hi).map η :=
  ⟨reflectionFunctor_map_injective hi hs, reflectionFunctor_map_surjective hi hs⟩

/-- **Reflection at a sink preserves indecomposability**, as soon as the sum of the arrows into the
sink is onto. Reflection is additive and bijective on the endomorphisms of `M`, so it matches the
idempotents of `M` with those of its reflection; an indecomposable has only the trivial ones, and
the reflection of the identity is the identity while the reflection of `0` is `0`. -/
theorem indecomposable_reflectRep (hM : Indecomposable M)
    (hs : Function.Surjective (incomingSum M i)) : Indecomposable (reflectRep M hi) := by
  have hbij := reflectionFunctor_map_bijective (N := M) hi hs
  have hzero : (reflectionFunctor i hi).map (0 : M ⟶ M) = 0 :=
    CategoryTheory.Functor.map_zero (reflectionFunctor i hi) M M
  refine reflectionFunctor_obj i hi M ▸ indecomposable_of_idempotent_eq_zero_or_id ?_ ?_
  · intro h0
    have h1 : (reflectionFunctor i hi).map (𝟙 M) = (reflectionFunctor i hi).map (0 : M ⟶ M) :=
      ((reflectionFunctor i hi).map_id M).trans
        (((Limits.IsZero.iff_id_eq_zero _).mp h0).trans hzero.symm)
    exact hM.1 ((Limits.IsZero.iff_id_eq_zero M).mpr (hbij.1 h1))
  · intro e he
    obtain ⟨η, rfl⟩ := hbij.2 e
    have hidem : η ≫ η = η := hbij.1 (((reflectionFunctor i hi).map_comp η η).trans he)
    rcases idempotent_eq_zero_or_id_of_indecomposable hM hidem with h | h
    · exact Or.inl (by rw [h]; exact hzero)
    · exact Or.inr (by rw [h]; exact (reflectionFunctor i hi).map_id M)

end General

/-! ### The vertex simple as the exceptional case

As in `TauCeti.RepresentationTheory.Quiver.Reflection.Indecomposable`, a statement naming both a
reflected representation and the vertex simple has to put the quiver, its arrows and the field in
one universe. -/

section VertexSimple

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u} Q] [Fintype Q]
  [∀ a b : Q, Fintype (a ⟶ b)]
variable {M : QuiverRep.{u, u, u, u} k Q} {i : Q}

/-- **Reflection at a sink carries an indecomposable representation other than the vertex simple
there to an indecomposable representation of the reflected quiver.** The vertex simple `Sᵢ` is
genuinely excluded: reflection sends it to the zero representation, by
`TauCeti.subsingleton_reflectRep_obj_self`. Together with
`TauCeti.dimVector_reflectRep_of_indecomposable`, which computes the dimension vector of the result
as `sᵢ · dim M` under the additional hypothesis that the vertex spaces at the sources of the arrows
into `i` are finite-dimensional, this is the inductive step of the reflection-functor proof of
Gabriel's theorem. -/
theorem indecomposable_reflectRep_of_not_nonempty_iso_simpleRep (hi : IsSink i)
    (hM : Indecomposable M) (hne : ¬ Nonempty (M ≅ simpleRep k Q i)) :
    Indecomposable (reflectRep M hi) :=
  indecomposable_reflectRep hi hM (incomingSum_surjective_of_indecomposable hi hM hne)

end VertexSimple

end TauCeti
