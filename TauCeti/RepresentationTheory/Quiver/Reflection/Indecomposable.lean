/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.LinearAlgebra.Projection
public import TauCeti.CategoryTheory.Preadditive.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.Reflection.Representation
public import TauCeti.RepresentationTheory.Quiver.Representation.Simple

/-!
# Reflecting an indecomposable representation at a sink

The Bernstein-Gelfand-Ponomarev reflection at a sink `i` replaces the vertex space `Mᵢ` by the
kernel of the sum `TauCeti.incomingSum` of the arrows into `i`, and it acts on dimension vectors by
the simple reflection `sᵢ` whenever that sum is onto (`TauCeti.dimVector_reflectRep`). This file
discharges that hypothesis: the sum of the arrows into a sink is onto for every indecomposable
representation except the vertex simple `Sᵢ`, which is the representation the reflection
annihilates.

One construction does the work. No arrow leaves a sink, so a linear endomorphism `π` of `Mᵢ` that
fixes the image of every arrow into `i` extends by the identity at the other vertices to an
endomorphism `TauCeti.sinkEnd` of the whole representation, idempotent as soon as `π` is. The
category of representations is abelian, hence idempotent complete, so an indecomposable object
carries no idempotent endomorphism besides `0` and the identity
(`TauCeti.idempotent_eq_zero_or_id_of_indecomposable`), and therefore `π` itself is `0` or the
identity. Applied to the projection onto the range of the incoming sum along a complement, this
says the range is all of `Mᵢ` unless `M` vanishes away from `i`; applied to the projection onto a
line, it says a representation concentrated at a sink is a line there, hence is `Sᵢ`.

## Main definitions

* `TauCeti.sinkEnd`: the endomorphism of `M` acting by a given endomorphism of `Mᵢ` at a sink `i`
  and by the identity elsewhere, with `TauCeti.sinkEnd_eq_id_iff` and
  `TauCeti.sinkEnd_eq_zero_iff` recognizing when it is trivial.

## Main results

* `TauCeti.sinkIdempotent_eq_id_or_eq_zero_of_indecomposable`: an idempotent of `Mᵢ` fixing the
  image of the arrows into a sink `i` of an indecomposable `M` is the identity, or is zero and `M`
  vanishes away from `i`.
* `TauCeti.exists_ne_zero_span_eq_top_of_forall_subsingleton` and
  `TauCeti.nonempty_iso_simpleRep_of_forall_subsingleton`: an indecomposable representation
  concentrated at a sink is a line there, hence isomorphic to the vertex simple.
* `TauCeti.incomingSum_surjective_of_indecomposable`: **the sum of the arrows into a sink is onto
  for every indecomposable representation not isomorphic to the vertex simple there.**
* `TauCeti.dimVector_reflectRep_of_indecomposable`: consequently the reflection at a sink acts on
  the dimension vector of such a representation by the simple reflection at that vertex.

## Implementation notes

`TauCeti.sinkEnd` takes its hypothesis on `π` in the form "`π` fixes the image of each arrow into
`i`" rather than "`π` fixes the range of `TauCeti.incomingSum`". The two agree on a finite quiver,
by `TauCeti.map_toPath_mem_range_incomingSum`, but the arrow form needs no finiteness, and neither
then do the construction, its recognition lemmas, or the statement that an indecomposable
representation concentrated at a sink is a line there. Finiteness enters only where
`TauCeti.incomingSum` does.

The results comparing `M` with `TauCeti.simpleRep k Q i` are stated in the last section, where the
quiver, its arrows and the field all live in one universe. This is forced, not chosen: the vertex
spaces of a reflected representation are cut out of a product indexed by the arrows, so
`TauCeti.reflectRep` needs them in `max v w x`, while `Sᵢ` puts the field itself at `i` and so
needs them in the universe of the field. A statement mentioning both therefore has to identify the
two, and the general statements above -- which name no vertex simple -- are proved in the wider
setting and specialize to it.

As in the neighbouring files, a vertex `i : Q` is used as an object of the free category
`CategoryTheory.Paths Q`, which is `Q` only by unfolding a semireducible definition. Rewriting
cannot see through that identification, so every step that branches on equality of vertices is
factored through a lemma quantified over `Q`, and the components of `TauCeti.sinkEnd` are supplied
by the private `sinkEndApp`; `TauCeti.sinkEnd_app_self` and `TauCeti.sinkEnd_app_of_ne` are the
interface.

## References

This is the Layer 4 identity `dim (C⁺ᵢ M) = sᵢ · dim M` of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md` with its hypothesis
discharged, and the input to the second milestone of that roadmap's Layer 5, that reflection
preserves indecomposability away from `Sᵢ`. See Bernstein--Gelfand--Ponomarev, *Coxeter functors
and Gabriel's theorem*, and Derksen--Weyman, *An Introduction to Quiver Representations*, Ch. 2.
-/

public section

namespace TauCeti

open CategoryTheory
open _root_.TauCeti.Quiver

universe u v w x

section General

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
variable {M : QuiverRep.{u, v, w, max v w x} k Q} {i : Q}

/-! ### The endomorphism attached to an idempotent at a sink -/

section SinkEnd

variable {π : M.obj i →ₗ[k] M.obj i}

variable (M π) in
open scoped Classical in
/-- The vertex components of `TauCeti.sinkEnd`: the given endomorphism at `i`, the identity
elsewhere. -/
private noncomputable def sinkEndApp (a : Q) : M.obj a ⟶ M.obj a :=
  if h : a = i then eqToHom (by rw [h]) ≫ ModuleCat.ofHom π ≫ eqToHom (by rw [h])
  else 𝟙 (M.obj a)

@[simp]
private theorem sinkEndApp_self : sinkEndApp M π i = ModuleCat.ofHom π := by
  classical
  simp only [sinkEndApp, dite_eq_left rfl, eqToHom_refl, Category.id_comp, Category.comp_id]

@[simp]
private theorem sinkEndApp_of_ne {a : Q} (ha : a ≠ i) : sinkEndApp M π a = 𝟙 (M.obj a) := by
  classical
  simp only [sinkEndApp, dite_eq_right ha]

/-- A vector fixed on the image of every arrow into `i` is fixed on the image of every path into
`i` from another vertex: such a path ends with an arrow into `i`. -/
private theorem map_path_fixed
    (hπ : ∀ (b : Q) (e : b ⟶ i) (z : M.obj b), π ((M.map e.toPath).hom z) =
      (M.map e.toPath).hom z)
    {a : Q} (ha : a ≠ i) (p : Quiver.Path a i) (y : M.obj a) :
    π ((M.map p).hom y) = (M.map p).hom y := by
  cases p with
  | nil => exact absurd rfl ha
  | cons q e =>
    have hcomp : M.map (q.cons e) = M.map q ≫ M.map e.toPath := M.map_comp q e.toPath
    rw [hcomp]
    exact hπ _ e _

private theorem sinkEndApp_naturality (hi : IsSink i)
    (hπ : ∀ (b : Q) (e : b ⟶ i) (z : M.obj b), π ((M.map e.toPath).hom z) =
      (M.map e.toPath).hom z)
    {a b : Q} (p : Quiver.Path a b) :
    M.map p ≫ sinkEndApp M π b = sinkEndApp M π a ≫ M.map p := by
  rcases eq_or_ne a i with rfl | ha
  · -- a path out of a sink is trivial, and both sides are its component at the sink
    obtain rfl := hi.eq_of_path p
    rw [hi.path_self_eq_nil p, QuiverRep.map_nil, Category.id_comp, Category.comp_id]
  · rw [sinkEndApp_of_ne ha, Category.id_comp]
    rcases eq_or_ne b i with rfl | hb
    · rw [sinkEndApp_self]
      exact ModuleCat.hom_ext (LinearMap.ext fun y ↦ map_path_fixed hπ ha p y)
    · rw [sinkEndApp_of_ne hb, Category.comp_id]

variable (M) in
/-- **The endomorphism of `M` given by an endomorphism at a sink.** For a sink `i` of `Q` and a
linear endomorphism `π` of `Mᵢ` fixing the image of every arrow into `i`, this is the endomorphism
of `M` acting by `π` at `i` and by the identity at every other vertex. -/
noncomputable def sinkEnd (hi : IsSink i) (π : M.obj i →ₗ[k] M.obj i)
    (hπ : ∀ (b : Q) (e : b ⟶ i) (z : M.obj b), π ((M.map e.toPath).hom z) =
      (M.map e.toPath).hom z) : M ⟶ M where
  app a := sinkEndApp M π a
  naturality _ _ p := sinkEndApp_naturality hi hπ p

variable {hi : IsSink i}
  {hπ : ∀ (b : Q) (e : b ⟶ i) (z : M.obj b), π ((M.map e.toPath).hom z) = (M.map e.toPath).hom z}

private theorem sinkEnd_app (a : Q) : (sinkEnd M hi π hπ).app a = sinkEndApp M π a := rfl

/-- At the sink, `TauCeti.sinkEnd` acts by the given endomorphism. -/
@[simp]
theorem sinkEnd_app_self : (sinkEnd M hi π hπ).app i = ModuleCat.ofHom π :=
  (sinkEnd_app i).trans sinkEndApp_self

/-- Away from the sink, `TauCeti.sinkEnd` acts by the identity. -/
@[simp]
theorem sinkEnd_app_of_ne {a : Q} (ha : a ≠ i) : (sinkEnd M hi π hπ).app a = 𝟙 (M.obj a) :=
  (sinkEnd_app a).trans (sinkEndApp_of_ne ha)

private theorem sinkEndApp_comp_self (hidem : IsIdempotentElem π) (a : Q) :
    sinkEndApp M π a ≫ sinkEndApp M π a = sinkEndApp M π a := by
  rcases eq_or_ne a i with rfl | ha
  · rw [sinkEndApp_self, ← ModuleCat.ofHom_comp]
    exact congrArg ModuleCat.ofHom hidem
  · rw [sinkEndApp_of_ne ha, Category.comp_id]

private theorem sinkEndApp_eq_id (h : π = LinearMap.id) (a : Q) :
    sinkEndApp M π a = 𝟙 (M.obj a) := by
  rcases eq_or_ne a i with rfl | ha
  · rw [sinkEndApp_self, h]
    rfl
  · rw [sinkEndApp_of_ne ha]

private theorem sinkEndApp_eq_zero (hzero : π = 0)
    (hsub : ∀ a : Q, a ≠ i → Subsingleton (M.obj a)) (a : Q) : sinkEndApp M π a = 0 := by
  rcases eq_or_ne a i with rfl | ha
  · rw [sinkEndApp_self, hzero]
    rfl
  · have := hsub a ha
    rw [sinkEndApp_of_ne ha]
    exact (Limits.IsZero.iff_id_eq_zero _).mp (ModuleCat.isZero_of_subsingleton _)

/-- `TauCeti.sinkEnd` is idempotent as soon as the endomorphism it is built from is. -/
theorem sinkEnd_comp_self (hidem : IsIdempotentElem π) :
    sinkEnd M hi π hπ ≫ sinkEnd M hi π hπ = sinkEnd M hi π hπ :=
  NatTrans.ext (funext fun a ↦ sinkEndApp_comp_self hidem a)

/-- `TauCeti.sinkEnd` is the identity exactly when the endomorphism it is built from is. -/
@[simp]
theorem sinkEnd_eq_id_iff : sinkEnd M hi π hπ = 𝟙 M ↔ π = LinearMap.id := by
  refine ⟨fun h ↦ ?_, fun h ↦ NatTrans.ext (funext fun a ↦ sinkEndApp_eq_id h a)⟩
  have happ : (sinkEnd M hi π hπ).app i = 𝟙 (M.obj i) := by rw [h]; rfl
  rw [sinkEnd_app_self] at happ
  exact congrArg ModuleCat.Hom.hom happ

/-- `TauCeti.sinkEnd` vanishes exactly when the endomorphism it is built from vanishes and the
representation is concentrated at the sink: away from the sink it acts by the identity, which is
zero only on a vanishing vertex space. -/
@[simp]
theorem sinkEnd_eq_zero_iff :
    sinkEnd M hi π hπ = 0 ↔ π = 0 ∧ ∀ a : Q, a ≠ i → Subsingleton (M.obj a) := by
  refine ⟨fun h ↦ ⟨?_, fun a ha ↦ ?_⟩,
    fun ⟨hzero, hsub⟩ ↦ NatTrans.ext (funext fun a ↦ sinkEndApp_eq_zero hzero hsub a)⟩
  · have happ : (sinkEnd M hi π hπ).app i = 0 := by rw [h]; rfl
    rw [sinkEnd_app_self] at happ
    exact congrArg ModuleCat.Hom.hom happ
  · have happ : (sinkEnd M hi π hπ).app a = 0 := by rw [h]; rfl
    rw [sinkEnd_app_of_ne ha] at happ
    exact ModuleCat.subsingleton_of_isZero ((Limits.IsZero.iff_id_eq_zero _).mpr happ)

end SinkEnd

/-! ### Idempotents at a sink of an indecomposable representation -/

section Idempotents

private theorem isZero_of_forall_subsingleton (hall : ∀ a : Q, Subsingleton (M.obj a)) :
    Limits.IsZero M :=
  Functor.isZero _ fun a ↦ @ModuleCat.isZero_of_subsingleton k _ (M.obj a) (hall a)

/-- **An idempotent at a sink of an indecomposable representation is trivial.** Let `i` be a sink
of `Q` and `M` an indecomposable representation. An idempotent endomorphism of `Mᵢ` fixing the
image of every arrow into `i` is either the identity, or zero — and in the second case `M` vanishes
away from `i`. -/
theorem sinkIdempotent_eq_id_or_eq_zero_of_indecomposable (hi : IsSink i)
    (hM : Indecomposable M) (π : M.obj i →ₗ[k] M.obj i)
    (hπ : ∀ (b : Q) (e : b ⟶ i) (z : M.obj b), π ((M.map e.toPath).hom z) =
      (M.map e.toPath).hom z)
    (hidem : IsIdempotentElem π) :
    π = LinearMap.id ∨ π = 0 ∧ ∀ a : Q, a ≠ i → Subsingleton (M.obj a) := by
  rcases idempotent_eq_zero_or_id_of_indecomposable hM
      (sinkEnd_comp_self (hi := hi) (hπ := hπ) hidem) with h | h
  · exact Or.inr ((sinkEnd_eq_zero_iff (hi := hi) (hπ := hπ)).mp h)
  · exact Or.inl ((sinkEnd_eq_id_iff (hi := hi) (hπ := hπ)).mp h)

/-- **An indecomposable representation concentrated at a sink is a line there**: its vertex space
at the sink is spanned by a single nonzero vector. -/
theorem exists_ne_zero_span_eq_top_of_forall_subsingleton (hi : IsSink i)
    (hM : Indecomposable M) (h : ∀ a : Q, a ≠ i → Subsingleton (M.obj a)) :
    ∃ y : M.obj i, y ≠ 0 ∧ Submodule.span k {y} = ⊤ := by
  -- the vertex space at `i` is nonzero, since otherwise `M` would be a zero object
  have hnt : Nontrivial (M.obj i) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    refine hM.1 (isZero_of_forall_subsingleton fun a ↦ ?_)
    rcases eq_or_ne a i with rfl | ha
    · exact hs
    · exact h a ha
  obtain ⟨y, hy⟩ := exists_ne (0 : M.obj i)
  refine ⟨y, hy, ?_⟩
  -- an arrow into a sink starts elsewhere, so it acts by zero here and the projection onto the
  -- line through `y` extends to an endomorphism of `M`
  obtain ⟨U, hU⟩ := (Submodule.span k {y}).exists_isCompl
  have hidem : IsIdempotentElem ((Submodule.span k {y}).projection U hU) :=
    Submodule.isIdempotentElem_projection hU
  have hproj : LinearMap.IsProj (Submodule.span k {y})
      ((Submodule.span k {y}).projection U hU) := by
    have hrange := LinearMap.IsIdempotentElem.isProj_range _ hidem
    rwa [Submodule.range_projection hU] at hrange
  have hπ : ∀ (b : Q) (e : b ⟶ i) (z : M.obj b),
      (Submodule.span k {y}).projection U hU ((M.map e.toPath).hom z) =
        (M.map e.toPath).hom z := by
    intro b e z
    have : Subsingleton (M.obj b) := h b (hi.ne_of_hom e)
    rw [Subsingleton.elim z 0, map_zero, map_zero]
  rcases sinkIdempotent_eq_id_or_eq_zero_of_indecomposable hi hM _ hπ hidem with hid | ⟨hz, -⟩
  · exact hproj.submodule_eq_top_iff.mpr hid
  · -- the projection onto the line through `y` does not vanish
    exact absurd (Submodule.span_singleton_eq_bot.mp (hproj.submodule_eq_bot_iff.mpr hz)) hy

end Idempotents

/-! ### The surjectivity of the incoming sum -/

section IncomingSum

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

/-- **The sum of the arrows into a sink of an indecomposable representation is onto, unless the
representation is concentrated at that sink.** This is the surjectivity hypothesis of
`TauCeti.dimVector_reflectRep`, discharged: the range of the incoming sum is a direct summand of
`Mᵢ`, so a proper range would split `M`, and the only splitting an indecomposable representation
admits leaves nothing outside the sink. -/
theorem incomingSum_surjective_or_forall_subsingleton (hi : IsSink i) (hM : Indecomposable M) :
    Function.Surjective (incomingSum M i) ∨ ∀ a : Q, a ≠ i → Subsingleton (M.obj a) := by
  -- project onto the range of the incoming sum along a complement
  obtain ⟨U, hU⟩ := (LinearMap.range (incomingSum M i)).exists_isCompl
  have hidem : IsIdempotentElem ((LinearMap.range (incomingSum M i)).projection U hU) :=
    Submodule.isIdempotentElem_projection hU
  have hproj : LinearMap.IsProj (LinearMap.range (incomingSum M i))
      ((LinearMap.range (incomingSum M i)).projection U hU) := by
    have hrange := LinearMap.IsIdempotentElem.isProj_range _ hidem
    rwa [Submodule.range_projection hU] at hrange
  have hπ : ∀ (b : Q) (e : b ⟶ i) (z : M.obj b),
      (LinearMap.range (incomingSum M i)).projection U hU ((M.map e.toPath).hom z) =
        (M.map e.toPath).hom z := fun b e z ↦
    (Submodule.projection_eq_self_iff hU _).mpr (map_toPath_mem_range_incomingSum M e z)
  rcases sinkIdempotent_eq_id_or_eq_zero_of_indecomposable hi hM _ hπ hidem with hid | ⟨-, hsub⟩
  · -- the projection onto the range is the identity, so the range is everything
    exact Or.inl (LinearMap.range_eq_top.mp (hproj.submodule_eq_top_iff.mpr hid))
  · exact Or.inr hsub

end IncomingSum

end General

/-! ### The vertex simple as the exceptional case -/

section VertexSimple

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u} Q]
variable {M : QuiverRep.{u, u, u, u} k Q} {i : Q}

/-- No path of positive length leaves a sink, so every vector of the vertex space there satisfies
the hypothesis of `TauCeti.simpleRepHom`. -/
private theorem map_eq_zero_of_isSink (hi : IsSink i) (y : M.obj ((Paths.of Q).obj i)) {a : Q}
    (p : Quiver.Path i a) (hp : p.length ≠ 0) : M.map p y = 0 := by
  obtain rfl := hi.eq_of_path p
  rw [hi.path_self_eq_nil p] at hp
  exact absurd Quiver.Path.length_nil hp

/-- **An indecomposable representation concentrated at a sink is the vertex simple there.** -/
theorem nonempty_iso_simpleRep_of_forall_subsingleton (hi : IsSink i) (hM : Indecomposable M)
    (h : ∀ a : Q, a ≠ i → Subsingleton (M.obj a)) : Nonempty (M ≅ simpleRep k Q i) := by
  obtain ⟨y, hy, hspan⟩ := exists_ne_zero_span_eq_top_of_forall_subsingleton hi hM h
  have := isIso_simpleRepHom y (map_eq_zero_of_isSink hi y) hy hspan fun a ha ↦
    @ModuleCat.isZero_of_subsingleton k _ (M.obj a) (h a ha)
  exact ⟨(asIso (simpleRepHom y (map_eq_zero_of_isSink hi y))).symm⟩

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

/-- **The sum of the arrows into a sink is onto for every indecomposable representation other than
the vertex simple there.** The vertex simple `Sᵢ` is genuinely excluded, by
`TauCeti.incomingSum_not_surjective`. -/
theorem incomingSum_surjective_of_indecomposable (hi : IsSink i) (hM : Indecomposable M)
    (hne : ¬ Nonempty (M ≅ simpleRep k Q i)) : Function.Surjective (incomingSum M i) :=
  (incomingSum_surjective_or_forall_subsingleton hi hM).resolve_right fun h ↦
    hne (nonempty_iso_simpleRep_of_forall_subsingleton hi hM h)

/-- **The reflection at a sink acts on the dimension vector of an indecomposable representation by
the simple reflection there**, unless that representation is the vertex simple at the sink, which
the reflection annihilates instead. This is the Layer 4 identity `dim (C⁺ᵢ M) = sᵢ · dim M` with
its hypothesis discharged. -/
theorem dimVector_reflectRep_of_indecomposable [DecidableEq Q] (hi : IsSink i)
    (hM : Indecomposable M) (hne : ¬ Nonempty (M ≅ simpleRep k Q i))
    (hfin : ∀ e : Σ b : Q, (b ⟶ i), FiniteDimensional k (M.obj e.1)) :
    (fun j : Q ↦ (dimVector (reflectRep M hi) j : ℤ))
      = vertexPreReflection Q i (fun j ↦ (dimVector M j : ℤ)) :=
  dimVector_reflectRep M hi hfin (incomingSum_surjective_of_indecomposable hi hM hne)

end VertexSimple

end TauCeti
