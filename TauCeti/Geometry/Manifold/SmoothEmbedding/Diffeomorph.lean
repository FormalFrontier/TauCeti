/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Composing smooth embeddings with diffeomorphisms

Mathlib defines `Manifold.IsSmoothEmbedding` as an immersion that is also a topological embedding,
and lists `Diffeomorph.isSmoothEmbedding` as a `TODO` in
`Mathlib/Geometry/Manifold/SmoothEmbedding.lean`, because a general composite of immersions has to
combine two complements.

Composing with a **diffeomorphism** is elementary, and
`TauCeti/Geometry/Manifold/Immersion.lean` settles it at the level of immersions: a diffeomorphism
carries charts to charts, so both composites are immersions with the *same* complement. This file
adds the topological half — composing with a diffeomorphism on either side preserves being a
topological embedding — and packages the result as operations on the bundled type
`TauCeti.SmoothEmbedding`.

Since the composition is transparent, the bundled operations are just reindexing: a
`TauCeti.SmoothEmbedding` may be reparametrised by a diffeomorphism of its source
(`TauCeti.SmoothEmbedding.compDiffeomorph`) or transported by a diffeomorphism of its target
(`TauCeti.SmoothEmbedding.transDiffeomorph`). Reparametrisation leaves the image alone and
transport moves it by the ambient diffeomorphism, and the two assemble into an action of the
self-diffeomorphism group `TauCeti.Diff` of the target and a right action of that of the source;
the two actions commute, which is recorded as a `SMulCommClass` instance.

This is the transport layer that layer 4 of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`) needs for its geometric presentations, where a knot
presentation is a smooth embedding of the circle into the ambient manifold `N`: reversing the
orientation of such a presentation and rotating its parametrisation are precisely precomposition
with a diffeomorphism of the circle, while the ambient `Diff(N)`-action is postcomposition.

## Main results

* `TauCeti.isSmoothEmbedding_comp_diffeomorph` and
  `TauCeti.isSmoothEmbedding_diffeomorph_comp`, with their `_iff` companions: smooth embeddings are
  stable under composition with a diffeomorphism on either side.
* `TauCeti.isSmoothEmbedding_diffeomorph`: a diffeomorphism is a smooth embedding.

## Main definitions

* `TauCeti.SmoothEmbedding.ofDiffeomorph`: a diffeomorphism as a bundled smooth embedding.
* `TauCeti.SmoothEmbedding.compDiffeomorph`: reparametrise a bundled smooth embedding by a
  diffeomorphism of its source.
* `TauCeti.SmoothEmbedding.transDiffeomorph`: transport a bundled smooth embedding by a
  diffeomorphism of its target.
* the `MulAction (Diff J N n) (SmoothEmbedding I J n M N)` given by transport, and the
  reparametrisation action of `(Diff I M n)ᵐᵒᵖ`.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 1, for immersions and
  embeddings and their behaviour under composition.
-/

public section

noncomputable section

namespace TauCeti

open Manifold Set
open scoped Manifold ContDiff

section IsSmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
  {n : ℕ∞ω} {f : M → N}

/-- Reparametrising a smooth embedding by a diffeomorphism of the source gives a smooth
embedding. -/
theorem isSmoothEmbedding_comp_diffeomorph [IsManifold I n M']
    (e : M' ≃ₘ^n⟮I, I⟯ M) (h : IsSmoothEmbedding I J n f) :
    IsSmoothEmbedding I J n (f ∘ e) :=
  ⟨isImmersion_comp_diffeomorph e h.isImmersion, h.isEmbedding.comp e.toHomeomorph.isEmbedding⟩

/-- Transporting a smooth embedding by a diffeomorphism of the target gives a smooth embedding. -/
theorem isSmoothEmbedding_diffeomorph_comp [IsManifold J n P]
    (h : IsSmoothEmbedding I J n f) (e : N ≃ₘ^n⟮J, J⟯ P) :
    IsSmoothEmbedding I J n (e ∘ f) :=
  ⟨isImmersion_diffeomorph_comp h.isImmersion e, e.toHomeomorph.isEmbedding.comp h.isEmbedding⟩

/-- Precomposition with a diffeomorphism of the source neither creates nor destroys a smooth
embedding. -/
theorem isSmoothEmbedding_comp_diffeomorph_iff [IsManifold I n M] [IsManifold I n M']
    (e : M' ≃ₘ^n⟮I, I⟯ M) : IsSmoothEmbedding I J n (f ∘ e) ↔ IsSmoothEmbedding I J n f := by
  refine ⟨fun h => ?_, isSmoothEmbedding_comp_diffeomorph e⟩
  have hcomp : (f ∘ ⇑e) ∘ ⇑e.symm = f := funext fun y => by simp
  have h' := isSmoothEmbedding_comp_diffeomorph e.symm h
  rwa [hcomp] at h'

/-- Postcomposition with a diffeomorphism of the target neither creates nor destroys a smooth
embedding. -/
theorem isSmoothEmbedding_diffeomorph_comp_iff [IsManifold J n N] [IsManifold J n P]
    (e : N ≃ₘ^n⟮J, J⟯ P) : IsSmoothEmbedding I J n (e ∘ f) ↔ IsSmoothEmbedding I J n f := by
  refine ⟨fun h => ?_, fun h => isSmoothEmbedding_diffeomorph_comp h e⟩
  have hcomp : ⇑e.symm ∘ ⇑e ∘ f = f := funext fun y => by simp
  have h' := isSmoothEmbedding_diffeomorph_comp h e.symm
  rwa [hcomp] at h'

/-- A diffeomorphism is a smooth embedding.

This is the statement Mathlib lists as the `TODO` `Diffeomorph.isSmoothEmbedding` in
`Mathlib/Geometry/Manifold/SmoothEmbedding.lean`; the name is flat here because a `Diffeomorph`
namespace nested in `TauCeti` would break dot notation on Mathlib's type. -/
theorem isSmoothEmbedding_diffeomorph [IsManifold I n M] [IsManifold I n M']
    (e : M ≃ₘ^n⟮I, I⟯ M') : IsSmoothEmbedding I I n e :=
  ⟨isImmersion_diffeomorph e, e.toHomeomorph.isEmbedding⟩

end IsSmoothEmbedding

namespace SmoothEmbedding

section Bundled

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H M'']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
  {n : ℕ∞ω}

/-- A diffeomorphism, as a bundled smooth embedding. -/
def ofDiffeomorph [IsManifold I n M] [IsManifold I n M'] (e : M ≃ₘ^n⟮I, I⟯ M') :
    SmoothEmbedding I I n M M' :=
  SmoothEmbedding.ofIsSmoothEmbedding e (isSmoothEmbedding_diffeomorph e)

@[simp]
theorem ofDiffeomorph_apply [IsManifold I n M] [IsManifold I n M'] (e : M ≃ₘ^n⟮I, I⟯ M') (x : M) :
    ofDiffeomorph e x = e x := by
  simp only [ofDiffeomorph, ofIsSmoothEmbedding_apply]

@[simp]
theorem coe_ofDiffeomorph [IsManifold I n M] [IsManifold I n M'] (e : M ≃ₘ^n⟮I, I⟯ M') :
    ⇑(ofDiffeomorph e) = e := by
  funext x
  exact ofDiffeomorph_apply e x

/-- A diffeomorphism is onto, so as a smooth embedding it has full image.

Not a `simp` lemma: `coe_ofDiffeomorph` already rewrites the left-hand side, so this form is never
in normal form. -/
theorem range_ofDiffeomorph [IsManifold I n M] [IsManifold I n M'] (e : M ≃ₘ^n⟮I, I⟯ M') :
    range (ofDiffeomorph e) = univ := by
  rw [coe_ofDiffeomorph]
  exact (EquivLike.surjective e).range_eq

/-- **Reparametrisation.** A diffeomorphism `e : M' ≃ₘ M` of the source turns a bundled smooth
embedding `f : M → N` into the bundled smooth embedding `f ∘ e : M' → N`. For a geometric knot
presentation, an embedding of the circle into the ambient manifold `N`, this is the change of
parametrisation of the knot, orientation reversal included. -/
def compDiffeomorph [IsManifold I n M'] (f : SmoothEmbedding I J n M N)
    (e : M' ≃ₘ^n⟮I, I⟯ M) : SmoothEmbedding I J n M' N :=
  SmoothEmbedding.ofIsSmoothEmbedding (f ∘ e)
    (isSmoothEmbedding_comp_diffeomorph e f.isSmoothEmbedding)

@[simp]
theorem compDiffeomorph_apply [IsManifold I n M']
    (f : SmoothEmbedding I J n M N) (e : M' ≃ₘ^n⟮I, I⟯ M) (x : M') :
    f.compDiffeomorph e x = f (e x) := by
  simp only [compDiffeomorph, ofIsSmoothEmbedding_apply, Function.comp_apply]

@[simp]
theorem coe_compDiffeomorph [IsManifold I n M']
    (f : SmoothEmbedding I J n M N) (e : M' ≃ₘ^n⟮I, I⟯ M) :
    ⇑(f.compDiffeomorph e) = f ∘ e := by
  funext x
  exact compDiffeomorph_apply f e x

/-- Reparametrising by the identity diffeomorphism changes nothing. -/
@[simp]
theorem compDiffeomorph_refl [IsManifold I n M] (f : SmoothEmbedding I J n M N) :
    f.compDiffeomorph (_root_.Diffeomorph.refl I M n) = f := by
  apply SmoothEmbedding.ext
  intro x
  rw [compDiffeomorph_apply]
  rfl

/-- Reparametrising twice is reparametrising by the composite diffeomorphism. -/
@[simp]
theorem compDiffeomorph_compDiffeomorph [IsManifold I n M']
    [IsManifold I n M''] (f : SmoothEmbedding I J n M N) (e : M' ≃ₘ^n⟮I, I⟯ M)
    (e' : M'' ≃ₘ^n⟮I, I⟯ M') :
    (f.compDiffeomorph e).compDiffeomorph e' = f.compDiffeomorph (e'.trans e) := by
  apply SmoothEmbedding.ext
  intro x
  rw [compDiffeomorph_apply, compDiffeomorph_apply, compDiffeomorph_apply]
  rfl

/-- Reparametrisation does not move the image of an embedding.

Not a `simp` lemma: `coe_compDiffeomorph` already rewrites the left-hand side, so this form is never
in normal form. -/
theorem range_compDiffeomorph [IsManifold I n M']
    (f : SmoothEmbedding I J n M N) (e : M' ≃ₘ^n⟮I, I⟯ M) :
    range (f.compDiffeomorph e) = range f := by
  rw [coe_compDiffeomorph]
  exact (EquivLike.surjective e).range_comp _

/-- **Ambient transport.** A diffeomorphism `e : N ≃ₘ P` of the target turns a bundled smooth
embedding `f : M → N` into the bundled smooth embedding `e ∘ f : M → P`. For a geometric knot
presentation this is the action of the ambient diffeomorphism group on knots. -/
def transDiffeomorph [IsManifold J n P] (f : SmoothEmbedding I J n M N)
    (e : N ≃ₘ^n⟮J, J⟯ P) : SmoothEmbedding I J n M P :=
  SmoothEmbedding.ofIsSmoothEmbedding (e ∘ f)
    (isSmoothEmbedding_diffeomorph_comp f.isSmoothEmbedding e)

@[simp]
theorem transDiffeomorph_apply [IsManifold J n P]
    (f : SmoothEmbedding I J n M N) (e : N ≃ₘ^n⟮J, J⟯ P) (x : M) :
    f.transDiffeomorph e x = e (f x) := by
  simp only [transDiffeomorph, ofIsSmoothEmbedding_apply, Function.comp_apply]

@[simp]
theorem coe_transDiffeomorph [IsManifold J n P]
    (f : SmoothEmbedding I J n M N) (e : N ≃ₘ^n⟮J, J⟯ P) :
    ⇑(f.transDiffeomorph e) = e ∘ f := by
  funext x
  exact transDiffeomorph_apply f e x

/-- Transporting by the identity diffeomorphism changes nothing. -/
@[simp]
theorem transDiffeomorph_refl [IsManifold J n N] (f : SmoothEmbedding I J n M N) :
    f.transDiffeomorph (_root_.Diffeomorph.refl J N n) = f := by
  apply SmoothEmbedding.ext
  intro x
  rw [transDiffeomorph_apply]
  rfl

/-- Transporting twice is transporting by the composite diffeomorphism. -/
@[simp]
theorem transDiffeomorph_transDiffeomorph {Q : Type*} [TopologicalSpace Q] [ChartedSpace G Q]
    [IsManifold J n P] [IsManifold J n Q] (f : SmoothEmbedding I J n M N)
    (e : N ≃ₘ^n⟮J, J⟯ P) (e' : P ≃ₘ^n⟮J, J⟯ Q) :
    (f.transDiffeomorph e).transDiffeomorph e' = f.transDiffeomorph (e.trans e') := by
  apply SmoothEmbedding.ext
  intro x
  rw [transDiffeomorph_apply, transDiffeomorph_apply, transDiffeomorph_apply]
  rfl

/-- Ambient transport moves the image of an embedding by the ambient diffeomorphism.

Not a `simp` lemma: `coe_transDiffeomorph` already rewrites the left-hand side, so this form is
never in normal form. -/
theorem range_transDiffeomorph [IsManifold J n P]
    (f : SmoothEmbedding I J n M N) (e : N ≃ₘ^n⟮J, J⟯ P) :
    range (f.transDiffeomorph e) = e '' range f := by
  rw [coe_transDiffeomorph, range_comp]

/-- Reparametrising and transporting commute: they act on opposite sides of the embedding. This is
the normal form for a mixed reparametrisation-and-transport, with the transport innermost. -/
@[simp]
theorem transDiffeomorph_compDiffeomorph [IsManifold I n M'] [IsManifold J n P]
    (f : SmoothEmbedding I J n M N)
    (e : M' ≃ₘ^n⟮I, I⟯ M) (e' : N ≃ₘ^n⟮J, J⟯ P) :
    (f.compDiffeomorph e).transDiffeomorph e' = (f.transDiffeomorph e').compDiffeomorph e :=
  SmoothEmbedding.ext fun x => by rw [transDiffeomorph_apply, compDiffeomorph_apply,
    compDiffeomorph_apply, transDiffeomorph_apply]

/-- The self-diffeomorphism group of the target acts on the smooth embeddings into it, by ambient
transport. This is the action of `Diff(N)` on geometric knot presentations in `N`. -/
instance instMulActionDiff [IsManifold J n N] :
    MulAction (Diff J N n) (SmoothEmbedding I J n M N) where
  smul e f := f.transDiffeomorph e
  one_smul f := f.transDiffeomorph_refl
  mul_smul e e' f := (f.transDiffeomorph_transDiffeomorph e' e).symm

@[simp]
theorem smul_def [IsManifold J n N] (e : Diff J N n) (f : SmoothEmbedding I J n M N) :
    e • f = f.transDiffeomorph e := rfl

/-- The self-diffeomorphism group of the source acts on the smooth embeddings out of it *on the
right*, by reparametrisation; the action is recorded on the opposite group. -/
instance instMulActionMulOppositeDiff [IsManifold I n M] :
    MulAction (Diff I M n)ᵐᵒᵖ (SmoothEmbedding I J n M N) where
  smul e f := f.compDiffeomorph e.unop
  one_smul f := f.compDiffeomorph_refl
  mul_smul e e' f := (f.compDiffeomorph_compDiffeomorph e'.unop e.unop).symm

@[simp]
theorem unop_smul_def [IsManifold I n M] (a : (Diff I M n)ᵐᵒᵖ) (f : SmoothEmbedding I J n M N) :
    a • f = f.compDiffeomorph a.unop := rfl

/-- Ambient transport and reparametrisation commute, so the two actions are compatible. -/
instance instSMulCommClassDiff [IsManifold I n M] [IsManifold J n N] :
    SMulCommClass (Diff J N n) (Diff I M n)ᵐᵒᵖ (SmoothEmbedding I J n M N) :=
  ⟨fun e a f => transDiffeomorph_compDiffeomorph f a.unop e⟩

end Bundled

end SmoothEmbedding

end TauCeti
