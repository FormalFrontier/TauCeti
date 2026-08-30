/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Basic

/-!
# Composing smooth embeddings with diffeomorphisms

Mathlib defines `Manifold.IsImmersion` by a normal form in charts — `f` looks like `u ↦ (u, 0)`
for suitable charts of the source and the target — and `Manifold.IsSmoothEmbedding` as an immersion
that is also a topological embedding. Composition is left open there: `IsImmersion.comp` and
`Diffeomorph.isSmoothEmbedding` are both listed as `TODO`s in
`Mathlib/Geometry/Manifold/Immersion.lean` and `Mathlib/Geometry/Manifold/SmoothEmbedding.lean`,
because a general composite has to combine two complements and needs the differential to split.

This file settles the special case that is elementary and that the geometric-topology roadmap
consumes everywhere: composing with a **diffeomorphism** on either side. Nothing has to be
recombined, because a diffeomorphism carries charts to charts: if `φ` is a chart of `M` in the
maximal atlas and `e : M' ≃ₘ M` is a diffeomorphism, then `φ ∘ e` is a chart of `M'` in the maximal
atlas, and reading `f ∘ e` in it produces literally the same normal form that `f` had in `φ`. The
same argument on the other side pulls an ambient chart back along `e⁻¹`. So both composites are
immersions with the *same* complement, and hence smooth embeddings.

Since the composition is transparent, the bundled operations are then just reindexing: a
`TauCeti.SmoothEmbedding` may be reparametrised by a diffeomorphism of its source
(`TauCeti.SmoothEmbedding.compDiffeomorph`) or transported by a diffeomorphism of its target
(`TauCeti.SmoothEmbedding.transDiffeomorph`). Reparametrisation leaves the image alone and
transport moves it by the ambient diffeomorphism, and the two assemble into an action of the
self-diffeomorphism group `TauCeti.Diff` of the target and a right action of that of the source.

This is the transport layer that layer 4 of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`) needs for its geometric presentations, where a knot
presentation is a smooth embedding `S¹ ↪ M`: reversing the orientation of such a presentation and
rotating its parametrisation are precisely precomposition with a diffeomorphism of the circle,
while the ambient `Diff(M)`-action is postcomposition. The last result of the file connects that
action to the layer's notion of equivalence: an embedding and its transport by the time-one map of
a diffeotopy are smoothly ambient isotopic.

## Main results

* `TauCeti.mem_maximalAtlas_transOpenPartialHomeomorph`: a diffeomorphism pulls a chart of the
  maximal atlas back to a chart of the maximal atlas.
* `TauCeti.isSmoothEmbedding_comp_diffeomorph` and
  `TauCeti.isSmoothEmbedding_diffeomorph_comp`: smooth embeddings are stable under composition with
  a diffeomorphism on either side, together with their `Manifold.IsImmersion` counterparts.
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

section Immersion

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
  {n : ℕ∞ω} {f : M → N}

/-- A diffeomorphism `e : M' ≃ₘ M` pulls a chart `φ` of the maximal atlas of `M` back to the chart
`φ ∘ e` of the maximal atlas of `M'`. This is the only geometric input to the composition results
below: it is what lets a normal form in charts be read on the other side of a diffeomorphism. -/
theorem mem_maximalAtlas_transOpenPartialHomeomorph [IsManifold I n M']
    (e : M' ≃ₘ^n⟮I, I⟯ M) {φ : OpenPartialHomeomorph M H}
    (hφ : φ ∈ IsManifold.maximalAtlas I n M) :
    e.toHomeomorph.transOpenPartialHomeomorph φ ∈ IsManifold.maximalAtlas I n M' := by
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
  exact ⟨(contMDiffOn_of_mem_maximalAtlas hφ).comp e.contMDiff.contMDiffOn fun _ hx => hx,
    e.symm.contMDiff.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hφ)⟩

/-- Precomposing with a diffeomorphism of the source preserves the immersion normal form at a
point, with the same complement: the domain chart of the immersion is pulled back along the
diffeomorphism, and `f ∘ e` read in the new chart is what `f` was in the old one. -/
theorem isImmersionAtOfComplement_comp_diffeomorph [IsManifold I n M']
    (e : M' ≃ₘ^n⟮I, I⟯ M) {x : M'} (h : IsImmersionAtOfComplement F I J n f (e x)) :
    IsImmersionAtOfComplement F I J n (f ∘ e) x := by
  refine IsImmersionAtOfComplement.mk_of_charts h.equiv
    (e.toHomeomorph.transOpenPartialHomeomorph h.domChart) h.codChart h.mem_domChart_source
    h.mem_codChart_source
    (mem_maximalAtlas_transOpenPartialHomeomorph e h.domChart_mem_maximalAtlas)
    h.codChart_mem_maximalAtlas (fun _ hy => h.source_subset_preimage_source hy) fun y hy => ?_
  simpa using h.writtenInCharts hy

/-- Postcomposing with a diffeomorphism of the target preserves the immersion normal form at a
point, with the same complement: the codomain chart of the immersion is pulled back along the
inverse diffeomorphism, and `e ∘ f` read in the new chart is what `f` was in the old one. -/
theorem isImmersionAtOfComplement_diffeomorph_comp [IsManifold J n P]
    {x : M} (h : IsImmersionAtOfComplement F I J n f x) (e : N ≃ₘ^n⟮J, J⟯ P) :
    IsImmersionAtOfComplement F I J n (e ∘ f) x := by
  refine IsImmersionAtOfComplement.mk_of_charts h.equiv h.domChart
    (e.symm.toHomeomorph.transOpenPartialHomeomorph h.codChart) h.mem_domChart_source ?_
    h.domChart_mem_maximalAtlas
    (mem_maximalAtlas_transOpenPartialHomeomorph e.symm h.codChart_mem_maximalAtlas)
    (fun y hy => ?_) fun y hy => ?_
  · simpa using h.mem_codChart_source
  · simpa using h.source_subset_preimage_source hy
  · simpa using h.writtenInCharts hy

/-- Precomposing an immersion with a fixed complement by a diffeomorphism of the source gives an
immersion with the same complement. -/
theorem isImmersionOfComplement_comp_diffeomorph [IsManifold I n M']
    (e : M' ≃ₘ^n⟮I, I⟯ M) (h : IsImmersionOfComplement F I J n f) :
    IsImmersionOfComplement F I J n (f ∘ e) :=
  fun x => isImmersionAtOfComplement_comp_diffeomorph e (h (e x))

/-- Postcomposing an immersion with a fixed complement by a diffeomorphism of the target gives an
immersion with the same complement. -/
theorem isImmersionOfComplement_diffeomorph_comp [IsManifold J n P]
    (h : IsImmersionOfComplement F I J n f) (e : N ≃ₘ^n⟮J, J⟯ P) :
    IsImmersionOfComplement F I J n (e ∘ f) :=
  fun x => isImmersionAtOfComplement_diffeomorph_comp (h x) e

/-- Reparametrising an immersion by a diffeomorphism of the source gives an immersion. -/
theorem isImmersion_comp_diffeomorph [IsManifold I n M']
    (e : M' ≃ₘ^n⟮I, I⟯ M) (h : IsImmersion I J n f) : IsImmersion I J n (f ∘ e) :=
  (isImmersionOfComplement_comp_diffeomorph e h.isImmersionOfComplement_complement).isImmersion

/-- Transporting an immersion by a diffeomorphism of the target gives an immersion. -/
theorem isImmersion_diffeomorph_comp [IsManifold J n P]
    (h : IsImmersion I J n f) (e : N ≃ₘ^n⟮J, J⟯ P) : IsImmersion I J n (e ∘ f) :=
  (isImmersionOfComplement_diffeomorph_comp h.isImmersionOfComplement_complement e).isImmersion

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

/-- A diffeomorphism is an immersion: it is the identity immersion transported by itself. -/
theorem isImmersion_diffeomorph [IsManifold I n M] [IsManifold I n M'] (e : M ≃ₘ^n⟮I, I⟯ M') :
    IsImmersion I I n e :=
  (isImmersion_diffeomorph_comp (IsImmersion.id (I := I) (n := n) (M := M)) e).congr rfl

/-- A diffeomorphism is a smooth embedding. -/
theorem isSmoothEmbedding_diffeomorph [IsManifold I n M] [IsManifold I n M']
    (e : M ≃ₘ^n⟮I, I⟯ M') : IsSmoothEmbedding I I n e :=
  ⟨isImmersion_diffeomorph e, e.toHomeomorph.isEmbedding⟩

end Immersion

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
    SmoothEmbedding I I n M M' where
  toContMDiffMap := ⟨e, e.contMDiff⟩
  isSmoothEmbedding_toFun := isSmoothEmbedding_diffeomorph e

@[simp]
theorem ofDiffeomorph_apply [IsManifold I n M] [IsManifold I n M'] (e : M ≃ₘ^n⟮I, I⟯ M') (x : M) :
    ofDiffeomorph e x = e x := by
  rfl

@[simp]
theorem coe_ofDiffeomorph [IsManifold I n M] [IsManifold I n M'] (e : M ≃ₘ^n⟮I, I⟯ M') :
    ⇑(ofDiffeomorph e) = e := by
  funext x
  exact ofDiffeomorph_apply e x

/-- A diffeomorphism is onto, so as a smooth embedding it has full image. -/
theorem range_ofDiffeomorph [IsManifold I n M] [IsManifold I n M'] (e : M ≃ₘ^n⟮I, I⟯ M') :
    range (ofDiffeomorph e) = univ := by
  rw [coe_ofDiffeomorph]
  exact (EquivLike.surjective e).range_eq

/-- **Reparametrisation.** A diffeomorphism `e : M' ≃ₘ M` of the source turns a bundled smooth
embedding `f : M → N` into the bundled smooth embedding `f ∘ e : M' → N`. For a geometric knot
presentation `S¹ ↪ M`, this is the change of parametrisation of the knot, orientation reversal
included. -/
def compDiffeomorph [IsManifold I n M'] (f : SmoothEmbedding I J n M N)
    (e : M' ≃ₘ^n⟮I, I⟯ M) : SmoothEmbedding I J n M' N where
  toContMDiffMap := ⟨f ∘ e, f.contMDiff.comp e.contMDiff⟩
  isSmoothEmbedding_toFun := isSmoothEmbedding_comp_diffeomorph e f.isSmoothEmbedding

@[simp]
theorem compDiffeomorph_apply [IsManifold I n M']
    (f : SmoothEmbedding I J n M N) (e : M' ≃ₘ^n⟮I, I⟯ M) (x : M') :
    f.compDiffeomorph e x = f (e x) := by
  rfl

@[simp]
theorem coe_compDiffeomorph [IsManifold I n M']
    (f : SmoothEmbedding I J n M N) (e : M' ≃ₘ^n⟮I, I⟯ M) :
    ⇑(f.compDiffeomorph e) = f ∘ e := by
  funext x
  exact compDiffeomorph_apply f e x

/-- Reparametrising by the identity diffeomorphism changes nothing. -/
@[simp]
theorem compDiffeomorph_refl [IsManifold I n M] (f : SmoothEmbedding I J n M N) :
    f.compDiffeomorph (_root_.Diffeomorph.refl I M n) = f :=
  SmoothEmbedding.ext fun _ => rfl

/-- Reparametrising twice is reparametrising by the composite diffeomorphism. -/
theorem compDiffeomorph_compDiffeomorph [IsManifold I n M']
    [IsManifold I n M''] (f : SmoothEmbedding I J n M N) (e : M' ≃ₘ^n⟮I, I⟯ M)
    (e' : M'' ≃ₘ^n⟮I, I⟯ M') :
    (f.compDiffeomorph e).compDiffeomorph e' = f.compDiffeomorph (e'.trans e) :=
  SmoothEmbedding.ext fun _ => rfl

/-- Reparametrisation does not move the image of an embedding. -/
theorem range_compDiffeomorph [IsManifold I n M']
    (f : SmoothEmbedding I J n M N) (e : M' ≃ₘ^n⟮I, I⟯ M) :
    range (f.compDiffeomorph e) = range f := by
  rw [coe_compDiffeomorph]
  exact (EquivLike.surjective e).range_comp _

/-- **Ambient transport.** A diffeomorphism `e : N ≃ₘ P` of the target turns a bundled smooth
embedding `f : M → N` into the bundled smooth embedding `e ∘ f : M → P`. For a geometric knot
presentation this is the action of the ambient diffeomorphism group on knots. -/
def transDiffeomorph [IsManifold J n P] (f : SmoothEmbedding I J n M N)
    (e : N ≃ₘ^n⟮J, J⟯ P) : SmoothEmbedding I J n M P where
  toContMDiffMap := ⟨e ∘ f, e.contMDiff.comp f.contMDiff⟩
  isSmoothEmbedding_toFun := isSmoothEmbedding_diffeomorph_comp f.isSmoothEmbedding e

@[simp]
theorem transDiffeomorph_apply [IsManifold J n P]
    (f : SmoothEmbedding I J n M N) (e : N ≃ₘ^n⟮J, J⟯ P) (x : M) :
    f.transDiffeomorph e x = e (f x) := by
  rfl

@[simp]
theorem coe_transDiffeomorph [IsManifold J n P]
    (f : SmoothEmbedding I J n M N) (e : N ≃ₘ^n⟮J, J⟯ P) :
    ⇑(f.transDiffeomorph e) = e ∘ f := by
  funext x
  exact transDiffeomorph_apply f e x

/-- Transporting by the identity diffeomorphism changes nothing. -/
@[simp]
theorem transDiffeomorph_refl [IsManifold J n N] (f : SmoothEmbedding I J n M N) :
    f.transDiffeomorph (_root_.Diffeomorph.refl J N n) = f :=
  SmoothEmbedding.ext fun _ => rfl

/-- Transporting twice is transporting by the composite diffeomorphism. -/
theorem transDiffeomorph_transDiffeomorph {Q : Type*} [TopologicalSpace Q] [ChartedSpace G Q]
    [IsManifold J n P] [IsManifold J n Q] (f : SmoothEmbedding I J n M N)
    (e : N ≃ₘ^n⟮J, J⟯ P) (e' : P ≃ₘ^n⟮J, J⟯ Q) :
    (f.transDiffeomorph e).transDiffeomorph e' = f.transDiffeomorph (e.trans e') :=
  SmoothEmbedding.ext fun _ => rfl

/-- Ambient transport moves the image of an embedding by the ambient diffeomorphism. -/
theorem range_transDiffeomorph [IsManifold J n P]
    (f : SmoothEmbedding I J n M N) (e : N ≃ₘ^n⟮J, J⟯ P) :
    range (f.transDiffeomorph e) = e '' range f := by
  rw [coe_transDiffeomorph, range_comp]

/-- Reparametrising and transporting commute: they act on opposite sides of the embedding. -/
theorem transDiffeomorph_compDiffeomorph [IsManifold I n M'] [IsManifold J n P]
    (f : SmoothEmbedding I J n M N)
    (e : M' ≃ₘ^n⟮I, I⟯ M) (e' : N ≃ₘ^n⟮J, J⟯ P) :
    (f.compDiffeomorph e).transDiffeomorph e' = (f.transDiffeomorph e').compDiffeomorph e :=
  SmoothEmbedding.ext fun _ => rfl

/-- The self-diffeomorphism group of the target acts on the smooth embeddings into it, by ambient
transport. This is the action of `Diff(M)` on geometric knot presentations. -/
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
  mul_smul e e' f := by
    refine SmoothEmbedding.ext fun x => ?_
    change (f.compDiffeomorph (e * e').unop) x
      = ((f.compDiffeomorph e'.unop).compDiffeomorph e.unop) x
    rw [compDiffeomorph_apply, compDiffeomorph_apply, compDiffeomorph_apply,
      MulOpposite.unop_mul, Diffeomorph.mul_apply]

@[simp]
theorem op_smul_def [IsManifold I n M] (e : Diff I M n) (f : SmoothEmbedding I J n M N) :
    MulOpposite.op e • f = f.compDiffeomorph e := rfl

end Bundled

section AmbientIsotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f g : SmoothEmbedding I J n M N}

/-- **Transport along a diffeotopy is an ambient isotopy.** An embedding and its transport by the
time-one map of a diffeotopy of the ambient manifold are smoothly ambient isotopic: the diffeotopy
itself is the witness. So the ambient `Diff`-action of `TauCeti.SmoothEmbedding.instMulActionDiff`
preserves the equivalence class of an embedding whenever the acting diffeomorphism is diffeotopic
to the identity — for knot presentations, that is exactly ambient isotopy of knots. -/
theorem smoothAmbientIsotopic_transDiffeomorph_final [IsManifold J n N]
    (f : SmoothEmbedding I J n M N) (Φ : Diffeotopy J n N) :
    f.SmoothAmbientIsotopic (f.transDiffeomorph Φ.final) :=
  SmoothAmbientIsotopic.of_diffeotopy Φ fun _ => rfl

/-- Reparametrising two embeddings by the same diffeomorphism of the source preserves smooth
ambient isotopy: the witnessing diffeotopy of the ambient manifold is unchanged. -/
theorem SmoothAmbientIsotopic.compDiffeomorph [IsManifold I n M']
    (hfg : f.SmoothAmbientIsotopic g) (e : M' ≃ₘ^n⟮I, I⟯ M) :
    (f.compDiffeomorph e).SmoothAmbientIsotopic (g.compDiffeomorph e) := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hfg
  exact SmoothAmbientIsotopic.of_diffeotopy Φ fun x => hΦ (e x)

end AmbientIsotopy

end SmoothEmbedding

end TauCeti
