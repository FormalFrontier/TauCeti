/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ZeroSequenceOfUnits
public import TauCeti.Topology.Algebra.OpenMapping.Henkel
import TauCeti.Topology.Algebra.Nonarchimedean.Pi
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# The open mapping theorem over a Tate ring

`TauCeti.HasZeroSequenceOfUnits.isOpenMap` is Henkel's theorem in the generality it is proved in:
the scalars need only a zero sequence of units, the source is a complete first-countable
nonarchimedean group, and the target need only be `T0Space` and Baire. This file records both
halves of the roadmap's derived form over a Tate ring — a surjective linear map, continuous at
zero, from a complete pseudometrisable module onto a complete metrisable one is open, and induces
the quotient topology — by discharging Henkel's hypotheses from ones a consumer can check.

The asymmetry is real and not an oversight. Both modules are asked for completeness and a countably
generated uniformity; only the *target* is asked to be `T0Space`, so only the target is metrisable.
The source is pseudometrisable, which is all Henkel needs of it, and separating the source would be
an assumption the theorem does not use.

Three of Henkel's substantive hypotheses survive the translation, and all three are stated. The
remaining binders are the structural context — what `A`, `M` and `N` are and how they are
topologised — and they are not counted among the three. They do not all move the same way. Some
carry across verbatim: `TopologicalSpace A`, `AddCommGroup M`, `UniformSpace M`,
`IsUniformAddGroup M`, and the target's `ContinuousConstSMul A N`. Others are strengthened:
`MonoidWithZero A` to `CommRing A`, `MulActionWithZero A M` to `Module A M`, `AddGroup N` to
`AddCommGroup N`, `MulAction A N` to `Module A N`, and the target's `TopologicalSpace N` /
`IsTopologicalAddGroup N` to a uniformity. And `IsTopologicalRing A` has no Henkel counterpart at
all — it is what `IsTateRing A` is stated over.

* `CompleteSpace M`. Nothing supplies it; completeness of the source is what
  `TauCeti.mem_image_of_mem_closure_image` needs in order to remove the closure.
* `NonarchimedeanAddGroup M`. Metrisability does not supply it, and nothing about a module over a
  Tate ring does either; it is a genuine assumption on the source.
* `T0Space N`. This is the Hausdorff hypothesis. It cannot come from the metrisability route,
  because `IsCompletelyPseudoMetrizableSpace` is *pseudo* and carries no separation.

Henkel also takes a fourth *explicit* argument, `hc : ∀ x : M, ContinuousAt (fun a : A ↦ a • x) 0`
— continuity of the scalar action at zero, in the scalar variable, on the **source**. That is what
`ContinuousSMul A M` is here to supply, and it is why that binder is neither structural nor
removable: dropping it leaves `hc` unprovable.

This is the whole reason the two sides carry different action hypotheses. The source needs
continuity in the *scalar* variable, to discharge `hc`; the target needs only continuity in the
*module* variable, which is exactly `ContinuousConstSMul A N` — Henkel's own binder, carried across
unchanged. The asymmetry is not an oversight.

The rest are inferred. `IsTateRing A` gives `HasZeroSequenceOfUnits A` through the powers of a
pseudouniformiser (`TauCeti.Huber.IsTateRing.hasZeroSequenceOfUnits`) — this is the only place the
Tate condition is used, and a Huber ring that is not Tate need not admit such a sequence.
Countable generation of the uniformity gives it for `𝓝 0`, which is the first countability Henkel
asks of the source.

The target's completeness deserves a word, since it is not what one would guess Henkel needs.
Henkel asks the target to be a **Baire** space, and completeness plus a countably generated
uniformity is how that is obtained here: the two together make `N` completely pseudometrisable
(`IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable`), and a completely
pseudometrisable space is Baire by the first Baire category theorem. So `CompleteSpace N` is not
removable without putting a Baire hypothesis back in its place.

Continuity is asked only at zero. For an additive map out of a topological group that is
equivalent to continuity everywhere (`continuous_of_continuousAt_zero`), so this is the same
hypothesis spelled at its weakest, and a consumer holding `Continuous f` supplies
`‹Continuous f›.continuousAt`.

Both halves of the roadmap's derived form are here. `TauCeti.Huber.IsTateRing.isOpenMap` is the
open-map half; `TauCeti.Huber.IsTateRing.isQuotientMap` is the other — that such a map induces the
quotient topology — and it delegates to `TauCeti.HasZeroSequenceOfUnits.isQuotientMap` exactly as
the open-map form delegates to `TauCeti.HasZeroSequenceOfUnits.isOpenMap`. It is the quotient form
that the strict-morphism material will consume, since what matters there is not that images are
open but that the target's topology is determined by the source's.

## Main results

* `TauCeti.Huber.IsTateRing.isOpenMap`: a surjective linear map, continuous at zero, from a
  complete pseudometrisable module onto a complete metrisable one over a Tate ring is open.
* `TauCeti.Huber.IsTateRing.isQuotientMap`: the same map induces the quotient topology on its
  target. This is the form the strict-morphism material will consume.
* `TauCeti.Huber.IsTateRing.isOpenMap_linearCombination`: a finite spanning family presents the
  module as an **open** quotient of `ι → A`, which is the strict-presentation form the
  Banach-theorem arguments consume.
* `TauCeti.Huber.IsTateRing.isQuotientMap_linearCombination`: the same presentation induces the
  quotient topology, pairing with the above as `isQuotientMap` pairs with `isOpenMap`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Theorem 6.16.
* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647).
-/

public section

open Filter Topology
open scoped Uniformity

namespace TauCeti.Huber

variable {A M N : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [(𝓤 M).IsCountablyGenerated] [NonarchimedeanAddGroup M] [Module A M] [ContinuousSMul A M]
  [AddCommGroup N] [UniformSpace N] [IsUniformAddGroup N] [CompleteSpace N]
  [(𝓤 N).IsCountablyGenerated] [T0Space N] [Module A N] [ContinuousConstSMul A N]

/-- **The open mapping theorem over a Tate ring.** A surjective `A`-linear map that is continuous
at zero, from a complete pseudometrisable topological `A`-module onto a complete metrisable one, is
open, when `A` is a Tate ring and the source is nonarchimedean.

Only the target carries `T0Space`, so only the target is metrisable rather than pseudometrisable;
the source is never asked to be separated because the proof does not use it.

This is `TauCeti.HasZeroSequenceOfUnits.isOpenMap` with its hypotheses discharged: it is the
general theorem that does the work, and this is the named instantiation the roadmap asks for.
Metrisability appears as a countably generated uniformity rather than as a metric, which is both
the weaker hypothesis and the vocabulary Henkel's own statement is phrased in.

Continuity is asked at zero only; a consumer holding `Continuous f` passes its `.continuousAt`. -/
theorem IsTateRing.isOpenMap (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hfc : ContinuousAt (f : M → N) 0) : IsOpenMap (f : M → N) :=
  HasZeroSequenceOfUnits.isOpenMap f hf hfc
    fun _ ↦ (continuous_id.smul continuous_const).continuousAt

/-- **The quotient form over a Tate ring.** Under exactly the hypotheses of
`TauCeti.Huber.IsTateRing.isOpenMap`, the map does not merely carry open sets to open sets: the
topology of `N` is the one coinduced from `M`.

This is the form Wedhorn's strict morphisms will use, where what matters is not that images are
open but that the target's topology is determined by the source's. It delegates to
`TauCeti.HasZeroSequenceOfUnits.isQuotientMap`, which supplies the full continuity of `f` that the
quotient conclusion needs from continuity at zero alone. -/
theorem IsTateRing.isQuotientMap (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hfc : ContinuousAt (f : M → N) 0) : IsQuotientMap (f : M → N) :=
  HasZeroSequenceOfUnits.isQuotientMap f hf hfc
    fun _ ↦ (continuous_id.smul continuous_const).continuousAt

section LinearCombination

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [(𝓤 A).IsCountablyGenerated] [NonarchimedeanRing A] [IsTateRing A]
  {N : Type*} [AddCommGroup N] [UniformSpace N] [IsUniformAddGroup N] [CompleteSpace N]
  [(𝓤 N).IsCountablyGenerated] [T0Space N] [Module A N] [ContinuousSMul A N]
  {ι : Type*} [Fintype ι]

-- `Continuous ⇑(Fintype.linearCombination A g)` does not expose an application of the map, so
-- `simp only [Fintype.linearCombination_apply]` has nothing to rewrite; the coercion has to be
-- turned into the pointwise sum by `funext` before `continuous_finsetSum` applies.
omit [IsUniformAddGroup A] [CompleteSpace A] [(𝓤 A).IsCountablyGenerated] [NonarchimedeanRing A]
  [IsTateRing A] [CompleteSpace N] [(𝓤 N).IsCountablyGenerated] [T0Space N] in
private theorem continuous_linearCombination (g : ι → N) :
    Continuous (Fintype.linearCombination A g : (ι → A) → N) := by
  rw [show (Fintype.linearCombination A g : (ι → A) → N) = fun a ↦ ∑ i, a i • g i from
    funext (Fintype.linearCombination_apply A g)]
  exact continuous_finsetSum _ fun i _ ↦ (continuous_apply i).smul continuous_const

/-- **A finite spanning family presents `N` as an open quotient of `Aᶥ`.** The
linear-combination map `a ↦ ∑ aᵢ • gᵢ` is surjective because `g` spans and continuous because
the action is, hence open by `TauCeti.Huber.IsTateRing.isOpenMap`.

Openness is the content. It is what turns "every element of `N` is a combination of the `gᵢ`" into
"every *small* element is a combination with *small* coefficients", and that quantitative form is
what the Banach-theorem arguments over a Tate ring consume. This is an ingredient for the
BGR §3.7.2/1 density argument on the route to Wedhorn 6.17/6.18, not that argument itself.

Nothing is asked of `g` beyond spanning; the hypotheses are `TauCeti.Huber.IsTateRing.isOpenMap`'s,
with the source instantiated at `ι → A` — which is where `A`'s own completeness, countably
generated uniformity and nonarchimedean structure are spent, since the `Pi` instances carry each
of them to `ι → A`. -/
theorem IsTateRing.isOpenMap_linearCombination (g : ι → N)
    (hspan : Submodule.span A (Set.range g) = ⊤) :
    IsOpenMap (Fintype.linearCombination A g : (ι → A) → N) :=
  IsTateRing.isOpenMap _ (span_range_eq_top_iff_surjective_fintypeLinearCombination A g |>.mp hspan)
    (continuous_linearCombination g).continuousAt

/-- **The quotient form of `TauCeti.Huber.IsTateRing.isOpenMap_linearCombination`.** A finite
spanning family does not merely present `N` as an open image of `ι → A`: the topology of `N` is
the one coinduced along the linear-combination map.

This is the pairing that `TauCeti.Huber.IsTateRing.isQuotientMap` makes with
`TauCeti.Huber.IsTateRing.isOpenMap`, at the named finite-presentation API. -/
theorem IsTateRing.isQuotientMap_linearCombination (g : ι → N)
    (hspan : Submodule.span A (Set.range g) = ⊤) :
    IsQuotientMap (Fintype.linearCombination A g : (ι → A) → N) :=
  IsTateRing.isQuotientMap _
    (span_range_eq_top_iff_surjective_fintypeLinearCombination A g |>.mp hspan)
    (continuous_linearCombination g).continuousAt

end LinearCombination

end TauCeti.Huber

end
