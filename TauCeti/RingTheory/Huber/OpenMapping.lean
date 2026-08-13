/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.ZeroSequenceOfUnits
public import TauCeti.Topology.Algebra.OpenMapping.Henkel
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# The open mapping theorem over a Tate ring

`TauCeti.HasZeroSequenceOfUnits.isOpenMap` is Henkel's theorem in the generality it is proved in:
the scalars need only a zero sequence of units, the source is a complete first-countable
nonarchimedean group, and the target need only be Baire. This file records the form the
strict-morphism material actually consumes — a surjective linear map from a complete
pseudometrisable module onto a complete metrisable one, over a Tate ring, is open — by discharging
those hypotheses from ones a consumer can check.

The asymmetry is real and not an oversight. Both modules are asked for completeness and a countably
generated uniformity; only the *target* is asked to be `T0Space`, so only the target is metrisable.
The source is pseudometrisable, which is all Henkel needs of it, and separating the source would be
an assumption the theorem does not use.

Three of Henkel's substantive hypotheses survive the translation, and all three are stated. (The
structural binders that merely say `M` and `N` are topological modules carry across unchanged and
are not counted here.)

* `CompleteSpace M`. Nothing supplies it; completeness of the source is what
  `TauCeti.mem_image_of_mem_closure_image` needs in order to remove the closure.
* `NonarchimedeanAddGroup M`. Metrisability does not supply it, and nothing about a module over a
  Tate ring does either; it is a genuine assumption on the source.
* `T0Space N`. This is the Hausdorff hypothesis. It cannot come from the metrisability route,
  because `IsCompletelyPseudoMetrizableSpace` is *pseudo* and carries no separation.

The rest are inferred. `IsTateRing A` gives `HasZeroSequenceOfUnits A` through the powers of a
pseudouniformiser (`TauCeti.Huber.IsTateRing.hasZeroSequenceOfUnits`) — this is the only place the
Tate condition is used, and a Huber ring that is not Tate need not admit such a sequence.
Countable generation of the uniformity gives it for `𝓝 0`, which is the first countability Henkel
asks of the source.

The target's action hypothesis is `ContinuousConstSMul A N`, which is Henkel's own binder rather
than a strengthening of it. The asymmetry with `ContinuousSMul A M` on the source is not an
oversight: the source needs continuity in the *scalar* variable to discharge `hc`, whereas the
target needs only continuity in the *module* variable, and `ContinuousConstSMul` is exactly that.

The target's completeness deserves a word, since it is not what one would guess Henkel needs.
Henkel asks the target to be a **Baire** space, and completeness plus a countably generated
uniformity is how that is obtained here: the two together make `N` completely pseudometrisable
(`IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable`), and a completely
pseudometrisable space is Baire by the first Baire category theorem. So `CompleteSpace N` is not
removable without putting a Baire hypothesis back in its place.

Continuity is asked only at zero. For an additive map out of a topological group that is
equivalent to continuity everywhere (`continuous_of_continuousAt_zero`), so this is the same
hypothesis spelled at its weakest, and a consumer holding `Continuous f` supplies
`hfc.continuousAt`.

Both halves of the roadmap's derived form are here. `TauCeti.Huber.IsTateRing.isOpenMap` is the
open-map half; `TauCeti.Huber.IsTateRing.isQuotientMap` is the other — that such a map induces the
quotient topology — and it delegates to `TauCeti.HasZeroSequenceOfUnits.isQuotientMap` exactly as
the open-map form delegates to `TauCeti.HasZeroSequenceOfUnits.isOpenMap`. It is the quotient form
that the strict-morphism material consumes, since what matters there is not that images are open
but that the target's topology is determined by the source's.

## Main results

* `TauCeti.Huber.IsTateRing.isOpenMap`: a continuous surjective linear map from a complete
  pseudometrisable module onto a complete metrisable one, over a Tate ring, is open.
* `TauCeti.Huber.IsTateRing.isQuotientMap`: the same map induces the quotient topology on its
  target. This is the form the strict-morphism material consumes.

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

/-- **The open mapping theorem over a Tate ring.** A surjective `A`-linear map from a complete
pseudometrisable topological `A`-module onto a complete metrisable one is open, when `A` is a Tate
ring and the source is nonarchimedean.

Only the target carries `T0Space`, so only the target is metrisable rather than pseudometrisable;
the source is never asked to be separated because the proof does not use it.

This is `TauCeti.HasZeroSequenceOfUnits.isOpenMap` with its hypotheses discharged: it is the
general theorem that does the work, and this is the named instantiation the roadmap asks for.
Metrisability appears as a countably generated uniformity rather than as a metric, which is both
the weaker hypothesis and the vocabulary Henkel's own statement is phrased in.

Continuity is asked at zero only; `Continuous f` gives it as `hfc.continuousAt`. -/
theorem IsTateRing.isOpenMap (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hfc : ContinuousAt (f : M → N) 0) : IsOpenMap (f : M → N) :=
  HasZeroSequenceOfUnits.isOpenMap f hf hfc
    fun _ ↦ (continuous_id.smul continuous_const).continuousAt

/-- **The quotient form over a Tate ring.** Under exactly the hypotheses of
`TauCeti.Huber.IsTateRing.isOpenMap`, the map does not merely carry open sets to open sets: the
topology of `N` is the one coinduced from `M`.

This is the form Wedhorn's strict morphisms use, where what matters is not that images are open but
that the target's topology is determined by the source's. It delegates to
`TauCeti.HasZeroSequenceOfUnits.isQuotientMap`, which supplies the full continuity of `f` that the
quotient conclusion needs from continuity at zero alone. -/
theorem IsTateRing.isQuotientMap (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hfc : ContinuousAt (f : M → N) 0) : IsQuotientMap (f : M → N) :=
  HasZeroSequenceOfUnits.isQuotientMap f hf hfc
    fun _ ↦ (continuous_id.smul continuous_const).continuousAt

end TauCeti.Huber

end
