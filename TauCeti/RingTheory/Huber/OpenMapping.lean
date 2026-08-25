/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ZeroSequenceOfUnits
public import TauCeti.Topology.Algebra.OpenMapping.Henkel
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Maps.Strict.Module
import TauCeti.Topology.Algebra.IsUniformGroup.Submodule
import TauCeti.Topology.Algebra.Module.Submodule
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

Both halves of the roadmap's derived form are here, together with a strict-map form for a map
that need not be surjective. `TauCeti.Huber.IsTateRing.isOpenMap` is the
open-map half; `TauCeti.Huber.IsTateRing.isQuotientMap` is the other — that such a map induces the
quotient topology — and it delegates to `TauCeti.HasZeroSequenceOfUnits.isQuotientMap` exactly as
the open-map form delegates to `TauCeti.HasZeroSequenceOfUnits.isOpenMap`. It is the quotient form
that the strict-morphism material will consume, since what matters there is not that images are
open but that the target's topology is determined by the source's.

That quotient form is also what pins down the topology of a *finitely generated* such module. A
finite generating family presents it as a topological quotient of `Fin n → A`, and the module
topology passes along that presentation, so the module carries the module topology —
`TauCeti.Huber.IsTateRing.isModuleTopology`. Continuity of every linear map out of it is then
Mathlib's `IsModuleTopology.continuous_of_linearMap` applied to that fact, and that consequence is
the continuity conjunct of Wedhorn 6.18(2). That is where the asymmetry of this file reverses: it
is the *source* that must be complete, metrisable and finitely generated, while the target is asked
for nothing beyond a topological module structure.

## Main results

* `TauCeti.Huber.IsTateRing.isOpenMap`: a surjective linear map, continuous at zero, from a
  complete pseudometrisable module onto a complete metrisable one over a Tate ring is open.
* `TauCeti.Huber.IsTateRing.isQuotientMap`: the same map induces the quotient topology on its
  target. This is the form the strict-morphism material will consume.
* `TauCeti.Huber.IsTateRing.isStrictMap_of_isClosed_range`: a linear map continuous at zero with
  closed range is strict, i.e. open onto its image. An ingredient for Wedhorn 6.18(2), not that
  proposition — see its docstring.
* `TauCeti.Huber.IsTateRing.isOpenMap_linearCombination`: a finite spanning family presents the
  module as an **open** quotient of `ι → A`, which is the strict-presentation form the
  Banach-theorem arguments consume.
* `TauCeti.Huber.IsTateRing.isQuotientMap_linearCombination`: the same presentation induces the
  quotient topology, pairing with the above as `isQuotientMap` pairs with `isOpenMap`.
* `TauCeti.Huber.IsTateRing.isModuleTopology`: a module-finite complete metrisable module carries
  the module topology, so its topology is determined by that of `A`. Feeding it to Mathlib's
  `IsModuleTopology.continuous_of_linearMap` is the continuity conjunct of Wedhorn 6.18(2): a
  linear map out of such a module is continuous, with no continuity hypothesis on the map and
  nothing asked of the target beyond a topological module structure. See its docstring for what
  separates that consequence from 6.18(2) itself.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Theorem 6.16 and Proposition 6.18(2). The proposition
  is not proved here in full. It assumes `A` noetherian and both modules finitely generated with
  the topology of 6.18(1), and concludes continuity as well as openness onto the image; what is
  here is its two conjuncts separately, each under hypotheses of its own.
  `TauCeti.Huber.IsTateRing.isModuleTopology` yields the continuity conjunct, which needs neither
  the noetherian hypothesis nor a topology of 6.18(1) on the target.
  `TauCeti.Huber.IsTateRing.isStrictMap_of_isClosed_range` is the openness conjunct, and takes a
  closed range as a hypothesis in place of what the noetherian finitely generated setting supplies.
  Assembling the two into 6.18(2) itself needs that missing input — closedness of a finitely
  generated submodule — which is not in this file.
* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647).

## Provenance

`TauCeti.Huber.IsTateRing.isModuleTopology` is adapted from the AINTLIB project
(Chris Birkbeck, Apache-2.0), `projects/AdicSpaces/Adic spaces/WedhornBanachTheorem.lean` at commit
`37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`, whose private
`continuous_of_moduleFinite_of_topNilpUnit` (lines 1113-1149) proves the continuity consequence by
the same route: present the source as a topological quotient along a finite generating family, then
transfer continuity across the quotient.

The proof is not transcribed, and the route is only the same as far as the presentation. There the
presentation map is built by hand, its openness is discharged by a `wedhorn_6_16_of_topNilpUnit`
that this repository does not have, and continuity is then pushed across the quotient by hand, in
twenty-five lines. Here the presentation is
`TauCeti.Huber.IsTateRing.isQuotientMap_linearCombination` above, and what is transferred is not
continuity of one map but the module topology itself, after which every linear map out of the source
is continuous by Mathlib's `IsModuleTopology.continuous_of_linearMap`. The hypotheses differ too:
the topologically nilpotent unit is supplied by `[IsTateRing A]` rather than taken as an explicit
argument, and in the consequence the target is asked only to be a topological `A`-module, where the
source lemma asks it to be complete, separated and countably uniform.

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

/-- **Strictness from a closed range over a Tate ring.** An `A`-linear map that is continuous at
zero and has closed range is a strict map: `Topology.IsStrictMap`, Bourbaki's "open onto its
image". Surjectivity is not assumed.

This is **not** Wedhorn Proposition 6.18(2), which assumes `A` noetherian and `M`, `N` finitely
generated with the canonical topology of 6.18(1), and *concludes* both continuity and openness onto
the image. Here continuity is a hypothesis and the closed-range hypothesis stands in for what the
noetherian finitely generated setting would supply. It is the openness conjunct of 6.18(2) as a
free-standing lemma, and an ingredient for it rather than the proposition.

Closedness of the range is the weaker of the two natural hypotheses: an open submodule is closed,
so a map with *open* range satisfies it too. Consumers recover the openness of `f.rangeRestrict`
from `LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict` and `IsOpenQuotientMap.isOpenMap`,
and the first-isomorphism homeomorphism from
`LinearMap.isStrictMap_iff_isHomeomorph_quotKerEquivRange`. Note `LinearMap.quotKerEquivRange`
on its own is only a linear equivalence, carrying no topology. -/
theorem IsTateRing.isStrictMap_of_isClosed_range (f : M →ₗ[A] N)
    (hfc : ContinuousAt (f : M → N) 0)
    (hr : IsClosed ((LinearMap.range f : Submodule A N) : Set N)) :
    Topology.IsStrictMap (f : M → N) := by
  have _ : CompleteSpace (LinearMap.range f) := hr.completeSpace_coe
  have hcont : Continuous (f.rangeRestrict : M → LinearMap.range f) :=
    (continuous_of_continuousAt_zero f hfc).subtype_mk _
  exact LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mpr
    ⟨f.surjective_rangeRestrict, hcont,
      IsTateRing.isOpenMap f.rangeRestrict f.surjective_rangeRestrict hcont.continuousAt⟩

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
    (IsModuleTopology.continuous_of_linearMap (Fintype.linearCombination A g)).continuousAt

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
    (IsModuleTopology.continuous_of_linearMap (Fintype.linearCombination A g)).continuousAt

end LinearCombination

section ModuleFinite

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [(𝓤 A).IsCountablyGenerated] [NonarchimedeanRing A] [IsTateRing A]
  {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [(𝓤 M).IsCountablyGenerated] [T0Space M] [Module A M] [ContinuousSMul A M] [Module.Finite A M]

/-- **A module-finite complete metrisable module over a Tate ring carries the module topology.**
That is: the topology `M` was given is already the finest one making it a topological `A`-module,
so nothing about `M`'s topology is left free once `A`'s is fixed.

This is the one reason `TauCeti.Huber.IsTateRing.isQuotientMap_linearCombination` is stated as a
quotient map rather than merely an open one. A finite generating family presents `M` as a
topological quotient of `Fin n → A`; the source of that presentation carries the module topology,
because `A` does over itself and Mathlib's `IsModuleTopology.instPi` carries that to a finite
product; and the module topology passes along a surjection, which is
`ModuleTopology.eq_coinduced_of_surjective`. Comparing the two descriptions of `M`'s topology as a
coinduced one gives the claim.

It is stated as a theorem rather than an instance deliberately. Its conclusion
`IsModuleTopology A M` has no discriminating head, so as an instance it would be tried on every
module-topology goal in every file that transitively imports this one, each attempt dragging in a
search for `IsTateRing`, `CompleteSpace` and `Module.Finite`. Call it explicitly, as
`have := IsTateRing.isModuleTopology (A := A) (M := M)`.

The **continuity conjunct** of Wedhorn Proposition 6.18(2) is the immediate consequence: with that
in scope, `IsModuleTopology.continuous_of_linearMap f` gives `Continuous f` for every linear
`f : M →ₗ[A] N` into every topological `A`-module `N`, with no continuity hypothesis on `f` —
finiteness of the source is what supplies it. Two hypotheses of 6.18(2) are absent from that
consequence, and their absence is the content. `A` is **not** asked to be noetherian: that
hypothesis is spent entirely on closedness of the range, which continuity does not need. And the
target is asked only to be a topological `A`-module — no completeness, no separation, no countably
generated uniformity, not even a uniform structure. Both are genuine weakenings, not oversights;
the source carries the whole burden, as it must, since it is the source being finitely generated
that makes the quotient presentation available. The openness conjunct of 6.18(2) is
`TauCeti.Huber.IsTateRing.isStrictMap_of_isClosed_range`, which still takes as a hypothesis the
closed range that the noetherian finitely generated setting would supply.

Mathlib's `LinearMap.continuous_of_finiteDimensional` is the same phenomenon over a complete
nontrivially normed field, where finite-dimensionality plays the role finite generation plays here;
neither statement subsumes the other, since a Tate ring need not be a field. -/
theorem IsTateRing.isModuleTopology : IsModuleTopology A M := by
  obtain ⟨n, g, hspan⟩ := Module.Finite.exists_fin (R := A) (M := M)
  exact ⟨(IsTateRing.isQuotientMap_linearCombination g hspan).eq_coinduced.trans
    (ModuleTopology.eq_coinduced_of_surjective
      (span_range_eq_top_iff_surjective_fintypeLinearCombination A g |>.mp hspan)).symm⟩

end ModuleFinite

end TauCeti.Huber

end
