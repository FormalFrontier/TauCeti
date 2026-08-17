/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Basic

/-!
# `A⟨T/s⟩` is a complete separated topological ring

The adic structure presheaf (roadmap Layer 3.3) is to assign `A⟨T/s⟩` to the rational subset
`R(T/s)`, and its values are required to be *complete separated* topological rings (*Adic Spaces*,
arXiv:1910.05934v1, §8.1–§8.2). This module supplies the codomain fact that assignment will need:
it exhibits `A⟨T/s⟩` as an object of `CompleteSeparatedTopCommRingCat`.

No presheaf exists yet, and what is built here is not one of its values but a *presentationwise*
object: it depends on the data `(T, s, S, hden)` presenting the localization, not only on the
subset `R(T/s)`. Showing that different presentations of the same rational subset give isomorphic
objects, and constructing the restriction maps, are both later work.

Nothing here is deep — `A⟨T/s⟩` is a separated completion, so it is complete and Hausdorff for its
own uniformity, and `CompleteSeparatedTopCommRingCat.of` bundles exactly that. What the module
supplies is the *bookkeeping*: `locTopology` is not an instance, so the uniform structures on `Aₛ`
are not in scope by inference, and a consumer would otherwise repeat the three-declaration preamble
`locUniformSpace`, `isUniformAddGroup_locUniformSpace`, `isTopologicalRing_locUniformSpace` at
every use. The definition below carries it once.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.completionLocObj` : `A⟨T/s⟩` as an object of
  `CompleteSeparatedTopCommRingCat`, presentationwise in `(T, s, S, hden)`.

## Main results

* `TauCeti.Huber.PairOfDefinition.completionLocObj_obj` : the underlying `TopCommRingCat` of that
  object is `UniformSpace.Completion S` with the topology `locUniformSpace` induces.

## Provenance

The packaging here is this repository's own, built on the localisation topology of
`LocalizationTopology.Basic`, which is the AINTLIB port — see that module's Provenance section for
the source file and commit. AINTLIB's own structure-presheaf files supplied nothing here: it
carries the codomain fact inside its presheaf construction rather than as a separate object, so
there was nothing at this granularity to port.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1–§8.2, where the structure
  presheaf of an adic space is built with complete separated topological rings as its codomain.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition and Definition 5.51, §5.6, for `A⟨T/s⟩`
  itself, which `LocalizationTopology.Completion` constructs.
-/

namespace TauCeti.Huber

open TauCeti.TopCommRingCat

public section

variable {A : Type*} [CommRing A] [TopologicalSpace A]

namespace PairOfDefinition

/-! ### `A⟨T/s⟩` as an object of `CompleteSeparatedTopCommRingCat` -/

/-- **`A⟨T/s⟩` as an object of `CompleteSeparatedTopCommRingCat`**: the separated completion of
`Aₛ` under `locTopology`, which is complete and Hausdorff for its own uniformity.

This is the object the adic structure presheaf is intended to take on the rational subset
`R(T/s)`; it is presentationwise, depending on `(T, s, S, hden)` and not yet known to depend only
on `R(T/s)`, and the restriction maps are later work.

`completionLocObj_obj` identifies the underlying object; the body is not exported, so that is how
a consumer computes with it. -/
noncomputable def completionLocObj [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) : CompleteSeparatedTopCommRingCat :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  CompleteSeparatedTopCommRingCat.of (UniformSpace.Completion S)

/-- The underlying topological ring of `completionLocObj` is `A⟨T/s⟩` itself: the completion of
`Aₛ` for the uniformity `locUniformSpace`. -/
@[simp]
theorem completionLocObj_obj [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (completionLocObj P T s S hden).obj = TopCommRingCat.of (UniformSpace.Completion S) := by
  let _ := locUniformSpace P T s S hden
  let _ := isUniformAddGroup_locUniformSpace P T s S hden
  let _ := isTopologicalRing_locUniformSpace P T s S hden
  exact CompleteSeparatedTopCommRingCat.of_obj _

end PairOfDefinition

end

end TauCeti.Huber
