/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Localization.Defs
public import TauCeti.Topology.Algebra.UniformRing

/-!
# Maps out of the completion of a localisation

A continuous ring homomorphism out of the completion of a localisation `S` of `A` is determined by
its restriction to `A`. This factors into two independent steps:

* agreeing on `S` forces agreement on `Ŝ`, because `S` is dense in it — that half is about
  completions alone and lives in `TauCeti.Topology.Algebra.UniformRing` as
  `UniformSpace.Completion.ringHom_ext_of_continuous`;
* agreeing after `algebraMap A S` forces agreement on `S`, by `IsLocalization.ringHom_ext`.

Only continuity is required of the two maps, and the target need only be a semiring carrying a
Hausdorff topology — no compatibility between the topology and the ring operations is used, and
nothing is asked of the submonoid.

## Main results

* `TauCeti.completion_localization_ringHom_ext_of_continuous`: two continuous ring homomorphisms
  out of `Ŝ` agreeing on `A` are equal.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], §8, where this is the reason a map out of `A⟨T/s⟩` is
  pinned down by its restriction to `A`.
-/

public section

namespace TauCeti

open UniformSpace

/-- **Maps out of the completion of a localisation are determined on the base ring.** Two
continuous ring homomorphisms `Ŝ → B` into a semiring carrying a Hausdorff topology that agree after
composing with `A → S → Ŝ` are equal. -/
theorem completion_localization_ringHom_ext_of_continuous {A S : Type*} [CommSemiring A]
    [CommRing S] [Algebra A S] (M : Submonoid A) [IsLocalization M S]
    [UniformSpace S] [IsUniformAddGroup S] [IsTopologicalRing S]
    {B : Type*} [Semiring B] [TopologicalSpace B] [T2Space B]
    {g h : Completion S →+* B} (hg : Continuous g) (hh : Continuous h)
    (hcomp : (g.comp Completion.coeRingHom).comp (algebraMap A S)
      = (h.comp Completion.coeRingHom).comp (algebraMap A S)) : g = h :=
  Completion.ringHom_ext_of_continuous hg hh (IsLocalization.ringHom_ext M hcomp)

end TauCeti
