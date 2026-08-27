/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.BaseChange
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import TauCeti.RingTheory.Huber.ClosedSubmodule
import Mathlib.RingTheory.Flat.Tensor

/-!
# `A⟨T₁, …, Tₖ⟩` is faithfully flat over a complete noetherian Tate ring

Wedhorn's Lemma 8.31(1): for a complete noetherian Tate ring `A`, the ring of restricted power
series `A⟨T₁, …, Tₖ⟩` is faithfully flat over `A`.

Flatness is Remark 8.29 applied to the ideals of `A`: for an ideal `I`, the comparison maps
identify `I ⊗[A] A⟨T⟩ → A ⊗[A] A⟨T⟩` with the coefficientwise inclusion `I⟨T⟩ → A⟨T⟩`, which is
injective, and Mathlib's `Module.Flat.iff_rTensor_injective` asks for nothing more. Faithfulness is
the prime `{∑ aᵥ Tᵛ | a₀ ∈ 𝔭}` Wedhorn writes down: the constant coefficient is a ring homomorphism
`A⟨T⟩ → A` retracting `A → A⟨T⟩`, so every prime of `A` is the contraction of a prime of `A⟨T⟩`,
and `Module.FaithfullyFlat.of_comap_surjective` concludes.

## Main results

* `TauCeti.Huber.flat_restrictedMvPowerSeriesSubring`: `A⟨T₁, …, Tₖ⟩` is flat over `A`.
* `TauCeti.Huber.faithfullyFlat_restrictedMvPowerSeriesSubring`: it is faithfully flat.

## Implementation notes

For an ideal `I` of `A`, Remark 8.29 (`restrictedMvPowerSeriesBaseChange_bijective`) is applied to
`I` with its subspace topology: `I` is closed (`isClosed_of_isNoetherian`), hence complete, hence
carries the module topology (`IsTateRing.isModuleTopology`). Faithfulness goes through
`Module.FaithfullyFlat.of_comap_surjective`, with the constant coefficient
`MvPowerSeries.constantCoeff ∘ restrictedMvPowerSeriesSubringVal` as the ring homomorphism whose
`comap` sections `Spec (A⟨T⟩) → Spec A`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Lemma 8.31.
-/

open Filter Topology
open scoped Uniformity

public section

namespace TauCeti.Huber

variable {k : ℕ} {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [(𝓤 A).IsCountablyGenerated] [T0Space A] [NonarchimedeanRing A] [IsTateRing A]
  [IsNoetherianRing A]

/-- **`A⟨T₁, …, Tₖ⟩` is flat over a complete noetherian Tate ring** (Wedhorn, Lemma 8.31(1)). -/
theorem flat_restrictedMvPowerSeriesSubring :
    Module.Flat A (restrictedMvPowerSeriesSubring k A) := by
  rw [Module.Flat.iff_rTensor_injective]
  intro I _
  -- An ideal of a noetherian complete Tate ring is closed, so with its subspace topology it is a
  -- finite complete metrisable module, hence carries the module topology and Remark 8.29 applies.
  have : CompleteSpace I := (isClosed_of_isNoetherian I).completeSpace_coe
  have : Module.Finite A I := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian I)
  have : IsModuleTopology A I := IsTateRing.isModuleTopology
  have hι : ContinuousAt (I.subtype : I → A) 0 := continuous_subtype_val.continuousAt
  intro x y hxy
  apply (restrictedMvPowerSeriesBaseChange_bijective (k := k) (A := A) (M := I)).injective
  apply restrictedMvPowerSeriesSubmoduleMap_injective (k := k) I.subtype hι I.injective_subtype
  rw [restrictedMvPowerSeriesSubmoduleMap_baseChange,
    restrictedMvPowerSeriesSubmoduleMap_baseChange]
  exact congrArg _ hxy

/-- **`A⟨T₁, …, Tₖ⟩` is faithfully flat over a complete noetherian Tate ring** (Wedhorn,
Lemma 8.31(1)). -/
theorem faithfullyFlat_restrictedMvPowerSeriesSubring :
    Module.FaithfullyFlat A (restrictedMvPowerSeriesSubring k A) := by
  have := flat_restrictedMvPowerSeriesSubring (k := k) (A := A)
  -- The constant coefficient retracts `algebraMap`, so `comap` along it sections `Spec`.
  set c : restrictedMvPowerSeriesSubring k A →+* A :=
    (MvPowerSeries.constantCoeff (σ := Fin k) (R := A)).comp
      restrictedMvPowerSeriesSubringVal.toRingHom with hc
  have hsect : c.comp (algebraMap A (restrictedMvPowerSeriesSubring k A)) = RingHom.id A := by
    ext a
    simp [hc, MvPowerSeries.algebraMap_apply]
  refine Module.FaithfullyFlat.of_comap_surjective fun p ↦ ⟨PrimeSpectrum.comap c p, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply, hsect, PrimeSpectrum.comap_id]

end TauCeti.Huber
