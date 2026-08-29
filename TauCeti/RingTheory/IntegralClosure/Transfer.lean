/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Transport principles for integral closures and their finiteness

Two general facts that the finiteness of integral closures is assembled from, each stated in the
abstract typeclass form `IsIntegralClosure`, and independent of each other.

* Descending the base: an integral closure of `A` in `B` is also the integral closure of `R` in
  `B` when `A` is integral over `R` — the converse of Mathlib's `IsIntegralClosure.tower_top`,
  and Stacks, Lemma 10.36.16 (tag 0308).
* Descending along an embedding: if the integral closure of `A` in a bigger ring is a finite
  module over the Noetherian ring `A`, so is the integral closure in a ring that embeds into it —
  the "as `R` is Noetherian it suffices to enlarge the field" step that Stacks uses in
  Lemmas 10.161.5, 10.161.12 and 10.161.13.

## Main results

* `TauCeti.IsIntegralClosure.tower_bot`: the integral closure of `A` in `B` is the integral
  closure of `R` in `B` when `A` is integral over `R`.
* `TauCeti.IsIntegralClosure.finite_of_injective`: finiteness of an integral closure descends
  along an injective `A`-algebra map of the top rings, over a Noetherian `A`.

## Provenance

Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and isogenies*
(`TauCetiRoadmap/EllipticCurves/README.md:1096`), through the support module
`RingTheory/IntegralClosure/NormalizationFinite`. The statements are Stacks, Lemmas 10.36.16
and 10.36.15(2) (tags 0308, 02JM; "Proof. Omitted") and the Noetherian reduction sentence of
Stacks 10.161.12 (tag 032N). The fraction-field sentence of Stacks 10.161.5 (tag 032I) is
generic localization material and lives in
`TauCeti/RingTheory/Localization/FiniteDimensional.lean`.
-/

public section

namespace TauCeti

/-- Source: Stacks, Lemma 10.36.16 (tag 0308): "Let `A → B → C` be ring maps. Let `B′` be the
integral closure of `A` in `B`, let `C′` be the integral closure of `B′` in `C`. Then `C′` is
the integral closure of `A` in `C`." Here in the form used by normalization-finiteness: if `C` is
the integral closure of `A` in `B` and `A` is integral over `R`, then `C` is the integral closure
of `R` in `B`. The converse of Mathlib's `IsIntegralClosure.tower_top`. -/
theorem IsIntegralClosure.tower_bot {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B]
    [CommSemiring C] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra C B] [IsScalarTower R A B]
    [IsIntegralClosure C A B] [Algebra.IsIntegral R A] : IsIntegralClosure C R B := by
  refine ⟨IsIntegralClosure.algebraMap_injective C A B, fun {x} ↦ ⟨fun hx ↦ ?_, fun hy ↦ ?_⟩⟩
  · -- integral over `R` ⇒ integral over `A`, so it is hit by `C`
    exact (IsIntegralClosure.isIntegral_iff (A := C) (R := A)).mp hx.tower_top
  · -- hit by `C` ⇒ integral over `A`, and `A` is integral over `R`
    exact isIntegral_trans x ((IsIntegralClosure.isIntegral_iff (A := C) (R := A)).mpr hy)

/-- Source: Stacks, Lemma 10.161.12 (tag 032N), proof: "Choose a finite normal field extension
`M/K` containing `L`. As `R` is Noetherian it suffices to show that the integral closure of `R`
in `M` is finite over `R`." Finiteness of integral closures descends along injective `A`-algebra
maps of the top rings. -/
theorem IsIntegralClosure.finite_of_injective {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M K' : Type*} [CommRing M] [CommRing K'] [Algebra A M] [Algebra A K'] {C C' : Type*}
    [CommRing C] [CommRing C'] [Algebra A C] [Algebra C M] [IsScalarTower A C M]
    [IsIntegralClosure C A M] [Algebra A C'] [Algebra C' K'] [IsScalarTower A C' K']
    [IsIntegralClosure C' A K'] [Module.Finite A C'] (ι : M →ₐ[A] K')
    (hι : Function.Injective ι) : Module.Finite A C := by
  -- `C → M → K'` makes `C` an algebra over which `IsIntegralClosure.lift` can land in `C'`
  let _ : Algebra C K' := (ι.toRingHom.comp (algebraMap C M)).toAlgebra
  have : IsScalarTower A C K' := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply A C M a]
    exact (ι.commutes a).symm
  have : Algebra.IsIntegral A C := ⟨fun x ↦ IsIntegralClosure.isIntegral A M x⟩
  have hinj : Function.Injective (IsIntegralClosure.lift (S := C) A C' K') := fun a b hab ↦ by
    refine IsIntegralClosure.algebraMap_injective C A M (hι ?_)
    have h := congrArg (algebraMap C' K') hab
    rwa [IsIntegralClosure.algebraMap_lift, IsIntegralClosure.algebraMap_lift] at h
  exact Module.Finite.of_injective
    (IsIntegralClosure.lift (S := C) A C' K').toLinearMap hinj

end TauCeti
