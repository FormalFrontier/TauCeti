/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

public section

/-!
# Flipping a root pairing transposes its Cartan matrix

Mathlib's `RootPairing.flip` interchanges the roots and the coroots of a root pairing, and
`RootPairing.Base.flip` records that a base of `P` is a base of `P.flip` supported on the same
simple indices. Interchanging the two sides transposes every pairing `⟨αᵢ, αⱼ^∨⟩`
(`RootPairing.pairing_flip`); this file carries that transposition across the integral structure
and the Cartan matrix of a base, which is where flipping is used.

## Main definitions

* `TauCeti.RootPairing.Base.flipSupportEquiv`: the identification of the support of a base with the
  support of its flip, which the two Cartan matrices are indexed by.

## Main results

* `TauCeti.RootPairing.pairingIn_flip`: flipping transposes the *chosen* preimage of a pairing in
  the coefficient ring `S`, not only the pairing itself.
* `TauCeti.RootPairing.Base.cartanMatrix_flip`: the Cartan matrix of the flipped base is the
  transpose of the Cartan matrix of the base.

## References

This file supplies the root-pairing half of the duality item of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, which records that
`DynkinType.cartanMatrix (.B n)` is the transpose of `DynkinType.cartanMatrix (.C n)` and that the
two types are "identified only after `flip` (duality)"; the classification side of that item is
`TauCeti.LinearAlgebra.RootSystem.Duality`.
-/

namespace TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

/-- **Flipping a root pairing transposes its integral pairing.** The pairing of the flipped pairing
is transposed by definition (`RootPairing.pairing_flip`); the content here is that the *chosen*
preimage in `S` is transposed too, which needs `algebraMap S R` to be injective. -/
@[simp] lemma pairingIn_flip (S : Type*) [CommRing S] [Algebra S R] [FaithfulSMul S R]
    (P : RootPairing ι R M N) [P.IsValuedIn S] (i j : ι) :
    P.flip.pairingIn S i j = P.pairingIn S j i :=
  FaithfulSMul.algebraMap_injective S R <| by simp

namespace Base

/-- A base of `P` is a base of `P.flip` supported on the same simple indices
(`RootPairing.Base.flip`); this is the resulting identification of the two index types, which the
Cartan matrices of the base and of its flip are indexed by. -/
def flipSupportEquiv {P : RootPairing ι R M N} (b : P.Base) : b.flip.support ≃ b.support :=
  Equiv.subtypeEquivRight fun _ ↦ by rw [RootPairing.Base.flip_support]

@[simp] lemma coe_flipSupportEquiv_apply {P : RootPairing ι R M N} (b : P.Base)
    (i : b.flip.support) :
    (flipSupportEquiv b i : ι) = i := (rfl)

/-- **The Cartan matrix of the flipped base is the transpose of the Cartan matrix of the base.** -/
@[simp] lemma cartanMatrix_flip [CharZero R] {P : RootPairing ι R M N} [P.IsCrystallographic]
    (b : P.Base) (i j : b.flip.support) :
    b.flip.cartanMatrix i j = b.cartanMatrix (flipSupportEquiv b j) (flipSupportEquiv b i) := by
  have h₁ : b.flip.cartanMatrix i j = P.flip.pairingIn ℤ (i : ι) (j : ι) :=
    RootPairing.Base.cartanMatrixIn_def _ _ _ _
  have h₂ : b.cartanMatrix (flipSupportEquiv b j) (flipSupportEquiv b i)
      = P.pairingIn ℤ (j : ι) (i : ι) := RootPairing.Base.cartanMatrixIn_def _ _ _ _
  rw [h₁, h₂, pairingIn_flip]

/-- Flipping a base twice returns the original base. -/
@[simp] lemma flip_flip {P : RootPairing ι R M N} (b : P.Base) : b.flip.flip = b := rfl

end Base

end RootPairing

end TauCeti
