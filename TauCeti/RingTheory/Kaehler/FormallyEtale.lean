/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Etale.Kaehler

/-!
# Bases of Kähler differentials along a formally étale extension

For a tower `R → S → T` with `T` formally étale over `S`, Mathlib's
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` identifies `T ⊗[S] Ω[S⁄R]` with
`Ω[T⁄R]`. This file records what that says about bases: an `S`-basis of `Ω[S⁄R]` becomes a
`T`-basis of `Ω[T⁄R]` on the same index type, each basis vector going to its image under
`KaehlerDifferential.map`.

The motivating application is a tower of fields `k → K → F` with `F/K` separable algebraic, so
that `Algebra.FormallyEtale.of_isSeparable` supplies the hypothesis: the differentials of `F`
over `k` are then computed by those of `K` over `k`.

## Main definitions

* `TauCeti.kaehlerBasisOfFormallyEtale`: the induced basis of `Ω[T⁄R]`.
-/

public section

noncomputable section

namespace TauCeti

open Module TensorProduct

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [Algebra.FormallyEtale S T]

/-- The `T`-basis of `Ω[T⁄R]` induced by an `S`-basis of `Ω[S⁄R]`, when `T` is formally étale
over `S`. Its vectors are the images of the given ones under `KaehlerDifferential.map`, as
recorded in `TauCeti.kaehlerBasisOfFormallyEtale_apply`. -/
def kaehlerBasisOfFormallyEtale {ι : Type*} (b : Basis ι S Ω[S⁄R]) : Basis ι T Ω[T⁄R] :=
  (b.baseChange T).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T)

@[simp]
theorem kaehlerBasisOfFormallyEtale_apply {ι : Type*} (b : Basis ι S Ω[S⁄R]) (i : ι) :
    kaehlerBasisOfFormallyEtale R S T b i = KaehlerDifferential.map R R S T (b i) := by
  simp [kaehlerBasisOfFormallyEtale, KaehlerDifferential.mapBaseChange_tmul]

end TauCeti
