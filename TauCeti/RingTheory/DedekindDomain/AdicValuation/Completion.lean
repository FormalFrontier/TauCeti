/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# The prime under the maximal ideal of an adic completion

The ring of integers of the completion `K_v` of the fraction field of a Dedekind domain `R` at a
height-one prime `v` is a local ring, and its maximal ideal contracts to `v` itself. This is what
identifies a condition imposed at the maximal ideal of `𝒪_v` with the condition at `v` upstairs.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.under_maximalIdeal_adicCompletionIntegers`: `v` is the
  prime lying under the maximal ideal of `𝒪_v`.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6, lines 813–822: the "Explicit 2-descent (core,
this layer)" bullet. Its semilocal half compares a square class of a global étale algebra with its
images in the completions, and this contraction is what matches the local condition to the global
prime. Nothing here mentions a curve.

## Provenance

Adapted, with the author's proof, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean` line 594. The source states the contraction with `Ideal.comap`
of an `algebraMap`; Mathlib spells that `Ideal.under`, which is used here. The source is written
against Lean `v4.32.0`; this is a forward port.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The prime of `R` lying under the maximal ideal of the ring of integers of the completion of
`K` at `v` is `v` itself. -/
@[simp]
lemma under_maximalIdeal_adicCompletionIntegers (v : HeightOneSpectrum R) :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).under R = v.asIdeal := by
  ext x
  rw [Ideal.under_def, Ideal.mem_comap, ← valuation_lt_one_iff_mem (K := K)]
  -- `v.adicCompletionIntegers K` is by definition `Valued.v.valuationSubring`, which is what lets
  -- `Valuation.mem_maximalIdeal_iff` apply here.
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
    (WithZero (Multiplicative ℤ))))).trans ?_
  rw [algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation']

end IsDedekindDomain.HeightOneSpectrum

end
