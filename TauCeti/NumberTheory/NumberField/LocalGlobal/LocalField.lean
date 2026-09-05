/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Finite completions of number fields are local fields

The completion of a number field at a nonzero prime ideal is a nonarchimedean local field. The
valuative relation on such a completion, its compatibility with the existing topology and its
nontriviality are supplied for an arbitrary Dedekind domain in
`TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel`; this file adds the one input those
generic results do not give, the finiteness of the residue field, and records the resulting
local-field instance.

This instance lets local-field results apply directly to the canonical finite completions used in
global arithmetic, without choosing another valuation or another completion.
-/

public section
noncomputable section

open IsDedekindDomain NumberField Valued.integer ValuativeRel

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The completion of a number field at a nonzero prime ideal is a nonarchimedean local field. -/
instance isNonarchimedeanLocalField_adicCompletion :
    IsNonarchimedeanLocalField (v.adicCompletion K) := by
  -- The residue field of `𝒪_v` is `𝓞 K ⧸ v`, which is finite.
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := K)).toEquiv
  -- Local compactness comes from Mathlib's criterion for the `Valued` structure of `K_v`. That
  -- criterion is stated for `Valued.integer`, which unfolds to `v.adicCompletionIntegers K`, so
  -- its two inputs are supplied by `inferInstanceAs` at the latter.
  let _ : ProperSpace (v.adicCompletion K) :=
    (@properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (v.adicCompletion K) ℤᵐ⁰ _ _
      (inferInstance : Valued (v.adicCompletion K) ℤᵐ⁰) inferInstance).mpr
      ⟨inferInstance,
        inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))⟩
  exact ⟨⟩

end IsDedekindDomain.HeightOneSpectrum

end
