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
`TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel`; assuming the one input those generic
results do not give, finiteness of the residue field, this file records the resulting local-field
instance. For rings of integers of number fields that finiteness hypothesis is automatic.

This instance lets local-field results apply directly to the canonical finite completions used in
global arithmetic, without choosing another valuation or another completion.
-/

public section
noncomputable section

open IsDedekindDomain NumberField Valued.integer ValuativeRel

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]

/-- An adic completion with finite residue field is a nonarchimedean local field. -/
instance isNonarchimedeanLocalField_adicCompletion :
    IsNonarchimedeanLocalField (v.adicCompletion K) := by
  -- The discrete valuation admits a rank-one normalization; its chosen base does not affect the
  -- topology.
  let _ : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (by norm_num : (1 : NNReal) < 2)
  let _ : NormedField (v.adicCompletion K) :=
    Valued.toNormedField (v.adicCompletion K) ℤᵐ⁰
  -- The residue field of `𝒪_v` is `R ⧸ v`, which is finite.
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
