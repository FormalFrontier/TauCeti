/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Henselian

/-!
# The ring of integers of a single adic completion

The ring of integers `𝒪_v` of the completion `K_v` of the fraction field of a Dedekind domain `R`
at a height-one prime `v` is a local ring, and this file collects what it is: its maximal ideal
contracts to `v` itself, its ideal filtration is the valuation filtration `K_v` induces on it, and
in the subspace topology it is a complete `𝔪`-adic — hence Henselian — local ring.

Everything here concerns one completion. The comparison of two completions along an extension
`w ∣ v` is `TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.under_maximalIdeal_adicCompletionIntegers`: `v` is the
  prime lying under the maximal ideal of `𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.mem_maximalIdeal_pow_iff`: membership in `𝔪 ^ n` is the
  valuation bound `≤ exp (-n)`, identifying the ideal filtration with the valuation filtration.
* `IsDedekindDomain.HeightOneSpectrum.isAdic_maximalIdeal_adicCompletionIntegers`: the subspace
  topology on `𝒪_v` is the `𝔪`-adic one.
* `IsDedekindDomain.HeightOneSpectrum.henselianLocalRing_adicCompletionIntegers`: `𝒪_v` is a
  Henselian local ring, being local and complete for its maximal ideal.

## Implementation notes

`Mathlib.NumberTheory.NumberField.Completion.FinitePlace` supplies two instances used throughout —
`IsDiscreteValuationRing (v.adicCompletionIntegers K)` and
`(Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsRankOneDiscrete`. Both are stated there for an
arbitrary Dedekind domain and its fraction field, not for number fields, so nothing here depends on
number-field theory; they simply live in that module upstream. This note records the reason so the
placement of a `NumberTheory` import inside `RingTheory` is not mistaken for a layering slip.

## Motivation

These results are consumed by a semilocal comparison in explicit `2`-descent, which matches a
square class of a global étale algebra with its images in the completions. Nothing here mentions
a curve — each statement is about a Dedekind domain and one of its completions.

## Provenance

Adapted, with the author's proof, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean` line 594, and
`EllipticCurves/Mathlib/AdicCompletionExtension.lean` for the filtration and Henselian results.
The source states the contraction with `Ideal.comap` of an `algebraMap`; Mathlib spells that
`Ideal.under`, which is used here.
-/

public section

open WithZero

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

section SingleCompletion

variable (v : HeightOneSpectrum R)

/-- An irreducible element of the ring of integers of a completion has valuation `exp (-1)`. -/
theorem valued_algebraMap_eq_exp_neg_one_of_irreducible {π : v.adicCompletionIntegers K}
    (hπ : Irreducible π) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) = exp (-1) := by
  -- `v.adicCompletionIntegers K` is by definition `Valued.v.valuationSubring`, which is what lets
  -- `π`'s maximal ideal be retyped as an ideal of the valuation subring here.
  have hgen : IsLocalRing.maximalIdeal (Valued.v : Valuation (v.adicCompletion K)
      ℤᵐ⁰).valuationSubring = Ideal.span {π} := hπ.maximalIdeal_eq
  have huni := Valuation.isUniformizer_of_maximalIdeal_eq_span
    (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) hgen
  rwa [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective K)] at huni

/-- An element of `𝒪_v` lies in the `n`-th power of the maximal ideal exactly when its valuation
is at most `exp (-n)`.

This identifies the ideal filtration of `𝒪_v` with the valuation filtration it inherits from
`K_v`, which is what makes the subspace topology visibly `𝔪`-adic below. -/
@[simp]
theorem mem_maximalIdeal_pow_iff {x : v.adicCompletionIntegers K} {n : ℕ} :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔
      Valued.v (x : v.adicCompletion K) ≤ exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hint := Valuation.valuationSubring.integers (v := (Valued.v : Valuation
    (v.adicCompletion K) ℤᵐ⁰))
  have hπn : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) ^ n =
      exp (-(n : ℤ)) := by
    rw [v.valued_algebraMap_eq_exp_neg_one_of_irreducible hπ, ← exp_nsmul]
    simp
  rw [← hπn]
  exact Set.ext_iff.mp (hint.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow hπ n) x

/-! ### `𝒪_v` is a complete adic Henselian local ring

The subspace topology `𝒪_v` inherits from `K_v` is the `𝔪`-adic one, and `𝒪_v` is closed in the
complete field `K_v`, hence complete. Being complete for the `𝔪`-adic topology it is `𝔪`-adically
complete, and a local ring that is complete with respect to its maximal ideal is Henselian.
-/

/-- The ring of integers of an adic completion is a topological ring, as a subring of `K_v`. -/
instance isTopologicalRing_adicCompletionIntegers :
    IsTopologicalRing (v.adicCompletionIntegers K) :=
  inferInstanceAs (IsTopologicalRing
    (Valued.v (R := v.adicCompletion K)).valuationSubring.toSubring)

/-- **Each power of the maximal ideal of `𝒪_v` is open**: `𝔪 ^ n` is the preimage under the
inclusion `𝒪_v → K_v` of a closed valuation ball, and those are open. -/
theorem isOpen_maximalIdeal_pow_adicCompletionIntegers (n : ℕ) :
    IsOpen ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
      Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) := by
  obtain ⟨z, hz⟩ := v.valuedAdicCompletion_surjective K (exp (-(n : ℤ)))
  have hr0 : Valued.v.restrict z ≠ 0 := by
    intro h
    have h0 : Valued.v z = 0 := by rw [← Valuation.embedding_restrict, h, map_zero]
    rw [hz] at h0
    exact exp_ne_zero h0
  have : ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
        Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) =
      (fun x : v.adicCompletionIntegers K ↦ (x : v.adicCompletion K)) ⁻¹'
        {y | Valued.v.restrict y ≤ Valued.v.restrict z} := by
    ext x
    rw [Set.mem_preimage, Set.mem_ofPred, Valuation.restrict_le_iff_le_embedding,
      Valuation.embedding_restrict, hz]
    exact v.mem_maximalIdeal_pow_iff (K := K)
  rw [this]
  exact (Valued.isOpen_closedBall _ hr0).preimage continuous_subtype_val

/-- **Every neighbourhood of `0` in `𝒪_v` contains a power of the maximal ideal.** A neighbourhood
is cut out by a valuation bound, and `exp` takes some integer below that bound; the corresponding
`𝔪 ^ n` is then undercut by it. -/
theorem exists_maximalIdeal_pow_subset_of_mem_nhds {s : Set (v.adicCompletionIntegers K)}
    (hs : s ∈ nhds 0) : ∃ n : ℕ, ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
      Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) ⊆ s := by
  obtain ⟨t, ht, hts⟩ := mem_nhds_subtype _ _ _ |>.mp hs
  rw [ZeroMemClass.coe_zero] at ht
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp ht
  obtain ⟨m, hm⟩ : ∃ m : ℤ, exp m < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    refine ⟨log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) - 1, ?_⟩
    conv_rhs => rw [← exp_log (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)]
    exact exp_lt_exp.mpr (by lia)
  refine ⟨(-m).toNat, fun x hx ↦ hts ?_⟩
  refine Set.mem_preimage.mpr (hγ ?_)
  have h1 := v.mem_maximalIdeal_pow_iff (K := K) |>.mp hx
  refine Set.mem_ofPred.mpr ((Valuation.restrict_lt_iff_lt_embedding (v := Valued.v)).mpr
    (h1.trans_lt ?_))
  calc exp (-(((-m).toNat : ℤ))) ≤ exp m := exp_le_exp.mpr (by lia)
    _ < _ := hm

/-- The subspace topology on the ring of integers `𝒪_v` of an adic completion is the `𝔪`-adic
topology of its maximal ideal. -/
theorem isAdic_maximalIdeal_adicCompletionIntegers :
    IsAdic (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :=
  isAdic_iff.mpr ⟨isOpen_maximalIdeal_pow_adicCompletionIntegers (K := K) v,
    fun _ hs ↦ exists_maximalIdeal_pow_subset_of_mem_nhds (K := K) v hs⟩

/-- `𝒪_v` is complete: it is a closed subset of the complete field `K_v`. -/
instance completeSpace_adicCompletionIntegers : CompleteSpace (v.adicCompletionIntegers K) :=
  (Valued.isClosed_valuationSubring (v.adicCompletion K)).completeSpace_coe

/-- `𝒪_v` is a uniform additive group, as an additive subgroup of `K_v`. -/
instance isUniformAddGroup_adicCompletionIntegers :
    IsUniformAddGroup (v.adicCompletionIntegers K) :=
  ((Valued.v (R := v.adicCompletion K)).valuationSubring.toSubring.toAddSubgroup).isUniformAddGroup

/-- `𝒪_v` is `𝔪`-adically complete: its topology is the `𝔪`-adic one and it is complete. -/
instance isAdicComplete_adicCompletionIntegers :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) :=
  -- `IsAdic` unfolds to an equality of topologies, so dot notation on it would resolve against
  -- `Eq`; the lemma is `protected` and must be named in full.
  (IsAdic.isAdicComplete_iff (v.isAdic_maximalIdeal_adicCompletionIntegers (K := K))).mpr
    ⟨inferInstance, inferInstance⟩

/-- **The ring of integers of an adic completion is a Henselian local ring.** It is a local ring
that is complete with respect to its maximal ideal, and such rings are Henselian. -/
instance henselianLocalRing_adicCompletionIntegers :
    HenselianLocalRing (v.adicCompletionIntegers K) where
  is_henselian f hf a₀ h₁ h₂ :=
    (IsAdicComplete.henselianRing _
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))).is_henselian f hf a₀ h₁ (h₂.map _)

end SingleCompletion

end IsDedekindDomain.HeightOneSpectrum

end
