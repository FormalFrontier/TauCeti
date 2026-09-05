/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Topology.Algebra.Valued.ValuativeRel

public import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension

/-!
# The valuative relation on an adic completion

Let `R` be a Dedekind domain with fraction field `K` and let `v` be a height-one prime of `R`. The
completion `K_v` already carries the adic valuation `Valued.v`, with values in `ℤᵐ⁰`. This file
equips `K_v` with the valuative relation that valuation induces, checks that its existing topology
is the valuative topology and that the relation is nontrivial, and identifies the ring of integers
and the residue field of the valuative relation with the ones `K_v` already has.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.integer_eq_adicCompletionIntegers`: the ring of integers of
  the valuative relation is `𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.residueFieldEquivAdicCompletion`: the residue field of the
  valuative relation is `R ⧸ v`; `residueFieldEquivAdicCompletion_apply_mk` describes it on a
  quotient representative.
* `IsDedekindDomain.HeightOneSpectrum.natCard_residueField_adicCompletion_eq_absNorm`: that residue
  field has `Ideal.absNorm v.asIdeal` elements.

## Implementation notes

The valuative relation is the one induced by `Valued.v`, so `Valued.v` is `Valuation.Compatible`
with it and the generic comparison lemmas `Valuation.vle_iff_le` and `Valuation.vle_one_iff`
translate between the two languages; no comparison API specific to `K_v` is introduced.

The residue-field comparison rests on `residueFieldEquivAdicCompletionIntegers`, which compares
`R ⧸ v` with the residue field of `𝒪_v`; only the passage from `𝒪_v` to the ring of integers of the
valuative relation is added here.
-/

public section
noncomputable section

open ValuativeRel

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- The valuative relation on an adic completion induced by its canonical adic valuation. -/
noncomputable instance instValuativeRelAdicCompletion : ValuativeRel (v.adicCompletion K) :=
  .ofValuation Valued.v

/-- The canonical adic valuation is compatible with the valuative relation it induces. -/
instance instCompatibleValuedAdicCompletion :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).Compatible :=
  .ofValuation _

/-- The topology of an adic completion is induced by its canonical valuative relation. -/
instance isValuativeTopologyAdicCompletion : IsValuativeTopology (v.adicCompletion K) := by
  apply IsValuativeTopology.of_mem_nhds_zero_iff_vle
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
  intro s
  exact Valued.is_topological_valuation s

/-- The canonical valuative relation on an adic completion is nontrivial. -/
instance isNontrivialAdicCompletion : ValuativeRel.IsNontrivial (v.adicCompletion K) :=
  ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) |>.mpr inferInstance

/-- The ring of integers of the valuative relation is the canonical ring of integers `𝒪_v`. -/
theorem integer_eq_adicCompletionIntegers :
    𝒪[v.adicCompletion K] = (v.adicCompletionIntegers K).toSubring := by
  ext x
  rw [ValuationSubring.mem_toSubring, mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  exact (Valuation.vle_one_iff (ValuativeRel.valuation (v.adicCompletion K))).symm.trans
    (Valuation.vle_one_iff (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))

/-- An element of `R` lands in the ring of integers of the valuative relation on `K_v`. -/
theorem algebraMap_mem_integer_adicCompletion (a : R) :
    algebraMap R (v.adicCompletion K) a ∈ 𝒪[v.adicCompletion K] := by
  rw [integer_eq_adicCompletionIntegers, ValuationSubring.mem_toSubring]
  exact coe_mem_adicCompletionIntegers v a

/-- The residue field of the valuative relation on `K_v` is the residue field `R ⧸ v` of `v`. -/
noncomputable def residueFieldEquivAdicCompletion :
    (R ⧸ v.asIdeal) ≃+* 𝓀[v.adicCompletion K] :=
  -- the ascription reads `RingEquiv.subringCongr` at `v.adicCompletionIntegers K` rather than at
  -- its `toSubring`, whose coercion is the same type but carries no `IsLocalRing` instance
  (v.residueFieldEquivAdicCompletionIntegers (K := K)).trans
    (IsLocalRing.ResidueField.mapEquiv
      ((RingEquiv.subringCongr (integer_eq_adicCompletionIntegers v)).symm :
        v.adicCompletionIntegers K ≃+* 𝒪[v.adicCompletion K]))

/-- **The residue-field equivalence on a quotient representative.** This is the characterization
consumers should use; the construction of the equivalence is an implementation detail and should
not be unfolded. -/
@[simp]
theorem residueFieldEquivAdicCompletion_apply_mk (a : R) :
    v.residueFieldEquivAdicCompletion (K := K) (Ideal.Quotient.mk v.asIdeal a) =
      IsLocalRing.residue _ (⟨algebraMap R (v.adicCompletion K) a,
        v.algebraMap_mem_integer_adicCompletion (K := K) a⟩ : 𝒪[v.adicCompletion K]) := by
  let e : v.adicCompletionIntegers K ≃+* 𝒪[v.adicCompletion K] :=
    (RingEquiv.subringCongr (integer_eq_adicCompletionIntegers v)).symm
  let x : IsLocalRing.ResidueField (v.adicCompletionIntegers K) := by
    change v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal _
    exact v.residueFieldEquivAdicCompletionIntegers (K := K)
      (Ideal.Quotient.mk v.asIdeal a)
  have hx : x = IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) a) := by
    change v.residueFieldEquivAdicCompletionIntegers (K := K)
      (Ideal.Quotient.mk v.asIdeal a) = _
    exact v.residueFieldEquivAdicCompletionIntegers_apply_mk (K := K) a
  change IsLocalRing.ResidueField.mapEquiv e x = _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, hx, IsLocalRing.ResidueField.map_residue]
  apply congrArg (IsLocalRing.residue _)
  apply Subtype.ext
  dsimp only [e]
  calc
    _ = ↑(algebraMap R (v.adicCompletionIntegers K) a) :=
      RingEquiv.coe_subringCongr_apply
        (integer_eq_adicCompletionIntegers v).symm _
    _ = _ := IsScalarTower.algebraMap_apply R (v.adicCompletionIntegers K)
      (v.adicCompletion K) a

/-- The residue field of `K_v` has cardinality the absolute norm of `v`. -/
theorem natCard_residueField_adicCompletion_eq_absNorm [Infinite R] :
    Nat.card 𝓀[v.adicCompletion K] = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (residueFieldEquivAdicCompletion v).toEquiv).symm

end IsDedekindDomain.HeightOneSpectrum

end
