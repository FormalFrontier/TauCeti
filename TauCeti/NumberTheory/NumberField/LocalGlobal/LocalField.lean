/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension

/-!
# Finite completions of number fields are local fields

The completion of a number field at a nonzero prime ideal is a nonarchimedean local field.  This
file equips Mathlib's `v.adicCompletion K` with the valuative relation induced by its existing
adic valuation and supplies the local-field instance.

The construction uses the existing topology and valuation on the completion.  In particular, its
valuative relation compares elements exactly as `Valued.v` does.  The residue field is finite
because it is isomorphic to the finite quotient `(𝓞 K) ⧸ v.asIdeal`; this also identifies its
cardinality with `Ideal.absNorm v.asIdeal`.

These instances let local-field results apply directly to the canonical finite completions used in
global arithmetic, without choosing another valuation or another completion.
-/

public section
noncomputable section

open IsDedekindDomain NumberField Valued.integer ValuativeRel
open scoped WithZero

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

/-- The valuative relation on a finite completion induced by its canonical adic valuation. -/
@[instance_reducible]
noncomputable def adicCompletionValuativeRel : ValuativeRel (v.adicCompletion K) :=
  .ofValuation Valued.v

/-- Use the canonical valuative relation on a finite completion. -/
noncomputable instance instValuativeRelAdicCompletion : ValuativeRel (v.adicCompletion K) :=
  adicCompletionValuativeRel v

/-- The canonical adic valuation is compatible with the valuative relation it induces. -/
instance instCompatibleValuedAdicCompletion :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).Compatible :=
  .ofValuation _

/-- The valuative relation on a finite completion orders elements as its adic valuation does. -/
@[simp]
theorem adicCompletion_vle_iff (a b : v.adicCompletion K) :
    a ≤ᵥ b ↔ Valued.v a ≤ Valued.v b :=
  Iff.rfl

/-- The topology of a finite completion is induced by its canonical valuative relation. -/
instance adicCompletionIsValuativeTopology : IsValuativeTopology (v.adicCompletion K) := by
  apply IsValuativeTopology.of_mem_nhds_zero_iff_vle
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
  intro s
  exact Valued.is_topological_valuation s

/-- The canonical valuative relation on a finite completion is nontrivial. -/
instance adicCompletionValuativeRelIsNontrivial :
    ValuativeRel.IsNontrivial (v.adicCompletion K) :=
  ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) |>.mpr inferInstance

/-- The local-field ring of integers is the canonical ring of integers of the completion. -/
theorem integer_eq_adicCompletionIntegers :
    𝒪[v.adicCompletion K] = (v.adicCompletionIntegers K).toSubring := by
  ext x
  change valuation (v.adicCompletion K) x ≤ 1 ↔
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) x ≤ 1
  simpa only [map_one] using
    ((Valuation.Compatible.vle_iff_le
      (v := valuation (v.adicCompletion K)) x 1).symm.trans
        (Valuation.Compatible.vle_iff_le
          (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) x 1))

/-- The residue field of a finite completion is the quotient by its defining prime ideal. -/
noncomputable def residueFieldEquivAdicCompletion :
    (𝓞 K) ⧸ v.asIdeal ≃+* 𝓀[v.adicCompletion K] := by
  let _ : IsLocalRing (v.adicCompletionIntegers K).toSubring :=
    inferInstanceAs (IsLocalRing (v.adicCompletionIntegers K))
  exact (v.residueFieldEquivAdicCompletionIntegers (K := K)).trans
    (IsLocalRing.ResidueField.mapEquiv
      (RingEquiv.subringCongr (integer_eq_adicCompletionIntegers v))).symm

/-- The residue field of a finite completion has cardinality equal to the norm of its prime. -/
theorem natCard_residueField_adicCompletion_eq_absNorm :
    Nat.card 𝓀[v.adicCompletion K] = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (residueFieldEquivAdicCompletion v).toEquiv).symm

/-- The completion of a number field at a nonzero prime ideal is a nonarchimedean local field. -/
instance isNonarchimedeanLocalField_adicCompletion :
    IsNonarchimedeanLocalField (v.adicCompletion K) := by
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := K)).toEquiv
  let _ : ProperSpace (v.adicCompletion K) :=
    (@properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (v.adicCompletion K) ℤᵐ⁰ _ _
      (inferInstance : Valued (v.adicCompletion K) ℤᵐ⁰) inferInstance).mpr
      ⟨inferInstance,
        (show IsDiscreteValuationRing (v.adicCompletionIntegers K) from inferInstance),
        (show Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) from inferInstance)⟩
  exact ⟨⟩

end TauCeti.NumberField
