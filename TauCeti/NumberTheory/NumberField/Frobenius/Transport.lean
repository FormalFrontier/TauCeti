/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Frobenius
public import TauCeti.NumberTheory.NumberField.AutomorphismAction

/-!
# Transporting relative Frobenius data across an isomorphism

An algebra isomorphism between two finite extensions of the same number field restricts to an
isomorphism between their rings of integers.  This file records the two local facts needed when a
construction indexed by relative Frobenius classes is transported along that isomorphism:

* relative unramifiedness is preserved by the induced map on prime ideals; and
* an arithmetic Frobenius is carried to its conjugate.

The prime-ideal map is used rather than a second prime carrier.  In particular, the statements
remain conditional at a prime and do not assign a Frobenius to a ramified prime.

## References

* [Chebotarev roadmap, Layer 2](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/Chebotarev/README.md)
  specifies the extension-isomorphism equivariance supplied here.
-/

public section

open Ideal
open scoped NumberField

namespace NumberField

variable {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

private theorem under_map_ringOfIntegersAlgEquiv (e : L ≃ₐ[K] L')
    (Q : Ideal (𝓞 L)) :
    (Q.map (RingOfIntegers.mapAlgEquiv e)).under (𝓞 K) = Q.under (𝓞 K) := by
  let eO := RingOfIntegers.mapAlgEquiv e
  rw [Ideal.under_def, Ideal.under_def]
  have hmap : Q.map (RingOfIntegers.mapAlgEquiv e) =
      Q.map (eO.toRingEquiv : 𝓞 L →+* 𝓞 L') := by
    rfl
  rw [hmap]
  rw [Ideal.map_comap_of_equiv]
  ext x
  simp only [Ideal.mem_comap]
  rw [← eO.commutes]
  simp

/-- Unramifiedness at a prime is invariant under the induced map on rings of integers. -/
theorem isUnramifiedAt_map_ringOfIntegersAlgEquiv (e : L ≃ₐ[K] L')
    (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Algebra.IsUnramifiedAt (𝓞 K) Q) :
    Algebra.IsUnramifiedAt (𝓞 K) (Q.map (RingOfIntegers.mapAlgEquiv e)) := by
  let eO := RingOfIntegers.mapAlgEquiv e
  let Q' : Ideal (𝓞 L') := Q.map (eO : 𝓞 L →+* 𝓞 L')
  let _ : Q'.IsPrime := Ideal.map_isPrime_of_equiv eO
  let hcomap : Q = Q'.comap (eO : 𝓞 L →+* 𝓞 L') := by
    dsimp [Q']
    exact (Q.comap_map_of_bijective _ eO.bijective).symm
  let eLocal : Localization.AtPrime Q ≃ₐ[𝓞 K] Localization.AtPrime Q' :=
    Localization.localAlgEquiv Q Q' eO hcomap
  let _ : Algebra.FormallyUnramified (𝓞 K) (Localization.AtPrime Q) := hQ
  exact Algebra.FormallyUnramified.of_equiv eLocal

/-- An arithmetic Frobenius is transported to the conjugate automorphism at the transported
prime.  The exponent is unchanged because the two primes have the same contraction to `𝓞 K`. -/
theorem isArithFrobAt_map_ringOfIntegersAlgEquiv (e : L ≃ₐ[K] L')
    (Q : Ideal (𝓞 L))
    (τ : L ≃ₐ[K] L)
    (hτ : IsArithFrobAt (𝓞 K) τ Q) :
    IsArithFrobAt (𝓞 K) (e.autCongr τ)
      (Q.map (RingOfIntegers.mapAlgEquiv e)) := by
  let eO := RingOfIntegers.mapAlgEquiv e
  let Q' : Ideal (𝓞 L') := Q.map (eO : 𝓞 L →+* 𝓞 L')
  -- Unfold `IsArithFrobAt` to expose the action-level formulation we transport.
  change (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L')
    (e.symm.trans (τ.trans e))).IsArithFrobAt Q'
  intro x
  let y : 𝓞 L := eO.symm x
  have hy := hτ y
  have haction :
      eO.symm ((MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L')
        (e.symm.trans (τ.trans e))) x) =
      (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) τ) (eO.symm x) := by
    apply RingOfIntegers.ext
    have heO_apply (z : 𝓞 L') : (eO.symm z : L) = e.symm (z : L') := by
      simpa only [eO] using RingOfIntegers.mapAlgEquiv_symm_apply e z
    rw [heO_apply]
    simp only [MulSemiringAction.toAlgHom_apply, algebraMap_smul_eq_apply,
      AlgEquiv.trans_apply]
    -- Reduce the two ring-of-integers actions to their ambient field actions.
    change e.symm (e (τ (e.symm (x : L')))) = τ (e.symm (x : L'))
    simp
  have hunder : Q'.under (𝓞 K) = Q.under (𝓞 K) :=
    under_map_ringOfIntegersAlgEquiv e Q
  rw [hunder]
  -- The mapped ideal is represented by the underlying ring equivalence here.
  change _ ∈ Ideal.map eO.toRingEquiv Q
  rw [← Ideal.symm_apply_mem_of_equiv_iff]
  -- Pull membership back along the equivalence so that the source Frobenius hypothesis applies.
  change eO.symm
      ((MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L')
        (e.symm.trans (τ.trans e))) x - x ^ Nat.card (𝓞 K ⧸ under (𝓞 K) Q)) ∈ Q
  rw [map_sub, map_pow, haction]
  exact hy

/-- The Frobenius transport theorem is an equivalence when the transported prime is written as the
map of the original one. -/
@[simp]
theorem isArithFrobAt_map_ringOfIntegersAlgEquiv_iff
    (e : L ≃ₐ[K] L')
    (Q : Ideal (𝓞 L))
    (τ : L ≃ₐ[K] L) :
    IsArithFrobAt (𝓞 K) (e.symm.trans (τ.trans e))
      (Q.map (RingOfIntegers.mapAlgEquiv e)) ↔
      IsArithFrobAt (𝓞 K) τ Q := by
  constructor
  · intro hσ
    let eO := RingOfIntegers.mapAlgEquiv e
    let Q' : Ideal (𝓞 L') := Q.map (eO : 𝓞 L →+* 𝓞 L')
    have hτ' := isArithFrobAt_map_ringOfIntegersAlgEquiv (e := e.symm)
      (Q := Q') (τ := e.autCongr τ) hσ
    have heO : RingOfIntegers.mapAlgEquiv e.symm = eO.symm := by
      simpa [eO] using RingOfIntegers.mapAlgEquiv_symm e
    rw [heO] at hτ'
    -- Expose the double conjugation before cancelling the inverse equivalence.
    change IsArithFrobAt (𝓞 K) ((e.symm).autCongr (e.autCongr τ))
      (Q'.map eO.symm) at hτ'
    have hconj : (e.symm).autCongr (e.autCongr τ) = τ := by
      ext x
      simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, e.symm_apply_apply,
        AlgEquiv.symm_symm]
    rw [hconj] at hτ'
    dsimp [Q'] at hτ'
    have hmap : (Q.map (eO : 𝓞 L →+* 𝓞 L')).map eO.symm = Q :=
      Ideal.map_of_equiv eO.toRingEquiv
    rw [hmap] at hτ'
    exact hτ'
  · exact isArithFrobAt_map_ringOfIntegersAlgEquiv e Q τ

/-- Unramifiedness is likewise invariant in both directions under the induced prime bijection. -/
@[simp]
theorem isUnramifiedAt_map_ringOfIntegersAlgEquiv_iff (e : L ≃ₐ[K] L')
    (Q : Ideal (𝓞 L)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 K) (Q.map (RingOfIntegers.mapAlgEquiv e)) ↔
      Algebra.IsUnramifiedAt (𝓞 K) Q := by
  constructor
  · intro hQ'
    let eO := RingOfIntegers.mapAlgEquiv e
    let Q' : Ideal (𝓞 L') := Q.map (eO : 𝓞 L →+* 𝓞 L')
    let _ : Q'.IsPrime := Ideal.map_isPrime_of_equiv eO
    have hQ := isUnramifiedAt_map_ringOfIntegersAlgEquiv (e := e.symm) (Q := Q') hQ'
    have heO : RingOfIntegers.mapAlgEquiv e.symm = eO.symm := by
      simpa [eO] using RingOfIntegers.mapAlgEquiv_symm e
    have hmap : Q'.map (RingOfIntegers.mapAlgEquiv e.symm) = Q := by
      rw [heO]
      dsimp [Q']
      exact Ideal.map_of_equiv eO.toRingEquiv
    simpa only [hmap] using hQ
  · exact isUnramifiedAt_map_ringOfIntegersAlgEquiv e Q

end NumberField
