/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Frobenius
public import TauCeti.NumberTheory.NumberField.Frobenius
public import TauCeti.NumberTheory.NumberField.AutomorphismAction

/-!
# The Artin symbol of an unramified prime

For a finite Galois extension of number fields, this file attaches to an unramified
prime ideal of the base the conjugacy class of its arithmetic Frobenius elements.
The definition uses Mathlib's `IsArithFrobAt` and `arithFrobAt`; no Frobenius
predicate or representative is introduced here.

The construction follows Jürgen Neukirch, *Algebraic Number Theory*, Chapter I, §9,
Exercise 2.
-/

public section

open Ideal
open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The arithmetic Artin symbol at a prime ideal unramified in `L`.

The value is the conjugacy class of Mathlib's coherently chosen arithmetic Frobenius at
one prime above `𝔭`; the unramifiedness proof is an argument, so the symbol is only
defined at unramified primes.
-/
noncomputable def artinSymbol {L : Type*} [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) Q) : ConjClasses (L ≃ₐ[K] L) := by
  let P : 𝔭.primesOver (𝓞 L) := Classical.choice inferInstance
  let _ : P.1.IsPrime := P.2.1
  let _ : P.1.LiesOver 𝔭 := P.2.2
  let _ : Algebra.IsUnramifiedAt (𝓞 K) P.1 := hur P.1
  exact ConjClasses.mk (arithFrobAt (𝓞 K) (L ≃ₐ[K] L) P.1)

/-- Every arithmetic Frobenius at a prime over `𝔭` represents `artinSymbol 𝔭 hur`.

Thus the definition is independent of the prime chosen above `𝔭` and of the chosen
Frobenius at that prime, as required for a conjugacy-class-valued symbol.
-/
theorem artinSymbol_eq_mk_of_isArithFrobAt {L : Type*} [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭]
    (σ : L ≃ₐ[K] L) (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    artinSymbol 𝔭 hur = ConjClasses.mk σ := by
  let P : 𝔭.primesOver (𝓞 L) := Classical.choice inferInstance
  let _ : P.1.IsPrime := P.2.1
  let _ : P.1.LiesOver 𝔭 := P.2.2
  have hpne : 𝔭 ≠ ⊥ :=
    (𝔭.bot_lt_of_maximal (RingOfIntegers.not_isField K)).ne'
  have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpne Q
  let _ : P.1.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
    (Ideal.ne_bot_of_liesOver_of_ne_bot hpne P.1) inferInstance
  let _ : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQne inferInstance
  rw [artinSymbol]
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  have hconj := isConj_arithFrobAt (𝓞 K) (L ≃ₐ[K] L) P.1 Q
    ((Ideal.LiesOver.over (p := 𝔭) (P := P.1)).symm.trans
      (Ideal.LiesOver.over (p := 𝔭) (P := Q)))
  have hQeq : arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q = σ := by
    -- `IsArithFrobAt` is an abbreviation for the action's induced algebra homomorphism;
    -- expose that homomorphism so Mathlib's uniqueness theorem can be applied.
    change (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) σ).IsArithFrobAt Q at hσ
    let _ : Algebra.IsUnramifiedAt (𝓞 K) Q := hur Q
    have hQ' := AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt
      (IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q) hσ
      (by exact Ideal.primeCompl_le_nonZeroDivisors Q)
    apply (galRestrict (𝓞 K) K L (𝓞 L)).injective
    ext x
    have hQ'' := congrArg (algebraMap (𝓞 L) L)
      (congrArg (fun f : (𝓞 L) →ₐ[𝓞 K] (𝓞 L) => f x) hQ')
    rw [MulSemiringAction.toAlgHom_apply, MulSemiringAction.toAlgHom_apply,
      NumberField.algebraMap_smul_eq_apply, NumberField.algebraMap_smul_eq_apply] at hQ''
    simpa [galRestrict_apply, algebraMap_galRestrict_apply] using hQ''
  simpa [hQeq] using hconj

end NumberField
