/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Frobenius
public import TauCeti.NumberTheory.NumberField.Frobenius.Restriction
public import TauCeti.NumberTheory.NumberField.AutomorphismAction

/-!
# The Artin symbol of an unramified prime

For a finite Galois extension of number fields, this file attaches to an unramified
prime ideal of the base the conjugacy class of its arithmetic Frobenius elements.
The definition uses Mathlib's `IsArithFrobAt` and `arithFrobAt`; no Frobenius
predicate or representative is introduced here.

The construction follows Jürgen Neukirch, *Algebraic Number Theory*, Chapter I, §9,
Exercise 2.

The same reference gives functoriality in a normal tower: restriction maps the Artin symbol of
`L/K` to the Artin symbol of `M/K`. Unramifiedness in the intermediate extension is derived from
unramifiedness in the top extension, rather than assumed separately.
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

/-- **Unramifiedness descends to an intermediate extension.** If every prime of `L` over `𝔭` is
unramified over `K`, then every prime of an intermediate field `M` over `𝔭` is unramified over
`K` as well. -/
theorem isUnramifiedAt_of_intermediateExtension {M L : Type*} [Field M] [NumberField M]
    [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    ∀ (P : Ideal (𝓞 M)) [P.IsPrime] [P.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) P := by
  intro P _ _
  let Q : P.primesOver (𝓞 L) := Classical.choice inferInstance
  let _ : Q.1.IsPrime := Q.2.1
  let _ : Q.1.LiesOver P := Q.2.2
  let _ : Q.1.LiesOver 𝔭 := Ideal.LiesOver.trans Q.1 P 𝔭
  let _ : Algebra.IsUnramifiedAt (𝓞 K) Q.1 := hur Q.1
  exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) P Q.1

/-- **The Artin symbol is functorial under restriction to a normal subextension.** For a normal
tower `L/M/K`, applying restriction to the conjugacy class `artinSymbol 𝔭` for `L/K` gives the
Artin symbol for `M/K`. The latter's unramifiedness witness is derived canonically from the
hypothesis for `L/K`. -/
theorem artinSymbol_map_restrictNormalHom {M L : Type*} [Field M] [NumberField M]
    [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [IsGalois K L] [IsGalois K M]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    ConjClasses.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M)
        (artinSymbol 𝔭 hur) =
      artinSymbol 𝔭 (isUnramifiedAt_of_intermediateExtension (M := M) (L := L) 𝔭 hur) := by
  let Q : 𝔭.primesOver (𝓞 L) := Classical.choice inferInstance
  let _ : Q.1.IsPrime := Q.2.1
  let _ : Q.1.LiesOver 𝔭 := Q.2.2
  have h𝔭ne : 𝔭 ≠ ⊥ :=
    (𝔭.bot_lt_of_maximal (RingOfIntegers.not_isField K)).ne'
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q.1
    (Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭ne Q.1)
  rw [artinSymbol_eq_mk_of_isArithFrobAt 𝔭 hur Q.1 σ hσ,
    artinSymbol_eq_mk_of_isArithFrobAt 𝔭
      (isUnramifiedAt_of_intermediateExtension (M := M) (L := L) 𝔭 hur)
      (Q.1.under (𝓞 M))
      (σ.restrictNormal M) hσ.restrictNormal]
  rfl

end NumberField
