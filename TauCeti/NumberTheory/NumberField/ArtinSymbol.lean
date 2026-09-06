/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Frobenius
public import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup
public import TauCeti.NumberTheory.NumberField.Frobenius.Restriction
public import TauCeti.NumberTheory.NumberField.SplitsCompletely
public import TauCeti.NumberTheory.NumberField.UnramifiedTower
import TauCeti.Algebra.Group.Conj

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

Finally, the symbol detects complete splitting: it is the identity class exactly when the
residue degree is one, equivalently when `𝓞 L` has `[L : K]` primes above `𝔭`.
-/

public section

open Ideal
open scoped NumberField Pointwise

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
  have hpne : 𝔭 ≠ ⊥ := NeZero.ne 𝔭
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
  -- `AlgEquiv.restrictNormalHom M σ` is `σ.restrictNormal M`, so this is exactly the computation
  -- rule for `ConjClasses.map` on representatives.
  exact ConjClasses.map_mk _ σ

/-- Every representative of `artinSymbol 𝔭 hur` is an arithmetic Frobenius at some prime above
`𝔭`. -/
theorem exists_isArithFrobAt_of_artinSymbol_eq_mk {L : Type*} [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) Q) {σ : L ≃ₐ[K] L}
    (h : artinSymbol 𝔭 hur = ConjClasses.mk σ) :
    ∃ Q : 𝔭.primesOver (𝓞 L), IsArithFrobAt (𝓞 K) σ Q.1 := by
  obtain ⟨Q₀, _, _⟩ := (inferInstance : Nonempty (𝔭.primesOver (𝓞 L)))
  obtain ⟨σ₀, hσ₀⟩ := exists_isArithFrobAt K Q₀
    (Ideal.ne_bot_of_liesOver_of_ne_bot (NeZero.ne 𝔭) Q₀)
  have hconj : IsConj σ₀ σ := ConjClasses.mk_eq_mk_iff_isConj.mp
    ((artinSymbol_eq_mk_of_isArithFrobAt 𝔭 hur Q₀ σ₀ hσ₀).symm.trans h)
  obtain ⟨τ, hτ⟩ := isConj_iff.mp hconj
  exact ⟨Ideal.primesOver.mk 𝔭 (τ • Q₀), hτ ▸ hσ₀.conj τ⟩

section IsoOfExtensions

/-!
### Transport along an isomorphism of extensions

An isomorphism `e : L ≃ₐ[K] L'` of extensions of `K` induces `𝓞 L ≃ₐ[𝓞 K] 𝓞 L'`, and everything
`artinSymbol` is built from travels along it: the primes above `𝔭`, their unramifiedness, and the
Frobenius condition. The symbol itself is therefore equivariant for the induced isomorphism
`AlgEquiv.autCongr e` of Galois groups.
-/

variable {L L' : Type*} [Field L] [Algebra K L] [Field L'] [Algebra K L']

variable [NumberField L] [IsGalois K L] [NumberField L'] [IsGalois K L']

/-- **The Artin symbol is equivariant under an isomorphism of extensions.** For `e : L ≃ₐ[K] L'`,
the symbol computed in `L'` is the image of the one computed in `L` under the induced isomorphism
`AlgEquiv.autCongr e` of Galois groups. -/
theorem artinSymbol_eq_map_autCongr (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal] (e : L ≃ₐ[K] L')
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q)
    (hur' : ∀ (Q : Ideal (𝓞 L')) [Q.IsPrime] [Q.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q) :
    artinSymbol 𝔭 hur' =
      ConjClasses.map (AlgEquiv.autCongr e).toMonoidHom (artinSymbol 𝔭 hur) := by
  -- Compute both symbols from one Frobenius `σ₀` at a prime above `𝔭` and its transport.
  obtain ⟨Q₀, _, _⟩ := (inferInstance : Nonempty (𝔭.primesOver (𝓞 L)))
  obtain ⟨σ₀, hσ₀⟩ := exists_isArithFrobAt K Q₀
    (Ideal.ne_bot_of_liesOver_of_ne_bot (NeZero.ne 𝔭) Q₀)
  rw [artinSymbol_eq_mk_of_isArithFrobAt 𝔭 hur Q₀ σ₀ hσ₀,
    artinSymbol_eq_mk_of_isArithFrobAt 𝔭 hur' (Q₀.comap (RingOfIntegers.mapAlgEquiv e).symm)
      (AlgEquiv.autCongr e σ₀) (e.isArithFrobAt_autCongr hσ₀)]
  rfl

end IsoOfExtensions

section SplitsCompletely

/-!
### The trivial Artin symbol

The Artin symbol is the identity class exactly at the primes that split completely. Both
directions come from the same computation: the symbol is represented by an arithmetic Frobenius
`σ` at any prime `Q` above `𝔭`, and `orderOf σ` is the inertia degree `f(Q/𝔭)`.
-/

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- **The Artin symbol is trivial exactly at residue degree one.** For a prime `Q` of `𝓞 L` above
an unramified `𝔭`, the Artin symbol of `𝔭` is the identity class if and only if `f(Q/𝔭) = 1`.

The symbol is `ConjClasses.mk σ` for an arithmetic Frobenius `σ` at `Q`, a class is trivial
exactly when its representative is, and `orderOf σ = f(Q/𝔭)`. -/
theorem artinSymbol_eq_one_iff_inertiaDeg_eq_one (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭] :
    artinSymbol 𝔭 hur = 1 ↔ Q.inertiaDeg (𝓞 K) = 1 := by
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (NeZero.ne 𝔭) Q
  have : Algebra.IsUnramifiedAt (𝓞 K) Q := hur Q
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q hQ
  rw [artinSymbol_eq_mk_of_isArithFrobAt 𝔭 hur Q σ hσ, ConjClasses.one_eq_mk_one,
    ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left, ← orderOf_eq_one_iff,
    orderOf_eq_inertiaDeg_of_isArithFrobAt Q hQ hσ]

/-- **The Artin symbol is trivial exactly at the completely split primes.** For `𝔭` unramified in
`L`, the Artin symbol of `𝔭` is the identity class if and only if `𝔭` splits completely, that is,
`𝓞 L` has `[L : K]` primes above `𝔭`.

The count criterion reads complete splitting as `e = f = 1`; unramifiedness supplies `e = 1`, so
what is left is exactly the residue-degree condition. -/
theorem artinSymbol_eq_one_iff_ncard_primesOver_eq_finrank (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q) :
    artinSymbol 𝔭 hur = 1 ↔ (𝔭.primesOver (𝓞 L)).ncard = Module.finrank K L := by
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (𝔭.primesOver (𝓞 L)))
  have : Algebra.IsUnramifiedAt (𝓞 K) Q := hur Q
  rw [artinSymbol_eq_one_iff_inertiaDeg_eq_one 𝔭 hur Q,
    ncard_primesOver_eq_finrank_iff_of_isGalois K L 𝔭,
    Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭 Q (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg 𝔭 Q (L ≃ₐ[K] L),
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt]
  exact (and_iff_right rfl).symm

end SplitsCompletely

end NumberField
