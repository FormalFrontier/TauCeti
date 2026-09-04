/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Frobenius.Transport
public import TauCeti.NumberTheory.NumberField.AutomorphismAction
public import TauCeti.NumberTheory.NumberField.RingOfIntegers.Equiv

/-!
# Transporting relative Frobenius data across an isomorphism

An algebra isomorphism between two finite extensions of the same number field restricts to an
isomorphism between their rings of integers (`NumberField.RingOfIntegers.mapAlgEquiv`).  This
file records the local fact needed when a construction indexed by relative Frobenius classes
is transported along that isomorphism: an arithmetic Frobenius is carried to its conjugate.

It is a specialization, along `RingOfIntegers.mapAlgEquiv`, of the generic algebra-equivalence
transport proved in `TauCeti/RingTheory/Frobenius/Transport.lean`; the compatibility lemma
`NumberField.toAlgHom_autCongr` mediates between the Galois-action formulation used here and the
algebra-homomorphism formulation used there.  Unramifiedness needs no specialization: call sites
use `Algebra.IsUnramifiedAt.mapAlgEquiv` and `Algebra.IsUnramifiedAt.mapAlgEquiv_iff` directly
with `RingOfIntegers.mapAlgEquiv e`.

The ideal map is used rather than a second ideal carrier.  In particular, the statements remain
conditional on an arithmetic Frobenius witness at the ideal; they do not extend that predicate to
ideals without such a witness.

## Main results

* `NumberField.isArithFrobAt_autCongr_map_ringOfIntegersAlgEquiv` and its `iff` form:
  arithmetic Frobenius transport.
* `NumberField.toAlgHom_autCongr`: conjugation of automorphisms restricts to conjugation of their
  actions on the ring of integers.

-/

public section

open scoped NumberField

namespace NumberField

variable {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

/-- **Conjugation restricts to the ring of integers.**  The action on `𝓞 L'` of the conjugate
automorphism `e.autCongr τ`, stated in its defining normal form `e.symm.trans (τ.trans e)`, is
the conjugation of the action of `τ` on `𝓞 L` by the induced equivalence
`RingOfIntegers.mapAlgEquiv e`. -/
theorem toAlgHom_autCongr (e : L ≃ₐ[K] L') (τ : L ≃ₐ[K] L) :
    MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L') (e.symm.trans (τ.trans e)) =
      (RingOfIntegers.mapAlgEquiv e : 𝓞 L →ₐ[𝓞 K] 𝓞 L').comp
        ((MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) τ).comp
          (RingOfIntegers.mapAlgEquiv e).symm.toAlgHom) := by
  ext x
  simp [MulSemiringAction.toAlgHom_apply, algebraMap_smul_eq_apply, AlgEquiv.trans_apply,
    RingOfIntegers.mapAlgEquiv_apply]

/-- An arithmetic Frobenius is transported to the conjugate automorphism at the transported
ideal.  The exponent is unchanged because the two ideals have the same contraction to `𝓞 K`
(`Ideal.under_mapAlgEquiv`). -/
theorem isArithFrobAt_autCongr_map_ringOfIntegersAlgEquiv (e : L ≃ₐ[K] L')
    (Q : Ideal (𝓞 L))
    (τ : L ≃ₐ[K] L)
    (hτ : IsArithFrobAt (𝓞 K) τ Q) :
    IsArithFrobAt (𝓞 K) (e.autCongr τ)
      (Q.map (RingOfIntegers.mapAlgEquiv e)) := by
  -- Unfold `IsArithFrobAt` to its algebra-homomorphism formulation and write the conjugated
  -- automorphism in its defining normal form (`AlgEquiv.autCongr_apply`).
  simp only [IsArithFrobAt, AlgEquiv.autCongr_apply]
  rw [toAlgHom_autCongr]
  exact AlgHom.IsArithFrobAt.mapAlgEquiv (RingOfIntegers.mapAlgEquiv e) Q _ hτ

/-- The Frobenius transport theorem is an equivalence when the transported ideal is written as the
map of the original one. -/
@[simp]
theorem isArithFrobAt_autCongr_map_ringOfIntegersAlgEquiv_iff
    (e : L ≃ₐ[K] L')
    (Q : Ideal (𝓞 L))
    (τ : L ≃ₐ[K] L) :
    IsArithFrobAt (𝓞 K) (e.symm.trans (τ.trans e))
      (Q.map (RingOfIntegers.mapAlgEquiv e)) ↔
      IsArithFrobAt (𝓞 K) τ Q := by
  simp only [IsArithFrobAt]
  rw [toAlgHom_autCongr]
  exact AlgHom.IsArithFrobAt.mapAlgEquiv_iff (RingOfIntegers.mapAlgEquiv e) Q _

end NumberField
