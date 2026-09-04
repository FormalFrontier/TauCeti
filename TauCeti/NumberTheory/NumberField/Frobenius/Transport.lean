/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.AutomorphismAction
public import TauCeti.NumberTheory.NumberField.RingOfIntegers.Equiv

/-!
# Transporting relative Frobenius data across an isomorphism

An algebra isomorphism between two field extensions of a common base field restricts to an
isomorphism between their rings of integers (`NumberField.RingOfIntegers.mapAlgEquiv`).  This
file records the local fact needed when a construction indexed by relative Frobenius classes
is transported along that isomorphism: an arithmetic Frobenius is carried to its conjugate.

## Main results

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

end NumberField
