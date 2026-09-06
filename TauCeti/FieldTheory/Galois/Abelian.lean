/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Abelian

/-!
# Commutativity of the Galois group of a subextension

Mathlib carries abelianness of a Galois extension as the class `IsAbelianGalois`, and its
instance `IsAbelianGalois K K'` for an intermediate field `K'` says that every subextension of an
abelian extension is again abelian. A construction whose ambient group is the Galois group of a
*general* extension cannot ask for that class, since a bundled commutative structure on
`Gal(L/K)` would be an assumption about `L/K`; it carries commutativity as a hypothesis
`∀ σ τ : Gal(L/K), Commute σ τ` instead. This file reads Mathlib's instance in that unbundled
form: the hypothesis for `L/K` is already the hypothesis for `M/K` for every intermediate field
`M`, and is never a second assumption.

## Main results

* `TauCeti.commute_of_intermediateField`
-/

public section

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

open scoped IsMulCommutative in
/-- **Commutativity of the Galois group passes to an intermediate field.** Every subextension of an
abelian extension is abelian, so a proof that `Gal(L/K)` is commutative is already a proof that
`Gal(M/K)` is, for every intermediate field `M`. -/
theorem commute_of_intermediateField (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
    (M : IntermediateField K L) (σ τ : M ≃ₐ[K] M) :
    Commute σ τ := by
  have : IsMulCommutative (L ≃ₐ[K] L) := ⟨⟨fun a b ↦ (hab a b).eq⟩⟩
  have : IsAbelianGalois K L := {}
  have : IsMulCommutative (M ≃ₐ[K] M) := inferInstance
  exact Commute.all σ τ

end TauCeti
