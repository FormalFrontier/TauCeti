/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Abelian

/-!
# Commutativity of Galois groups

Mathlib carries abelianness of a Galois extension as the class `IsAbelianGalois`, and its
instance `IsAbelianGalois K K'` for an intermediate field `K'` says that every subextension of an
abelian extension is again abelian. A construction whose ambient group is the Galois group of a
*general* extension cannot ask for that class, since a bundled commutative structure on
`Gal(L/K)` would be an assumption about `L/K`; it carries commutativity as a hypothesis
`∀ σ τ : Gal(L/K), Commute σ τ` instead. This file reads Mathlib's instance in that unbundled
form. The same hypothesis supplies the scoped `IsMulCommutative` instance used by constructions
that need Mathlib's bundled commutativity API, and it passes to every field in a tower under `L`.

## Main results

* `TauCeti.isMulCommutative_galoisGroup_of_commute`
* `TauCeti.commute_of_tower`
-/

public section

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

omit [IsGalois K L] in
/-- An explicit proof that a Galois group is commutative supplies Mathlib's bundled
`IsMulCommutative` structure on that group. -/
theorem isMulCommutative_galoisGroup_of_commute
    (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ) : IsMulCommutative (L ≃ₐ[K] L) :=
  .of_comm fun σ τ ↦ (hab σ τ).eq

open scoped IsMulCommutative in
/-- **Commutativity of the Galois group passes down a field tower.** Every subextension of an
abelian extension is abelian, so a proof that `Gal(L/K)` is commutative is already a proof that
`Gal(M/K)` is for every field `M` in a tower under `L`. -/
theorem commute_of_tower {M : Type*} [Field M] [Algebra K M] [Algebra M L]
    [IsScalarTower K M L] (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
    (σ τ : M ≃ₐ[K] M) :
    Commute σ τ := by
  let _ := isMulCommutative_galoisGroup_of_commute hab
  have : IsAbelianGalois K L := {}
  have : IsAbelianGalois K M := .tower_bot K M L
  exact Commute.all σ τ

end TauCeti
