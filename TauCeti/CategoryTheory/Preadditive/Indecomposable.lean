/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Recognizing indecomposable objects from their endomorphisms

Mathlib defines `CategoryTheory.Indecomposable X` as the conjunction "`X` is not a zero object,
and in every decomposition `X ≅ Y ⊞ Z` one of `Y`, `Z` is zero", and proves exactly one criterion
for it: a simple object is indecomposable (`CategoryTheory.indecomposable_of_simple`). That
criterion is too strong for the objects that carry the theory of a finite-dimensional algebra: an
indecomposable projective module is almost never simple. The criterion that does apply is the one
this file supplies — an object all of whose idempotent endomorphisms are trivial is
indecomposable — together with the form in which it is used in practice: over a field, an object
whose endomorphism space is one-dimensional (a *brick*) is indecomposable.

Only one direction is proved. The converse needs a decomposition `X ≅ im e ⊞ ker e` attached to an
idempotent `e`, that is, idempotent completeness of the ambient category, which is a genuinely
extra hypothesis and is not needed by any consumer here.

## Main results

* `TauCeti.indecomposable_of_forall_idempotent`: a nonzero object whose only idempotent
  endomorphisms are `0` and the identity is indecomposable.
* `TauCeti.exists_eq_smul_id_of_finrank_end_eq_one`: in a `k`-linear category, an object with a
  one-dimensional endomorphism space has every endomorphism a scalar multiple of the identity.
* `TauCeti.indecomposable_of_finrank_end_eq_one`: **a brick is indecomposable**.

## Implementation notes

The idempotent hypothesis is phrased with composition, `e ≫ e = e`, rather than through the ring
`CategoryTheory.End X`, whose multiplication is composition in the opposite order; for an
idempotent the two agree, but the hypothesis is easier to discharge as stated.

`indecomposable_of_forall_idempotent` extracts, from an isomorphism `X ≅ Y ⊞ Z`, the idempotent
`biprod.fst ≫ biprod.inl` transported to `X`. It is `0` exactly when `Y` is zero and the identity
exactly when `Z` is zero, so the hypothesis splits the decomposition; the proof reads off
`𝟙 Y` and `𝟙 Z` from it using only the biproduct equations `biprod.inl_fst`, `biprod.inr_snd` and
`biprod.inr_fst`.

The brick criterion is stated for a field. The argument itself only inverts one scalar, so it
would run over a division ring, but `CategoryTheory.Linear` takes a commutative base and
`Module.finrank` is the invariant used by the consumers, so no generality is lost in practice.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **An object with no nontrivial idempotent endomorphism is indecomposable.** A decomposition
`X ≅ Y ⊞ Z` produces the idempotent `biprod.fst ≫ biprod.inl` on `X`; it is `0` only if `Y` is
zero, and the identity only if `Z` is zero. -/
theorem indecomposable_of_forall_idempotent [HasBinaryBiproducts C] {X : C} (hX : ¬ IsZero X)
    (h : ∀ e : X ⟶ X, e ≫ e = e → e = 0 ∨ e = 𝟙 X) : Indecomposable X := by
  refine ⟨hX, fun Y Z i ↦ ?_⟩
  have hidem : (i.hom ≫ biprod.fst ≫ biprod.inl ≫ i.inv) ≫
      (i.hom ≫ biprod.fst ≫ biprod.inl ≫ i.inv) = i.hom ≫ biprod.fst ≫ biprod.inl ≫ i.inv := by
    simp
  rcases h _ hidem with h0 | h1
  · refine Or.inl ((IsZero.iff_id_eq_zero Y).mpr ?_)
    -- Conjugating back and framing with `biprod.inl`, `biprod.fst` turns the idempotent into `𝟙 Y`.
    have := congrArg (fun f : X ⟶ X ↦ biprod.inl ≫ i.inv ≫ f ≫ i.hom ≫ biprod.fst) h0
    simpa using this
  · refine Or.inr ((IsZero.iff_id_eq_zero Z).mpr ?_)
    -- Framing instead with `biprod.inr`, `biprod.snd` kills the idempotent and leaves `𝟙 Z`.
    have := congrArg (fun f : X ⟶ X ↦ biprod.inr ≫ i.inv ≫ f ≫ i.hom ≫ biprod.snd) h1
    simpa using this.symm

variable {k : Type*} [Field k] [Linear k C]

/-- An object whose endomorphism space is one-dimensional has a nonzero identity, hence is not a
zero object. -/
theorem id_ne_zero_of_finrank_end_eq_one {X : C} (h : Module.finrank k (X ⟶ X) = 1) :
    𝟙 X ≠ 0 := by
  haveI : Nontrivial (X ⟶ X) := Module.nontrivial_of_finrank_pos (R := k) (by rw [h]; exact one_pos)
  obtain ⟨f, g, hfg⟩ := exists_pair_ne (X ⟶ X)
  intro hid
  exact hfg (by rw [← Category.comp_id f, ← Category.comp_id g, hid, comp_zero, comp_zero])

/-- An object whose endomorphism space is one-dimensional is not a zero object. -/
theorem not_isZero_of_finrank_end_eq_one {X : C} (h : Module.finrank k (X ⟶ X) = 1) :
    ¬ IsZero X := fun hX ↦
  id_ne_zero_of_finrank_end_eq_one h ((IsZero.iff_id_eq_zero X).mp hX)

/-- **Every endomorphism of a brick is a scalar.** If the endomorphism space of `X` is
one-dimensional then the identity spans it, so each endomorphism is `c • 𝟙 X`. -/
theorem exists_eq_smul_id_of_finrank_end_eq_one {X : C} (h : Module.finrank k (X ⟶ X) = 1)
    (f : X ⟶ X) : ∃ c : k, f = c • 𝟙 X := by
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (𝟙 X) (id_ne_zero_of_finrank_end_eq_one h)).mp h f
  exact ⟨c, hc.symm⟩

/-- **A brick is indecomposable.** If the endomorphism space of `X` is one-dimensional over the
base field then every endomorphism is a scalar, so the only idempotents are `0` and the identity
and `TauCeti.indecomposable_of_forall_idempotent` applies. -/
theorem indecomposable_of_finrank_end_eq_one [HasBinaryBiproducts C] {X : C}
    (h : Module.finrank k (X ⟶ X) = 1) :
    Indecomposable X := by
  refine indecomposable_of_forall_idempotent (not_isZero_of_finrank_end_eq_one h) fun e he ↦ ?_
  obtain ⟨c, rfl⟩ := exists_eq_smul_id_of_finrank_end_eq_one h e
  rw [Linear.smul_comp, Linear.comp_smul, Category.comp_id, smul_smul] at he
  rcases eq_or_ne c 0 with rfl | hc
  · exact Or.inl (zero_smul k (𝟙 X))
  · refine Or.inr ?_
    -- Scaling the idempotent equation `(c * c) • 𝟙 X = c • 𝟙 X` by `c⁻¹` gives `c • 𝟙 X = 𝟙 X`.
    have := congrArg (fun f : X ⟶ X ↦ c⁻¹ • f) he
    simpa [smul_smul, ← mul_assoc, inv_mul_cancel₀ hc] using this

end TauCeti
