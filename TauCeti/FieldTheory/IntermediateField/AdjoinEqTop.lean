/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Automorphisms fixing a generating set are the identity

If a set `s` generates a field extension `E/F` (`IntermediateField.adjoin F s = ⊤`), then an
`F`-algebra automorphism of `E` fixing every element of `s` is the identity. This is the
whole-field counterpart of Mathlib's `IntermediateField.algHom_ext_of_eq_adjoin` (which
compares homomorphisms out of the *subfield* `adjoin F s`), obtained from it by transporting
along `adjoin F s ≃ₐ[F] E` rather than repeating the adjoin induction.

It is the extensionality step shared by the multiquadratic Layer 1 arguments: the splitting
law shows a decomposition-group element fixes every generator `√dᵢ` and concludes it is
trivial, and the Frobenius computation concludes the same when every Legendre symbol is `1`.

## Main results

* `TauCeti.IntermediateField.algEquiv_ext_of_adjoin_eq_top`: two automorphisms agreeing on a
  generating set are equal.
* `TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top`: an automorphism fixing each
  element of a generating set is `1`.
-/

public section

namespace TauCeti.IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {s : Set E}

/-- **Two algebra homomorphisms agreeing on a generating set are equal.** If `s` generates `E`
over `F` (`IntermediateField.adjoin F s = ⊤`) and `F`-algebra maps `σ, τ : E →ₐ[F] E₂` (into any
semiring `E₂`) agree on every element of `s`, then `σ = τ`. This is the whole-field, two-map
counterpart of Mathlib's `IntermediateField.algHom_ext_of_eq_adjoin`. -/
theorem algHom_ext_of_adjoin_eq_top {E₂ : Type*} [Semiring E₂] [Algebra F E₂]
    (htop : IntermediateField.adjoin F s = ⊤)
    {σ τ : E →ₐ[F] E₂} (h : ∀ x ∈ s, σ x = τ x) : σ = τ := by
  -- Transport `σ`, `τ` along `adjoin F s ≃ E` and compare on the subfield with Mathlib's
  -- `algHom_ext_of_eq_adjoin`, which is the adjoin induction we would otherwise repeat.
  let e : IntermediateField.adjoin F s ≃ₐ[F] E :=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  have key : σ.comp e.toAlgHom = τ.comp e.toAlgHom :=
    IntermediateField.adjoin_algHom_ext F fun x hx => h x hx
  refine AlgHom.ext fun y => ?_
  obtain ⟨z, rfl⟩ := e.surjective y
  exact AlgHom.congr_fun key z

/-- Two `F`-algebra automorphisms of `E` agreeing on a generating set are equal. -/
theorem algEquiv_ext_of_adjoin_eq_top (htop : IntermediateField.adjoin F s = ⊤)
    {σ τ : E ≃ₐ[F] E} (h : ∀ x ∈ s, σ x = τ x) : σ = τ :=
  AlgEquiv.ext (AlgHom.ext_iff.mp
    (algHom_ext_of_adjoin_eq_top (E₂ := E) htop (σ := σ.toAlgHom) (τ := τ.toAlgHom) h))

/-- An `F`-algebra automorphism of `E` that fixes every element of a set generating `E` over
`F` is the identity. This is `TauCeti.IntermediateField.algEquiv_ext_of_adjoin_eq_top` against
the identity. -/
theorem algEquiv_eq_one_of_adjoin_eq_top (htop : IntermediateField.adjoin F s = ⊤)
    {σ : E ≃ₐ[F] E} (hfix : ∀ x ∈ s, σ x = x) : σ = 1 :=
  algEquiv_ext_of_adjoin_eq_top htop (σ := σ) (τ := 1) (by simpa using hfix)

end TauCeti.IntermediateField
