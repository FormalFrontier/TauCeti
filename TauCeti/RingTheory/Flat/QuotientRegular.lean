/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Flatness of `B ⧸ (g)` when `g` acts injectively on each `(R ⧸ I) ⊗[R] B`

Let `B` be a flat algebra over a commutative ring `R` and `g ∈ B`. If multiplication by `g` on
`(R ⧸ I) ⊗[R] B` is injective for every finitely generated ideal `I` of `R`, then `B ⧸ (g)` is a
flat `R`-module.

This is the claim inside Wedhorn's proof of Lemma 8.31(2): for `B = A⟨X⟩` over a complete
noetherian Tate ring `A`, and `g = f - X` or `g = 1 - f X`, the quotient is flat because
multiplication by `g` is injective on `M⟨X⟩ = M ⊗[A] A⟨X⟩` for every finitely generated `M` —
in particular for every `M = A ⧸ I`, which is all the argument uses. Wedhorn proves the claim
with the long exact `Tor` sequence. What the sequence encodes is a diagram chase, and that chase
is what is carried out here, against Mathlib's ideal criterion for flatness: `B ⧸ (g)` is flat
once `I ⊗[R] (B ⧸ (g)) → R ⊗[R] (B ⧸ (g))` is injective for every finitely generated ideal `I`.

## Main results

* `Module.Flat.quotient_span_singleton_of_lTensor_mulLeft_injective`: the statement above.

## Implementation notes

The hypothesis is asked only on `(R ⧸ I) ⊗[R] B` for finitely generated ideals `I`, which is
exactly what the chase consumes; a hypothesis on every finitely generated module, as Wedhorn
states it, specialises to this. It is stated with the coefficient module on the left,
matching the orientation of Mathlib's `Module.Flat.iff_rTensor_injective`.

The chase, for a finitely generated ideal `I`: an element of `I ⊗ (B ⧸ (g))` killed in
`R ⊗ (B ⧸ (g))` lifts to `I ⊗ B`, is there the image of `g` times some `w` in `R ⊗ B`, and
injectivity of `g` on `(R ⧸ I) ⊗ B` shows that `w` comes from `I ⊗ B`, so the element is `g`
times an element of `I ⊗ B` and dies in `I ⊗ (B ⧸ (g))`. Flatness of `B` enters twice: as
exactness of `I ⊗ B → R ⊗ B → (R ⧸ I) ⊗ B`, and as injectivity of `I ⊗ B → R ⊗ B`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Lemma 8.31.
-/

public section

open TensorProduct

namespace Module.Flat

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- **A flat algebra modulo an element acting injectively on each `(R ⧸ I) ⊗[R] B` is flat.**
Let `B` be a flat `R`-algebra and `g ∈ B`. If `id ⊗ (g • ·) : (R ⧸ I) ⊗[R] B → (R ⧸ I) ⊗[R] B` is
injective for every finitely generated ideal `I`, then `B ⧸ (g)` is a flat `R`-module. This is the
`Tor`-sequence step of Wedhorn's Lemma 8.31(2); a consumer holding injectivity for every finitely
generated module, as Wedhorn states it, passes it at `M = R ⧸ I`. -/
theorem quotient_span_singleton_of_lTensor_mulLeft_injective [Flat R B] (g : B)
    (hg : ∀ ⦃I : Ideal R⦄, I.FG →
      Function.Injective (LinearMap.lTensor (R ⧸ I) (LinearMap.mulLeft R g))) :
    Flat R (B ⧸ Ideal.span {g}) := by
  rw [iff_rTensor_injective]
  intro I hI
  set v : B →ₗ[R] B := LinearMap.mulLeft R g with hv
  set π : B →ₗ[R] B ⧸ Ideal.span {g} := (Ideal.Quotient.mkₐ R (Ideal.span {g})).toLinearMap
    with hπ
  have hexact : Function.Exact v π := fun y ↦ by
    simp only [hπ, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton', Set.mem_range, hv,
      LinearMap.mulLeft_apply]
    exact exists_congr fun a ↦ by rw [mul_comm]
  have hπv : π ∘ₗ v = 0 := hexact.linearMap_comp_eq_zero
  have hqι : I.mkQ ∘ₗ I.subtype = 0 := (LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨z', rfl⟩ := LinearMap.lTensor_surjective I (g := π) Ideal.Quotient.mk_surjective z
  -- `rTensor B I.subtype z'` is killed by `lTensor R π`, so it is `g` times some `w`.
  have h1 : LinearMap.lTensor R π (LinearMap.rTensor B I.subtype z') = 0 := by
    rwa [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
      LinearMap.comp_apply]
  obtain ⟨w, hw⟩ := ((lTensor_exact R hexact) _).mp h1
  -- The image of `w` in `(R ⧸ I) ⊗ B` is killed by `g`, hence zero, so `w` comes from `I ⊗ B`.
  have h2 : LinearMap.lTensor (R ⧸ I) v (LinearMap.rTensor B I.mkQ w) = 0 := by
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
      LinearMap.comp_apply, hw, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hqι,
      LinearMap.rTensor_zero, LinearMap.zero_apply]
  obtain ⟨z₀, hz₀⟩ := ((rTensor_exact B (LinearMap.exact_subtype_mkQ I)) _).mp
    ((injective_iff_map_eq_zero _).mp (hg hI) _ h2)
  -- Flatness of `B` makes `I ⊗ B → R ⊗ B` injective, so `z' = g • z₀`.
  have h4 : LinearMap.lTensor I v z₀ = z' :=
    rTensor_preserves_injective_linearMap I.subtype I.injective_subtype <| by
      rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
        LinearMap.comp_apply, hz₀, hw]
  rw [← h4, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hπv, LinearMap.lTensor_zero,
    LinearMap.zero_apply]

end Module.Flat
