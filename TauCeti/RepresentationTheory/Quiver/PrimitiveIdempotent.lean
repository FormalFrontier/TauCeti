/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic
public import TauCeti.RingTheory.PrimitiveIdempotent

/-!
# The vertex idempotents of a path algebra are primitive

When the trivial path is the only path from `v` to `v`, the corner ring `eᵥ kQ eᵥ` of the vertex
idempotent at `v` is as small as it can be: `eᵥ f eᵥ` is a scalar multiple of `eᵥ`
(`TauCeti.vertexIdempotent_mul_mul_vertexIdempotent`), so the corner ring is a copy of `k`. As soon
as `0` and `1` are the only idempotents of `k` — that is, as soon as `1` is a primitive idempotent
of `k`, which holds over a domain and over a local ring (`TauCeti.isPrimitiveIdempotent_one`) — the
only idempotents of that corner are therefore `0` and `eᵥ`, which is exactly primitivity of `eᵥ`.

The path hypothesis is local to `v`, cycles elsewhere in the quiver being irrelevant; an acyclic
quiver supplies it at every vertex through `TauCeti.Quiver.IsAcyclic.eq_nil`.

Read through `TauCeti.isPrimitiveIdempotent_iff_isIndecomposableModule`, this says that the left
ideal `kQ eᵥ` — the indecomposable projective `Pᵥ` — is an indecomposable module. That the
corresponding *representation* `TauCeti.indecProjRep` is indecomposable is already known
categorically (`TauCeti.Quiver.Representation.indecomposable_indecProjRep`); the statement here is
the module-level one, about the left ideal of `kQ` itself, and it is the input to the
primitive-idempotent decomposition of `1 = ∑ᵥ eᵥ`.

The path hypothesis is what the proof needs, not what the statement needs. With an oriented cycle
through `v` the corner ring is the monoid algebra of the monoid of paths `v → v`, which is free on
the loops at `v` that do not return to `v` in between; a free associative algebra over a domain is
a domain, so `0` and `eᵥ` remain its only idempotents and `eᵥ` remains primitive — for the one-loop
quiver, where `kQ ≅ k[X]` and the single vertex idempotent is `1`, this is just that `k[X]` is a
domain. What the hypothesis buys is the scalar corner computation run here, which is unavailable in
that generality.

## Main results

* `TauCeti.isPrimitiveIdempotent_vertexIdempotent`: **a vertex idempotent of the path algebra of a
  finite quiver is primitive** as soon as the trivial path is the only path at its vertex and `1`
  is primitive in the coefficient ring.
* `TauCeti.isIndecomposableModule_span_singleton_vertexIdempotent`: consequently the left ideal
  `kQ eᵥ` is an indecomposable `kQ`-module.

Primitivity of `eᵥ` is a semiring-level statement, and is proved here directly from the definition,
transporting a decomposition of `eᵥ` to one of `1` in the coefficient ring. Additive inverses enter
only with the corollary, the module characterization asking for a ring.

## References

This supplies the vertex-idempotent instance of the primitive idempotents of Layer 3A in
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose Layer 1 identifies
`kQ eᵥ` with the indecomposable projective `Pᵥ`.
-/

public section

namespace TauCeti

open PathAlgebra

universe u v w

variable {k : Type w} {Q : Type u} [Quiver.{v} Q] [Finite Q]

section Semiring

variable [Semiring k]

/-- **A vertex idempotent with no nontrivial path at its vertex is primitive.** Both summands of a
decomposition of `eᵥ` lie in the corner ring `eᵥ kQ eᵥ`, hence are the trivial path at `v` carrying
a scalar coefficient; reading off those coefficients turns the decomposition into a decomposition
of `1` in the coefficient ring, where `1` is primitive. -/
theorem isPrimitiveIdempotent_vertexIdempotent (hk : IsPrimitiveIdempotent (1 : k)) (v : Q)
    (h : ∀ p : Quiver.Path v v, p = Quiver.Path.nil) :
    IsPrimitiveIdempotent (vertexIdempotent k v : pathAlgebra k Q) := by
  have := hk.nontrivial
  have hmul : ∀ a b : k, (single ⟨v, v, Quiver.Path.nil⟩ a *
      single ⟨v, v, Quiver.Path.nil⟩ b : pathAlgebra k Q)
        = single ⟨v, v, Quiver.Path.nil⟩ (a * b) := fun a b ↦ by
    rw [single_mul_single_of_comp, Quiver.Path.comp_nil]
  have hinj : ∀ a b : k, (single ⟨v, v, Quiver.Path.nil⟩ a : pathAlgebra k Q)
      = single ⟨v, v, Quiver.Path.nil⟩ b → a = b := fun a b hab ↦ by
    simpa using congrArg
      (fun g : pathAlgebra k Q ↦ (pathAlgebraBasis k Q).repr g ⟨v, v, Quiver.Path.nil⟩) hab
  have hcorner : ∀ f : pathAlgebra k Q, vertexIdempotent k v * f = f →
      f * vertexIdempotent k v = f → ∃ c : k, f = single ⟨v, v, Quiver.Path.nil⟩ c :=
    fun f hef hfe ↦ ⟨_, by
      have hf := vertexIdempotent_mul_mul_vertexIdempotent v h f
      rwa [hef, hfe, vertexIdempotent_eq_single, smul_single, mul_one] at hf⟩
  refine ⟨vertexIdempotent_mul_self v, vertexIdempotent_ne_zero v, ?_⟩
  intro f₁ f₂ h₁ h₂ h₁₂ h₂₁ hsum
  obtain ⟨c₁, rfl⟩ := hcorner f₁ (by rw [← hsum, add_mul, h₁.eq, h₂₁, add_zero])
    (by rw [← hsum, mul_add, h₁.eq, h₁₂, add_zero])
  obtain ⟨c₂, rfl⟩ := hcorner f₂ (by rw [← hsum, add_mul, h₁₂, h₂.eq, zero_add])
    (by rw [← hsum, mul_add, h₂₁, h₂.eq, zero_add])
  have hc₁ : c₁ * c₁ = c₁ := hinj _ _ (by rw [← hmul]; exact h₁.eq)
  have hc₂ : c₂ * c₂ = c₂ := hinj _ _ (by rw [← hmul]; exact h₂.eq)
  have hc₁₂ : c₁ * c₂ = 0 := hinj _ _ (by rw [← hmul, h₁₂, single_zero])
  have hc₂₁ : c₂ * c₁ = 0 := hinj _ _ (by rw [← hmul, h₂₁, single_zero])
  have hcsum : c₁ + c₂ = 1 := hinj _ _ (by rw [single_add, hsum, vertexIdempotent_eq_single])
  exact (hk.eq_zero_or_eq_zero_of_add hc₁ hc₂ hc₁₂ hc₂₁ hcsum).imp
    (fun hz ↦ by rw [hz, single_zero]) fun hz ↦ by rw [hz, single_zero]

end Semiring

/-- **The indecomposable projective `Pᵥ = kQ eᵥ` is an indecomposable module**, when the trivial
path is the only path from `v` to itself: its generator is then a primitive idempotent. -/
theorem isIndecomposableModule_span_singleton_vertexIdempotent [Ring k]
    (hk : IsPrimitiveIdempotent (1 : k)) (v : Q)
    (h : ∀ p : Quiver.Path v v, p = Quiver.Path.nil) :
    IsIndecomposableModule (pathAlgebra k Q)
      (Ideal.span {(vertexIdempotent k v : pathAlgebra k Q)}) :=
  (isPrimitiveIdempotent_vertexIdempotent hk v h).isIndecomposableModule

end TauCeti
