/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra
public import TauCeti.RingTheory.PrimitiveIdempotent

/-!
# The vertex idempotents of a path algebra are primitive

When the trivial path is the only path from `v` to `v`, the corner ring `eᵥ kQ eᵥ` of the vertex
idempotent at `v` is as small as it can be: `eᵥ f eᵥ` is a scalar multiple of `eᵥ`
(`TauCeti.vertexIdempotent_mul_mul_vertexIdempotent`), so the corner ring is a copy of `k`. Over a
domain its only idempotents are therefore `0` and `eᵥ`, which is exactly primitivity of `eᵥ`.

The hypothesis is local to `v`, cycles elsewhere in the quiver being irrelevant; an acyclic quiver
supplies it at every vertex through `TauCeti.Quiver.IsAcyclic.eq_nil`.

Read through `TauCeti.isPrimitiveIdempotent_iff_isIndecomposableModule`, this says that the left
ideal `kQ eᵥ` — the indecomposable projective `Pᵥ` — is an indecomposable module. That the
corresponding *representation* `TauCeti.indecProjRep` is indecomposable is already known
categorically (`TauCeti.Quiver.Representation.indecomposable_indecProjRep`); the statement here is
the module-level one, about the left ideal of `kQ` itself, and it is the input to the
primitive-idempotent decomposition of `1 = ∑ᵥ eᵥ`.

The hypothesis is what the proof needs, not what the statement needs. With an oriented cycle
through `v` the corner ring is the monoid algebra of the monoid of paths `v → v`, which is free on
the loops at `v` that do not return to `v` in between; a free associative algebra is a domain, so
`0` and `eᵥ` remain its only idempotents and `eᵥ` remains primitive — for the one-loop quiver,
where `kQ ≅ k[X]` and the single vertex idempotent is `1`, this is just that `k[X]` is a domain.
What the hypothesis buys is the scalar corner computation run here, which is unavailable in that
generality.

## Main results

* `TauCeti.isPrimitiveIdempotent_vertexIdempotent`: **a vertex idempotent of the path algebra of a
  finite quiver is primitive** as soon as the trivial path is the only path at its vertex.
* `TauCeti.isIndecomposableModule_span_singleton_vertexIdempotent`: consequently the left ideal
  `kQ eᵥ` is an indecomposable `kQ`-module.

## References

This supplies the vertex-idempotent instance of the primitive idempotents of Layer 3A in
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose Layer 1 identifies
`kQ eᵥ` with the indecomposable projective `Pᵥ`.
-/

public section

namespace TauCeti

open PathAlgebra

universe u v w

variable {k : Type w} {Q : Type u} [CommRing k] [IsDomain k] [Quiver.{v} Q] [Finite Q]

/-- **A vertex idempotent with no nontrivial path at its vertex is primitive.** An idempotent `f`
of the corner ring `eᵥ kQ eᵥ` is `c • eᵥ` for a scalar `c`, and idempotence of `f` forces `c² = c`,
hence `c = 0` or `c = 1`, the coefficients having no zero divisors. -/
theorem isPrimitiveIdempotent_vertexIdempotent (v : Q)
    (h : ∀ p : Quiver.Path v v, p = Quiver.Path.nil) :
    IsPrimitiveIdempotent (vertexIdempotent k v : pathAlgebra k Q) := by
  refine isPrimitiveIdempotent_of_forall (vertexIdempotent_mul_self v)
    (vertexIdempotent_ne_zero v) fun f hf hef hfe ↦ ?_
  set c := (pathAlgebraBasis k Q).repr f ⟨v, v, Quiver.Path.nil⟩ with hc
  have hfeq : f = c • (vertexIdempotent k v : pathAlgebra k Q) := by
    rw [hc, ← vertexIdempotent_mul_mul_vertexIdempotent v h f, hef, hfe]
  have hsq : (c * c) • (vertexIdempotent k v : pathAlgebra k Q)
      = c • vertexIdempotent k v := by
    have hff := hf.eq
    rwa [hfeq, smul_mul_smul_comm, vertexIdempotent_mul_self] at hff
  have hcc : c * c = c := by
    have hrepr := congrArg
      (fun g : pathAlgebra k Q => (pathAlgebraBasis k Q).repr g ⟨v, v, Quiver.Path.nil⟩) hsq
    simpa [vertexIdempotent_eq_single, smul_single] using hrepr
  have hfactor : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hcc, sub_self]
  rcases mul_eq_zero.mp hfactor with hzero | hone
  · exact Or.inl (by rw [hfeq, hzero, zero_smul])
  · exact Or.inr (by rw [hfeq, sub_eq_zero.mp hone, one_smul])

/-- **The indecomposable projective `Pᵥ = kQ eᵥ` is an indecomposable module**, when the trivial
path is the only path from `v` to itself: its generator is then a primitive idempotent. -/
theorem isIndecomposableModule_span_singleton_vertexIdempotent (v : Q)
    (h : ∀ p : Quiver.Path v v, p = Quiver.Path.nil) :
    IsIndecomposableModule (pathAlgebra k Q)
      (Ideal.span {(vertexIdempotent k v : pathAlgebra k Q)}) :=
  (isPrimitiveIdempotent_vertexIdempotent v h).isIndecomposableModule

end TauCeti
