/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Radical
public import TauCeti.RingTheory.PrimitiveIdempotent

/-!
# The vertex idempotents of an acyclic path algebra are primitive

Over a finite acyclic quiver the corner ring `eᵥ kQ eᵥ` of a vertex idempotent is as small as it
can be: the only path from `v` to `v` is the trivial one, so `eᵥ f eᵥ` is a scalar multiple of `eᵥ`
(`TauCeti.vertexIdempotent_mul_mul_vertexIdempotent`) and the corner ring is a copy of `k`. Its
only idempotents are therefore `0` and `eᵥ`, which is exactly primitivity of `eᵥ`.

Read through `TauCeti.isPrimitiveIdempotent_iff_isIndecomposableModule`, this says that the left
ideal `kQ eᵥ` — the indecomposable projective `Pᵥ` — is an indecomposable module. That the
corresponding *representation* `TauCeti.indecProjRep` is indecomposable is already known
categorically (`TauCeti.Quiver.Representation.indecomposable_indecProjRep`); the statement here is
the module-level one, about the left ideal of `kQ` itself, and it is the input to the
primitive-idempotent decomposition of `1 = ∑ᵥ eᵥ`.

Acyclicity is genuinely needed: for the one-loop quiver `kQ ≅ k[X]` the single vertex idempotent is
`1`, whose corner ring is all of `k[X]`; that ring has no nontrivial idempotents either, so `1`
stays primitive there, but the corner computation this file runs is unavailable, and over a quiver
with an oriented cycle a vertex idempotent can fail to be primitive.

## Main results

* `TauCeti.isPrimitiveIdempotent_vertexIdempotent`: **the vertex idempotents of the path algebra of
  a finite acyclic quiver are primitive.**
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

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Finite Q]

/-- **The vertex idempotents of a finite acyclic path algebra are primitive.** An idempotent `f` of
the corner ring `eᵥ kQ eᵥ` is `c • eᵥ` for a scalar `c`, and idempotence of `f` forces `c² = c`,
hence `c = 0` or `c = 1`. -/
theorem isPrimitiveIdempotent_vertexIdempotent (h : Quiver.IsAcyclic Q) (v : Q) :
    IsPrimitiveIdempotent (vertexIdempotent k v : pathAlgebra k Q) := by
  refine isPrimitiveIdempotent_of_forall (isIdempotentElem_vertexIdempotent v)
    (vertexIdempotent_ne_zero v) fun f hf hef hfe ↦ ?_
  set c := (pathAlgebraBasis k Q).repr f ⟨v, v, Quiver.Path.nil⟩ with hc
  have hfeq : f = c • (vertexIdempotent k v : pathAlgebra k Q) := by
    rw [hc, ← vertexIdempotent_mul_mul_vertexIdempotent h v f, hef, hfe]
  have hsq : (c * c) • (vertexIdempotent k v : pathAlgebra k Q)
      = c • vertexIdempotent k v := by
    have hff := hf.eq
    rwa [hfeq, smul_mul_smul_comm, vertexIdempotent_mul_self] at hff
  have hcc : c * c = c := by
    have hzero : (c * c - c) • (vertexIdempotent k v : pathAlgebra k Q) = 0 := by
      rw [sub_smul, hsq, sub_self]
    rcases smul_eq_zero.mp hzero with hsub | hev
    · exact sub_eq_zero.mp hsub
    · exact absurd hev (vertexIdempotent_ne_zero v)
  have hfactor : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hcc, sub_self]
  rcases mul_eq_zero.mp hfactor with hzero | hone
  · exact Or.inl (by rw [hfeq, hzero, zero_smul])
  · exact Or.inr (by rw [hfeq, sub_eq_zero.mp hone, one_smul])

/-- **The indecomposable projective `Pᵥ = kQ eᵥ` is an indecomposable module**, over a finite
acyclic quiver: its generator is a primitive idempotent. -/
theorem isIndecomposableModule_span_singleton_vertexIdempotent (h : Quiver.IsAcyclic Q) (v : Q) :
    IsIndecomposableModule (pathAlgebra k Q)
      (Ideal.span {(vertexIdempotent k v : pathAlgebra k Q)}) :=
  (isPrimitiveIdempotent_vertexIdempotent h v).isIndecomposableModule

end TauCeti
