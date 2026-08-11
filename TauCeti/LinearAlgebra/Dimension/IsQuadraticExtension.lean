/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Generators of a quadratic extension

Mathlib's `Algebra.IsQuadraticExtension K L` records that `L/K` has degree two but says nothing
about the elements realising that degree. This file supplies the facts a consumer needs in
order to *choose* and *change* a generator:

`Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap`: a generator exists at all, so a
construction over `L/K` may pick one.
`Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul`: any two generators of a
quadratic extension differ by `θ' = b + aθ` with `a ≠ 0`, so a statement proved for one generator
transfers to every other. This is what makes a construction defined by "pick any `θ ∈ L ∖ K`"
well posed up to the ambiguity that `b + aθ` describes.
`linearIndependent_one_of_notMem_range_algebraMap` is the linear-algebra step behind the second.

Two of the three ask for no field structure on `L`, and each is stated at the weakest level its
proof supports. `Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap` needs only a
*semiring*, the level Mathlib states `Algebra.IsQuadraticExtension` itself at, because it sees
`L` only as a free `K`-module of rank two and derives nontriviality from that rank rather than
assuming it. `linearIndependent_one_of_notMem_range_algebraMap` carries no rank hypothesis at
all — its argument is just that `θ` is not a `K`-multiple of `1`, so it does ask for `L`
nontrivial — but it stops at a *ring*, because the `LinearIndependent.pair_iff'` it applies is
stated over an `AddCommGroup`. So both cover the split and non-reduced quadratic algebras
`K × K` and `K[X]/(X²)`. Only `exists_eq_algebraMap_add_algebraMap_mul` asks for a field.

These are consumed by the extension quadratic twist in
`TauCeti/AlgebraicGeometry/EllipticCurve/QuadraticTwist.lean`, which advances
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 5 (twists).

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/LinearAlgebra/Dimension/IsQuadraticExtension.lean` at the roadmap's pin
`bc2fe8ff7396`, FLT PR #1088, Apache 2.0). That file's own header reads
`Authors: Kevin Buzzard, Claude`; following this repository's convention for adapted material,
the upstream authorship is credited here rather than in the copyright header. Only the results
the twist consumes are ported; the rest of the source file — which restates
`Algebra.IsQuadraticExtension` itself, already in Mathlib — is not needed.
-/

public section

variable (K L : Type*) [Field K]

/-- `1` and any element lying outside the base field are linearly independent over the base
field. The ambient algebra need not be a field — only a nontrivial ring, since the argument
is just that `θ` is not a `K`-multiple of `1`. -/
theorem linearIndependent_one_of_notMem_range_algebraMap [Ring L] [Nontrivial L] [Algebra K L]
    {θ : L} (hθ : θ ∉ Set.range (algebraMap K L)) : LinearIndependent K ![(1 : L), θ] :=
  (LinearIndependent.pair_iff' one_ne_zero).mpr fun a ha ↦
    hθ ⟨a, by rwa [Algebra.algebraMap_eq_smul_one]⟩

/-- A quadratic algebra has a generator: some element lies outside the base field. Were every
element in the image of `algebraMap` the algebra would have rank one, contradicting
`finrank = 2`. This is what lets a construction over `L/K` *choose* a generator. It needs only a
semiring, the level `Algebra.IsQuadraticExtension` is stated at: `L` is free of rank `2` over the
field `K` either way, nontriviality follows from that rank, and the injectivity of `algebraMap`
comes from `K` being simple. -/
theorem Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap [Semiring L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] : ∃ θ : L, θ ∉ Set.range (algebraMap K L) := by
  have h2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  have : Nontrivial L := Module.nontrivial_of_finrank_pos (R := K) (by rw [h2]; norm_num)
  by_contra! h
  have h1 : Module.finrank K L = 1 :=
    Module.finrank_of_bijective_algebraMap ⟨FaithfulSMul.algebraMap_injective K L, h⟩
  omega

variable [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L]

namespace Algebra.IsQuadraticExtension

/-- Any element of a quadratic extension `L/K` is a `K`-linear combination of `1` and a given
generator `θ`, and the `θ`-coefficient is nonzero if the element also lies outside `K`. So any
two generators differ by `θ' = b + aθ` with `a ≠ 0`. -/
theorem exists_eq_algebraMap_add_algebraMap_mul {θ θ' : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) (hθ' : θ' ∉ Set.range (algebraMap K L)) :
    ∃ a b : K, a ≠ 0 ∧ θ' = algebraMap K L b + algebraMap K L a * θ := by
  have hli := linearIndependent_one_of_notMem_range_algebraMap K L hθ
  have hmem : θ' ∈ Submodule.span K (Set.range ![(1 : L), θ]) := by
    rw [hli.span_eq_top_of_card_eq_finrank
      (by rw [Fintype.card_fin]; exact (finrank_eq_two K L).symm)]
    trivial
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hmem
  obtain ⟨c, d, hcd⟩ := hmem
  refine ⟨d, c, fun hd ↦ hθ' ⟨c, ?_⟩, ?_⟩
  · rw [← hcd, hd, zero_smul, add_zero, Algebra.algebraMap_eq_smul_one]
  · rw [← hcd, Algebra.smul_def, Algebra.smul_def, mul_one]

end Algebra.IsQuadraticExtension

end
