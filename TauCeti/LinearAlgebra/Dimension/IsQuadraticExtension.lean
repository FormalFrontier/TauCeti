/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
`Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul`: every element is `b + aθ`
for a fixed generator `θ`, the coordinate presentation over the basis `1, θ` (used by the
quadratic field-norm computation).
`Algebra.IsQuadraticExtension.exists_ne_zero_eq_algebraMap_add_algebraMap_mul`: for a *second*
generator the `θ`-coefficient is nonzero, so any two generators differ by `θ' = b + aθ` with
`a ≠ 0` and a statement proved for one transfers to every other.
`linearIndependent_one_of_notMem_range_algebraMap` is the linear-algebra step behind them.

None asks for a field on `L`, and each is stated at the weakest level its proof supports. The
generator-existence and both coordinate theorems need only a *semiring* — the level Mathlib states
`Algebra.IsQuadraticExtension` itself at — the ring structure the spanning needs being borrowed
locally through `Algebra.semiringToRing`. `linearIndependent_one_of_notMem_range_algebraMap`
carries no rank hypothesis at all — its argument is just that `θ` is not a `K`-multiple of `1`, so
it asks for `L` nontrivial — but it stops at a *ring*, because the `LinearIndependent.pair_iff'`
it applies is stated over an `AddCommGroup`. So all cover the split and non-reduced quadratic
algebras `K × K` and `K[X]/(X²)`.

These are consumed by the extension quadratic twist in
`TauCeti/AlgebraicGeometry/EllipticCurve/QuadraticTwist.lean`, which advances
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 5 (twists), and by the quadratic field-norm
computation in `TauCeti/NumberTheory/NumberField/Quadratic/Norm.lean`.

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

/-- **Every element of a quadratic extension is `b + aθ`** for a fixed generator `θ`: the basis
`1, θ` spans `L` over `K`. The `θ`-coefficient may vanish, exactly when the element lies in the
base field; `exists_ne_zero_eq_algebraMap_add_algebraMap_mul` records that it does not for a second
generator. The spanning is `K`-linear algebra, so this needs only a *semiring* on `L`. -/
theorem Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul [Semiring L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) (x : L) :
    ∃ a b : K, x = algebraMap K L b + algebraMap K L a * θ := by
  let _ : Ring L := Algebra.semiringToRing K
  have h2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  have : Nontrivial L := Module.nontrivial_of_finrank_pos (R := K) (by rw [h2]; norm_num)
  have hli := linearIndependent_one_of_notMem_range_algebraMap K L hθ
  have hmem : x ∈ Submodule.span K (Set.range ![(1 : L), θ]) := by
    rw [hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin]; exact h2.symm)]
    trivial
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hmem
  obtain ⟨c, d, hcd⟩ := hmem
  exact ⟨d, c, by rw [← hcd, Algebra.smul_def, Algebra.smul_def, mul_one]⟩

/-- Any element of a quadratic extension `L/K` is a `K`-linear combination of `1` and a given
generator `θ`, and the `θ`-coefficient is nonzero if the element also lies outside `K`. So any
two generators differ by `θ' = b + aθ` with `a ≠ 0`. -/
theorem Algebra.IsQuadraticExtension.exists_ne_zero_eq_algebraMap_add_algebraMap_mul [Semiring L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] {θ θ' : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) (hθ' : θ' ∉ Set.range (algebraMap K L)) :
    ∃ a b : K, a ≠ 0 ∧ θ' = algebraMap K L b + algebraMap K L a * θ := by
  obtain ⟨a, b, hab⟩ :=
    Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul K L hθ θ'
  refine ⟨a, b, ?_, hab⟩
  rintro rfl
  exact hθ' ⟨b, by rw [hab, map_zero, zero_mul, add_zero]⟩

end
