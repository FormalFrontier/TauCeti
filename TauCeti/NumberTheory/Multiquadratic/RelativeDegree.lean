/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Subfield.Degree

/-!
# Relative degrees in the multiquadratic subfield lattice

For square roots `root i` of radicands `d i` over a field `K` with `2 ≠ 0`, square-class
independence makes `M = K(rootᵢ : i)` Galois with group `(ℤ/2)ⁿ`, and the order-reversing
bijection `TauCeti.Multiquadratic.intermediateFieldEquivSubmodule` matches each intermediate field
`F` of `M / K` with an `𝔽₂`-subspace `U` of `ι → ℤ/2`
(`TauCeti.NumberTheory.Multiquadratic.Subfield.Lattice`).
`TauCeti.NumberTheory.Multiquadratic.Subfield.Degree` records the **absolute** degree
`[F : K] = 2 ^ (n - dim U)`; this file records the complementary **relative** degree of the whole
multiquadratic field over `F`.

The tower law `[M : K] = [F : K] · [M : F]` turns the absolute reading `[F : K] · 2 ^ dim U = 2ⁿ`
into the relative one: cancelling `[F : K]` leaves

`[M : F] = 2 ^ dim U`.

So the two codimensions are genuinely complementary — `[F : K]` grows with the codimension of `U`,
`[M : F]` grows with its dimension, and their product is the full degree `2ⁿ`. The headline reading
is the dual of the "quadratic subfields are the hyperplanes" characterisation: `M` is quadratic
over `F` exactly when `U` is a line, `dim U = 1`. In particular, over any quadratic subfield of a
degree-`2ⁿ` multiquadratic field, the multiquadratic field itself has degree `2 ^ (n - 1)`, the
relative degree the genus-field constructions consume.

## Main results

* `TauCeti.Multiquadratic.finiteDimensional_top_over_intermediateField`: `M` is finite-dimensional
  over any intermediate field `F`, the instance the relative degrees are read against.
* `TauCeti.Multiquadratic.finrank_intermediateField_mul_finrank_top`: the tower identity
  `[F : K] · [M : F] = 2ⁿ`.
* `TauCeti.Multiquadratic.finrank_top_over_intermediateField`: `[M : F] = 2 ^ dim U`, the relative
  degree of `M` over an intermediate field `F` through the dimension of its subspace `U`.
* `TauCeti.Multiquadratic.finrank_top_over_intermediateField_eq_two_iff`: `M` is quadratic over `F`
  exactly when `U` is a line, `dim U = 1`.
* `TauCeti.Multiquadratic.finrank_top_over_intermediateField_of_finrank_eq_two`: over a quadratic
  subfield, `[M : F] = 2 ^ (n - 1)`.

## Provenance

The subfield/subspace dictionary and the absolute-degree reading this refines are migrated, with the
rest of the multiquadratic Layer 0, from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization of
L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture. The relative-degree
reading assembles that absolute reading with Mathlib's tower law
(`Module.finrank_mul_finrank`).
-/

public section

open IntermediateField Module

namespace TauCeti.Multiquadratic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}
  {d : ι → K} {root : ι → L}

/-- A multiquadratic field is finite-dimensional over any intermediate field. -/
theorem finiteDimensional_top_over_intermediateField [Finite ι]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    FiniteDimensional F (adjoin K (Set.range root)) :=
  haveI := isSplittingField hroot
  haveI : FiniteDimensional K (adjoin K (Set.range root)) :=
    Polynomial.IsSplittingField.finiteDimensional _ (definingPolynomial d)
  Module.Finite.of_restrictScalars_finite K F (adjoin K (Set.range root))

/-- **The tower identity `[F : K] · [M : F] = 2ⁿ`.** Under square-class independence, an
intermediate field `F` of `M = K(rootᵢ : i)` and the whole multiquadratic field multiply their
degrees to the full degree `2 ^ |ι|`: the absolute degree `[F : K]` times the relative degree
`[M : F]`. -/
theorem finrank_intermediateField_mul_finrank_top [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    Module.finrank K F * Module.finrank F (adjoin K (Set.range root)) = 2 ^ Nat.card ι := by
  rw [Module.finrank_mul_finrank K F (adjoin K (Set.range root)),
    finrank_adjoin_range hroot hindep]

/-- **The relative degree of a multiquadratic field over an intermediate field.** Under square-class
independence, the whole multiquadratic field `M = K(rootᵢ : i)` has degree `2 ^ dim U` over an
intermediate field `F`, where `U` is the `𝔽₂`-subspace of `ι → ℤ/2` attached to `F`. This is the
reciprocal partner of `TauCeti.Multiquadratic.finrank_intermediateField_eq_two_pow`: `[F : K]` reads
the codimension of `U`, `[M : F]` reads its dimension, and their product is the full degree. -/
theorem finrank_top_over_intermediateField [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    Module.finrank F (adjoin K (Set.range root))
      = 2 ^ Module.finrank (ZMod 2) (intermediateFieldEquivSubmodule hroot hindep F).ofDual := by
  haveI := isSplittingField hroot
  haveI : FiniteDimensional K (adjoin K (Set.range root)) :=
    Polynomial.IsSplittingField.finiteDimensional _ (definingPolynomial d)
  have hpos : 0 < Module.finrank K F := Module.finrank_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [finrank_intermediateField_mul_finrank_top hroot hindep F,
    ← finrank_mul_two_pow_finrank_intermediateFieldEquivSubmodule hroot hindep F]

/-- **`M` is quadratic over `F` exactly when its subspace is a line.** Under square-class
independence, the multiquadratic field `M = K(rootᵢ : i)` has degree `2` over an intermediate field
`F` exactly when the `𝔽₂`-subspace `U` of `ι → ℤ/2` attached to `F` is a line, `dim U = 1`. This is
the dual of "the quadratic subfields are the hyperplanes"
(`TauCeti.Multiquadratic.finrank_intermediateField_eq_two_iff`). -/
theorem finrank_top_over_intermediateField_eq_two_iff [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    Module.finrank F (adjoin K (Set.range root)) = 2 ↔
      Module.finrank (ZMod 2) (intermediateFieldEquivSubmodule hroot hindep F).ofDual = 1 := by
  rw [finrank_top_over_intermediateField hroot hindep F]
  constructor
  · intro h
    have : (2 : ℕ) ^ Module.finrank (ZMod 2)
        (intermediateFieldEquivSubmodule hroot hindep F).ofDual = 2 ^ 1 := by simpa using h
    exact Nat.pow_right_injective (le_refl 2) this
  · intro h
    rw [h, pow_one]

/-- **The relative degree over a quadratic subfield is `2 ^ (n - 1)`.** Under square-class
independence, over any quadratic subfield `F` of the degree-`2ⁿ` multiquadratic field
`M = K(rootᵢ : i)`, the multiquadratic field itself has degree `2 ^ (|ι| - 1)`. This is the relative
degree that the genus-field constructions read off over the quadratic base. -/
theorem finrank_top_over_intermediateField_of_finrank_eq_two [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root)))
    (hF : Module.finrank K F = 2) :
    Module.finrank F (adjoin K (Set.range root)) = 2 ^ (Nat.card ι - 1) := by
  rw [finrank_top_over_intermediateField hroot hindep F]
  congr 1
  have := (finrank_intermediateField_eq_two_iff hroot hindep F).mp hF
  omega

end TauCeti.Multiquadratic
