/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.FieldTheory.KrullTopology
public import TauCeti.NumberTheory.Multiquadratic.Subfield.Lattice

/-!
# Degrees in the multiquadratic subfield lattice

For square roots `root i` of radicands `d i` over a field `K` with `2 ≠ 0`, square-class
independence makes `M = K(rootᵢ : i)` Galois with group `(ℤ/2)ⁿ`, and the order-reversing
bijection `TauCeti.Multiquadratic.intermediateFieldEquivSubmodule` matches each intermediate field
`F` of `M / K` with an `𝔽₂`-subspace `U` of `ι → ℤ/2`
(`TauCeti.NumberTheory.Multiquadratic.Subfield.Lattice`). That bijection records *which* subfields
exist; this file records their **degrees**.

Galois theory reads the degree of an intermediate field as the index of its fixing subgroup
(`IntermediateField.finrank_eq_fixingSubgroup_index`), and the fixing subgroup is exactly the
subgroup of `(ℤ/2)ⁿ` carried by `U`. Counting gives the clean reciprocal relation

`[F : K] · |U| = 2ⁿ`,

equivalently `[F : K] = 2 ^ (n - dim U)`: a larger subfield matches a smaller subspace, and the
two codimensions add up to `n`. The headline consequence is the identification of the **quadratic
subfields**: `F` has degree `2` over `K` exactly when its subspace `U` is a hyperplane,
`dim U + 1 = n`.

## Main results

* `TauCeti.Multiquadratic.finrank_mul_card_intermediateFieldEquivSubmodule`:
  `[F : K] · |U| = 2ⁿ`, the degree of an intermediate field times the cardinality of its subspace.
* `TauCeti.Multiquadratic.finrank_mul_two_pow_finrank_intermediateFieldEquivSubmodule`: the same
  relation read through the dimension of `U`, `[F : K] · 2 ^ dim U = 2ⁿ`.
* `TauCeti.Multiquadratic.finrank_intermediateField_eq_two_pow`: the explicit-power form
  `[F : K] = 2 ^ (n - dim U)`.
* `TauCeti.Multiquadratic.finrank_intermediateField_eq_two_iff`: `F` is a quadratic subfield of `M`
  exactly when its subspace is a hyperplane, `dim U + 1 = n`.

## Provenance

The subfield/subspace dictionary this refines is migrated, with the rest of the multiquadratic
Layer 0, from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization of
L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture. The degree reading
assembles Mathlib's Galois index formula (`IntermediateField.finrank_eq_fixingSubgroup_index`) with
the subgroup-cardinality bookkeeping (`Subgroup.index_mul_card`, `Subgroup.card_mapSubgroup`).
-/

public section

open IntermediateField Module

namespace TauCeti.Multiquadratic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}
  {d : ι → K} {root : ι → L}

/-- The cardinality of an `𝔽₂`-subspace `U` of `ι → ℤ/2` is `2` to its dimension. -/
private theorem card_submodule_eq_pow_finrank [Finite ι]
    (U : Submodule (ZMod 2) (ι → ZMod 2)) :
    Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI := Fintype.ofFinite ι
  letI : Fintype U := Fintype.ofFinite U
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := U), ZMod.card]

/-- The subspace attached to an intermediate field `F` of `M = K(rootᵢ : i)` has the same
cardinality as the fixing subgroup of `F`: both reinterpret the same set of automorphisms, one as a
subgroup of `Gal(M/K)` and one as an `𝔽₂`-subspace of `ι → ℤ/2`. -/
private theorem card_intermediateFieldEquivSubmodule_ofDual [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    Nat.card (intermediateFieldEquivSubmodule hroot hindep F).ofDual
      = Nat.card F.fixingSubgroup := by
  rw [intermediateFieldEquivSubmodule_apply_ofDual hroot hindep F]
  calc
    Nat.card (AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup'
        ((galoisGroupEquiv hroot hindep).mapSubgroup F.fixingSubgroup)))
        = Nat.card (Subgroup.toAddSubgroup'
            ((galoisGroupEquiv hroot hindep).mapSubgroup F.fixingSubgroup)) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun _ => AddSubgroup.mem_toZModSubmodule 2)
    _ = Nat.card ((galoisGroupEquiv hroot hindep).mapSubgroup F.fixingSubgroup) :=
      Nat.card_congr (Multiplicative.ofAdd.subtypeEquiv fun a =>
        Subgroup.mem_toAddSubgroup' _ a)
    _ = Nat.card F.fixingSubgroup :=
      Subgroup.card_mapSubgroup (H := F.fixingSubgroup) (galoisGroupEquiv hroot hindep)

/-- **The degree of an intermediate field times the size of its subspace is `2ⁿ`.** Under
square-class independence, an intermediate field `F` of `M = K(rootᵢ : i)` and its subspace
`U = (intermediateFieldEquivSubmodule F).ofDual` of `ι → ℤ/2` satisfy `[F : K] · |U| = 2 ^ |ι|`.
The Galois correspondence is order-reversing, so a larger subfield matches a smaller subspace and
the two sizes multiply to the full degree. -/
theorem finrank_mul_card_intermediateFieldEquivSubmodule [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    Module.finrank K F
        * Nat.card (intermediateFieldEquivSubmodule hroot hindep F).ofDual
      = 2 ^ Nat.card ι := by
  haveI := isSplittingField hroot
  haveI : FiniteDimensional K (adjoin K (Set.range root)) :=
    Polynomial.IsSplittingField.finiteDimensional _ (definingPolynomial d)
  haveI := isGalois hroot
  rw [card_intermediateFieldEquivSubmodule_ofDual hroot hindep F,
    IntermediateField.finrank_eq_fixingSubgroup_index
      (F := K) (E' := adjoin K (Set.range root)) F,
    Subgroup.index_mul_card F.fixingSubgroup]
  exact card_aut_adjoin_range hroot hindep

/-- **The degree of an intermediate field through the dimension of its subspace.** The reciprocal
relation `[F : K] · |U| = 2ⁿ` read with `|U| = 2 ^ dim U`: `[F : K] · 2 ^ dim U = 2 ^ |ι|`. -/
theorem finrank_mul_two_pow_finrank_intermediateFieldEquivSubmodule [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    Module.finrank K F
        * 2 ^ Module.finrank (ZMod 2) (intermediateFieldEquivSubmodule hroot hindep F).ofDual
      = 2 ^ Nat.card ι := by
  rw [← card_submodule_eq_pow_finrank,
    finrank_mul_card_intermediateFieldEquivSubmodule hroot hindep F]

/-- **The degree of an intermediate field is `2` to the codimension of its subspace.** Under
square-class independence, an intermediate field `F` of `M = K(rootᵢ : i)` has
`[F : K] = 2 ^ (|ι| - dim U)`, where `U` is the `𝔽₂`-subspace attached to `F`. This is the
explicit-power form of the reciprocal relation `[F : K] · |U| = 2ⁿ`. -/
theorem finrank_intermediateField_eq_two_pow [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    Module.finrank K F = 2 ^ (Nat.card ι
        - Module.finrank (ZMod 2) (intermediateFieldEquivSubmodule hroot hindep F).ofDual) := by
  classical
  letI := Fintype.ofFinite ι
  have h := finrank_mul_two_pow_finrank_intermediateFieldEquivSubmodule hroot hindep F
  set m := Module.finrank (ZMod 2) (intermediateFieldEquivSubmodule hroot hindep F).ofDual
  have hle : m ≤ Nat.card ι := by
    rw [Nat.card_eq_fintype_card, ← Module.finrank_fintype_fun_eq_card (R := ZMod 2) (η := ι)]
    exact Submodule.finrank_le _
  have hsplit : (2 : ℕ) ^ Nat.card ι = 2 ^ (Nat.card ι - m) * 2 ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hsplit] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

/-- **The quadratic subfields are the hyperplanes.** Under square-class independence, an
intermediate field `F` of `M = K(rootᵢ : i)` has degree `2` over `K` exactly when its subspace
`U` of `ι → ℤ/2` is a hyperplane, i.e. `dim U + 1 = |ι|`. This is the lattice reading of "the
quadratic subfields of a multiquadratic field". -/
theorem finrank_intermediateField_eq_two_iff [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    Module.finrank K F = 2 ↔
      Module.finrank (ZMod 2) (intermediateFieldEquivSubmodule hroot hindep F).ofDual + 1
        = Nat.card ι := by
  have h := finrank_mul_two_pow_finrank_intermediateFieldEquivSubmodule hroot hindep F
  set m := Module.finrank (ZMod 2) (intermediateFieldEquivSubmodule hroot hindep F).ofDual
  set n := Nat.card ι
  constructor
  · intro hF
    rw [hF] at h
    have h2 : (2 : ℕ) ^ (m + 1) = 2 ^ n := by rw [pow_succ, mul_comm]; exact h
    exact Nat.pow_right_injective (le_refl 2) h2
  · intro hmn
    have h2 : (2 : ℕ) ^ n = 2 * 2 ^ m := by rw [← hmn, pow_succ, mul_comm]
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h

end TauCeti.Multiquadratic
