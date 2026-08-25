/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Module.ZMod
public import TauCeti.NumberTheory.Multiquadratic.Galois.Group

/-!
# The subfield lattice of a multiquadratic field

For square roots `root i` of radicands `d i` over a field `K` with `2 ≠ 0`, square-class
independence makes `M = K(rootᵢ : i)` Galois with group `(ℤ/2)ⁿ`
(`TauCeti.NumberTheory.Multiquadratic.Galois.Group`). The fundamental theorem of Galois theory
turns the lattice of intermediate fields of `M/K` into the (order-reversed) lattice of subgroups
of `Gal(M/K)`; transporting along the isomorphism `Gal(M/K) ≃ (ℤ/2)ⁿ` lands in the subgroups of
`ι → ℤ/2`, and an additive subgroup of an `𝔽₂`-vector space is the same thing as an
`𝔽₂`-subspace. Composing these identifications gives an order-reversing bijection between the
intermediate fields of `M/K` and the `𝔽₂`-subspaces of `ι → ℤ/2`.

This is the lattice-of-subfields layer of the multiquadratic roadmap: the dictionary
"subfields ↔ subspaces of `𝔽₂ⁿ`" that organises, for instance, the quadratic subfields and the
genus-field constructions.

## Main results

* `TauCeti.Multiquadratic.intermediateFieldEquivSubmodule`: for square-class independent
  radicands, the order-reversing bijection
  `IntermediateField K M ≃o (Submodule (ZMod 2) (ι → ℤ/2))ᵒᵈ`.
* `TauCeti.Multiquadratic.card_intermediateField_adjoin_range`: its cardinality reading — the
  number of intermediate fields of `M/K` is the number of `𝔽₂`-subspaces of `ι → ℤ/2`.

## Provenance

The Galois-group identification this builds on is migrated, with the rest of the multiquadratic
Layer 0, from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization of
L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture. The subfield/subspace
dictionary itself assembles Mathlib's Galois correspondence
(`IsGalois.intermediateFieldEquivSubgroup`) with the subgroup ↔ subspace order isomorphisms for
`𝔽₂`-vector spaces (`Subgroup.toAddSubgroup'`, `AddSubgroup.toZModSubmodule`).
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}
  {d : ι → K} {root : ι → L}

/-- **The subfield lattice of a multiquadratic field is the `𝔽₂`-subspace lattice of `(ℤ/2)ⁿ`.**
If no nonempty subset product of the radicands `d i` is a square in `K` (and `2 ≠ 0`), then the
intermediate fields of `M = K(rootᵢ : i)` over `K` correspond, order-reversingly, to the
`𝔽₂`-subspaces of `ι → ℤ/2`: a larger subfield is fixed by a smaller group, hence matches a
smaller subspace.

The bijection is the composite of Mathlib's Galois correspondence
`IsGalois.intermediateFieldEquivSubgroup` (intermediate fields ↔ subgroups of the Galois group,
dualised), the Galois-group isomorphism `galoisGroupEquiv` (`Gal(M/K) ≃ Multiplicative (ι → ℤ/2)`),
and the identification of subgroups of an `𝔽₂`-vector space with its subspaces. -/
noncomputable def intermediateFieldEquivSubmodule [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i)) :
    IntermediateField K (adjoin K (Set.range root)) ≃o
      (Submodule (ZMod 2) (ι → ZMod 2))ᵒᵈ :=
  haveI := isSplittingField hroot
  haveI : FiniteDimensional K (adjoin K (Set.range root)) :=
    Polynomial.IsSplittingField.finiteDimensional _ (definingPolynomial d)
  haveI := isGalois hroot
  IsGalois.intermediateFieldEquivSubgroup.trans
    (OrderIso.dual
      ((galoisGroupEquiv hroot hindep).mapSubgroup.trans
        (Subgroup.toAddSubgroup'.trans (AddSubgroup.toZModSubmodule 2))))

/-- The subspace attached to an intermediate field is the image of its fixing subgroup under the
sign-pattern Galois-group equivalence. -/
@[simp] theorem intermediateFieldEquivSubmodule_apply_ofDual [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    (intermediateFieldEquivSubmodule hroot hindep F).ofDual =
      AddSubgroup.toZModSubmodule 2
        (Subgroup.toAddSubgroup'
          ((galoisGroupEquiv hroot hindep).mapSubgroup F.fixingSubgroup)) :=
by
  rw [intermediateFieldEquivSubmodule]
  rfl

/-- A sign vector belongs to the subspace attached to an intermediate field exactly when it is the
sign pattern of an automorphism fixing that field. -/
theorem mem_intermediateFieldEquivSubmodule_apply_ofDual_iff [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) (v : ι → ZMod 2) :
    v ∈ (intermediateFieldEquivSubmodule hroot hindep F).ofDual ↔
      ∃ σ ∈ F.fixingSubgroup, signPattern root σ = v := by
  rw [intermediateFieldEquivSubmodule]
  simp [Subgroup.mem_map]

/-- The intermediate field attached to a subspace is the fixed field of the automorphisms whose
sign patterns lie in that subspace. -/
@[simp] theorem mem_intermediateFieldEquivSubmodule_symm_apply_iff [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (U : Submodule (ZMod 2) (ι → ZMod 2)) (x : adjoin K (Set.range root)) :
    x ∈ (intermediateFieldEquivSubmodule hroot hindep).symm (OrderDual.toDual U) ↔
      ∀ σ, signPattern root σ ∈ U → σ x = x := by
  suffices (∀ v ∈ U, ((galoisGroupEquiv hroot hindep).symm (Multiplicative.ofAdd v)) x = x) ↔
      ∀ σ, signPattern root σ ∈ U → σ x = x by
    simpa [intermediateFieldEquivSubmodule] using this
  constructor
  · intro h σ hσ
    have hσeq : (galoisGroupEquiv hroot hindep).symm
        (Multiplicative.ofAdd (signPattern root σ)) = σ := by
      apply (galoisGroupEquiv hroot hindep).injective
      rw [MulEquiv.apply_symm_apply, galoisGroupEquiv_apply]
    simpa [hσeq] using h (signPattern root σ) hσ
  · intro h v hv
    exact h ((galoisGroupEquiv hroot hindep).symm (Multiplicative.ofAdd v)) (by
      have happ := (galoisGroupEquiv hroot hindep).apply_symm_apply (Multiplicative.ofAdd v)
      rw [galoisGroupEquiv_apply] at happ
      simpa [Multiplicative.ofAdd.injective happ] using hv)

/-- **The number of subfields of a multiquadratic field.** Under square-class independence, the
intermediate fields of `M = K(rootᵢ : i)` over `K` are in bijection with the `𝔽₂`-subspaces of
`ι → ℤ/2`, so there are exactly as many of them. (For `|ι| = n` this count is the number of
subspaces of `𝔽₂ⁿ`, the Galois number `Gₙ`.) -/
theorem card_intermediateField_adjoin_range [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i)) :
    Nat.card (IntermediateField K (adjoin K (Set.range root)))
      = Nat.card (Submodule (ZMod 2) (ι → ZMod 2)) :=
  Nat.card_congr <|
    (intermediateFieldEquivSubmodule hroot hindep).toEquiv.trans
      (OrderDual.toDual (α := Submodule (ZMod 2) (ι → ZMod 2))).symm

end TauCeti.Multiquadratic
