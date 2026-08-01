/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.RelativeDegree

/-!
# The relative Galois group of a multiquadratic field

For square roots `root i` of radicands `d i` over a field `K` with `2 ≠ 0`, square-class
independence makes `M = K(rootᵢ : i)` an abelian Galois extension of `K` with group `(ℤ/2)ⁿ`, and
`TauCeti.NumberTheory.Multiquadratic.Subfield.Lattice` matches each intermediate field `F` of
`M / K` with the `𝔽₂`-subspace `U` of `ι → ℤ/2` consisting of the sign patterns of the
automorphisms that fix `F`. `TauCeti.NumberTheory.Multiquadratic.RelativeDegree` records the
relative *degree* `[M : F] = 2 ^ dim U`; this file records the relative *group*.

Two things happen. First, a relative automorphism restricts to a `K`-automorphism, and those are
involutions, so `Gal(M/F)` has exponent dividing two; commutativity comes for free, since Mathlib's
tower instances for `IsAbelianGalois` already make both halves of the tower abelian Galois once
`TauCeti.Multiquadratic.isAbelianGalois` supplies `IsAbelianGalois K M`. So `Gal(M/F)` is again
elementary abelian, exactly as `Gal(M/K)` is.
Second, the sign pattern identifies `Gal(M/F)` precisely: restriction of scalars embeds it into
`Gal(M/K) ≃ (ℤ/2)ⁿ`, its image is exactly the subspace `U` attached to `F`, and the resulting map

`Gal(M/F) ≃* Multiplicative U`

is an isomorphism. Nothing is proved bijective by hand for this: it is Mathlib's
`IntermediateField.fixingSubgroupEquiv` composed with the restriction of
`TauCeti.Multiquadratic.galoisGroupEquiv` to the fixing subgroup of `F`, whose image the subfield
dictionary already identifies with `U`. Cardinalities then come from
`IsGalois.card_aut_eq_finrank` together with the relative degrees of
`TauCeti.NumberTheory.Multiquadratic.RelativeDegree`: `|Gal(M/F)| = 2 ^ dim U` in general, and
`|Gal(M/F)| = 2 ^ (n - 1)` over a quadratic subfield, the reading the genus-field constructions
consume.

This is the group-theoretic half of the relative picture the genus-field constructions consume: the
genus field is multiquadratic over `ℚ`, and the group the genus theory identifies with `Cl/Cl²` is
its Galois group over the quadratic base `ℚ(√d)`, a relative group of exactly this shape.

## Main results

* `TauCeti.Multiquadratic.aut_top_over_intermediateField_mul_self_eq_one`: every relative
  automorphism is an involution.
* `TauCeti.Multiquadratic.aut_top_over_intermediateField_exponent_dvd_two`: `Gal(M/F)` has exponent
  dividing two.
* `TauCeti.Multiquadratic.galoisGroupEquivIntermediateFieldSubmodule`: the isomorphism
  `Gal(M/F) ≃* Multiplicative U` given by the sign pattern of the restricted automorphism.
* `TauCeti.Multiquadratic.card_aut_top_over_intermediateField`: `|Gal(M/F)| = 2 ^ dim U`.
* `TauCeti.Multiquadratic.card_aut_top_over_intermediateField_of_finrank_eq_two`: over a quadratic
  subfield, `|Gal(M/F)| = 2 ^ (n - 1)`.

## Provenance

The multiquadratic Galois group and the subfield/subspace dictionary refined here are migrated,
with the rest of Layer 0, from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization of
L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture. The relative reading
assembles that dictionary with Mathlib's Galois correspondence
(`IntermediateField.fixingSubgroupEquiv`) and its abelian-extension tower instances
(`IsAbelianGalois.tower_top`).
-/

public section

open IntermediateField Module

namespace TauCeti.Multiquadratic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}
  {d : ι → K} {root : ι → L}

/-- Restricting an `F`-automorphism of `M` to `K` lands in the subgroup fixing `F`. -/
private theorem restrictScalars_mem_fixingSubgroup
    (F : IntermediateField K (adjoin K (Set.range root)))
    (σ : adjoin K (Set.range root) ≃ₐ[F] adjoin K (Set.range root)) :
    σ.restrictScalars K ∈ F.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact σ.commutes ⟨x, hx⟩

/-- **Relative automorphisms of a multiquadratic field are involutions.** An `F`-automorphism of
`M = K(rootᵢ : i)` restricts to a `K`-automorphism, and those square to the identity
(`TauCeti.Multiquadratic.aut_mul_self_eq_one`). -/
theorem aut_top_over_intermediateField_mul_self_eq_one
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (F : IntermediateField K (adjoin K (Set.range root)))
    (σ : adjoin K (Set.range root) ≃ₐ[F] adjoin K (Set.range root)) :
    σ * σ = 1 :=
  AlgEquiv.restrictScalars_injective K (aut_mul_self_eq_one hroot (σ.restrictScalars K))

/-- **The relative Galois group has exponent dividing two.** As stated this needs no finiteness or
characteristic hypothesis, just as `TauCeti.Multiquadratic.aut_exponent_dvd_two` does not for
`Gal(M/K)`. Under the extra hypotheses `[Finite ι]` and `[NeZero (2 : K)]` of
`TauCeti.Multiquadratic.isAbelianGalois`, Mathlib's `IsAbelianGalois.tower_top` supplies
commutativity as well, and then this says `Gal(M/F)` is elementary abelian, exactly as `Gal(M/K)`
is. -/
theorem aut_top_over_intermediateField_exponent_dvd_two
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    Monoid.exponent (adjoin K (Set.range root) ≃ₐ[F] adjoin K (Set.range root)) ∣ 2 := by
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro σ
  rw [pow_two]
  exact aut_top_over_intermediateField_mul_self_eq_one hroot F σ

/-- The sign pattern of a relative automorphism lies in the `𝔽₂`-subspace attached to the base
field: by definition that subspace collects the sign patterns of the automorphisms fixing `F`. -/
theorem signPattern_restrictScalars_mem [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root)))
    (σ : adjoin K (Set.range root) ≃ₐ[F] adjoin K (Set.range root)) :
    signPattern root (σ.restrictScalars K) ∈
      (intermediateFieldEquivSubmodule hroot hindep F).ofDual :=
  (mem_intermediateFieldEquivSubmodule_apply_ofDual_iff hroot hindep F _).mpr
    ⟨σ.restrictScalars K, restrictScalars_mem_fixingSubgroup F σ, rfl⟩

/-- The image of the fixing subgroup of `F` under the sign-pattern Galois-group equivalence is the
subgroup underlying the `𝔽₂`-subspace attached to `F`. This is
`TauCeti.Multiquadratic.intermediateFieldEquivSubmodule_apply_ofDual`, read as an equality of
subgroups of `Multiplicative (ι → ℤ/2)`. -/
private theorem fixingSubgroup_map_galoisGroupEquiv [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    F.fixingSubgroup.map (galoisGroupEquiv hroot hindep : _ →* _)
      = Subgroup.toAddSubgroup'.symm
          ((intermediateFieldEquivSubmodule hroot hindep F).ofDual.toAddSubgroup) := by
  ext σ
  simp [intermediateFieldEquivSubmodule_apply_ofDual hroot hindep F]

/-- **The relative Galois group of a multiquadratic field is the subspace attached to its base.**
Under square-class independence, restricting an `F`-automorphism of `M = K(rootᵢ : i)` to `K` and
reading its sign pattern is an isomorphism of `Gal(M/F)` onto the `𝔽₂`-subspace `U` of `ι → ℤ/2`
that the subfield dictionary attaches to `F`. For `F = ⊥` the subspace is everything and this is
`TauCeti.Multiquadratic.galoisGroupEquiv`.

No bijection is proved here: this is the composite of Mathlib's
`IntermediateField.fixingSubgroupEquiv`, which inverts restriction of scalars, with the restriction
of `TauCeti.Multiquadratic.galoisGroupEquiv` to the fixing subgroup of `F`, whose image is `U` by
`TauCeti.Multiquadratic.intermediateFieldEquivSubmodule_apply_ofDual`. -/
noncomputable def galoisGroupEquivIntermediateFieldSubmodule [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    (adjoin K (Set.range root) ≃ₐ[F] adjoin K (Set.range root)) ≃*
      Multiplicative ↥(intermediateFieldEquivSubmodule hroot hindep F).ofDual :=
  (IntermediateField.fixingSubgroupEquiv F).symm.trans
    (((galoisGroupEquiv hroot hindep).subgroupMap F.fixingSubgroup).trans
      (MulEquiv.subgroupCongr (fixingSubgroup_map_galoisGroupEquiv hroot hindep F)))

/-- The relative Galois equivalence sends an automorphism to the sign pattern of its restriction. -/
@[simp] theorem galoisGroupEquivIntermediateFieldSubmodule_apply [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root)))
    (σ : adjoin K (Set.range root) ≃ₐ[F] adjoin K (Set.range root)) :
    galoisGroupEquivIntermediateFieldSubmodule hroot hindep F σ =
      Multiplicative.ofAdd
        ⟨signPattern root (σ.restrictScalars K),
          signPattern_restrictScalars_mem hroot hindep F σ⟩ :=
  -- Both transports act as the identity on underlying sign vectors, so the value is the one
  -- `galoisGroupEquiv` reads off the restricted automorphism.
  Subtype.ext ((MulEquiv.coe_subgroupMap_apply (galoisGroupEquiv hroot hindep)
    F.fixingSubgroup ((IntermediateField.fixingSubgroupEquiv F).symm σ)).trans
      (galoisGroupEquiv_apply hroot hindep (σ.restrictScalars K)))

/-- The inverse of the relative Galois equivalence realizes a sign pattern `v` in the subspace
attached to `F` as the `F`-automorphism sending each generator `rootᵢ` to `(-1)^(vᵢ) · rootᵢ`. This
is the relative reading of `TauCeti.Multiquadratic.galoisGroupEquiv_symm_apply_gen`. -/
@[simp] theorem galoisGroupEquivIntermediateFieldSubmodule_symm_apply_gen [Finite ι]
    [NeZero (2 : K)] (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root)))
    (v : (intermediateFieldEquivSubmodule hroot hindep F).ofDual) (i : ι) :
    ((galoisGroupEquivIntermediateFieldSubmodule hroot hindep F).symm (Multiplicative.ofAdd v))
        (gen root i) = (-1) ^ ((v : ι → ZMod 2) i).val * gen root i := by
  set σ := (galoisGroupEquivIntermediateFieldSubmodule hroot hindep F).symm
    (Multiplicative.ofAdd v)
  have hsign : signPattern root (σ.restrictScalars K) = (v : ι → ZMod 2) := by
    have happ := (galoisGroupEquivIntermediateFieldSubmodule hroot hindep F).apply_symm_apply
      (Multiplicative.ofAdd v)
    rw [galoisGroupEquivIntermediateFieldSubmodule_apply] at happ
    exact congrArg Subtype.val (Multiplicative.ofAdd.injective happ)
  -- `σ` and its restriction of scalars have the same underlying function.
  exact (aut_gen_eq_signPattern hroot (σ.restrictScalars K) i).trans (by rw [hsign])

/-- **The order of the relative Galois group of a multiquadratic field.** Under square-class
independence, the relative Galois group `Gal(M/F)` of `M = K(rootᵢ : i)` over an intermediate field
`F` has order `2 ^ dim U`, where `U` is the `𝔽₂`-subspace of `ι → ℤ/2` attached to `F`. This is the
cardinality reading of `TauCeti.Multiquadratic.galoisGroupEquivIntermediateFieldSubmodule`, taken
here from the relative degree `TauCeti.Multiquadratic.finrank_top_over_intermediateField`, and it
is to the relative group what `TauCeti.Multiquadratic.card_aut_adjoin_range` is to the absolute
one. -/
theorem card_aut_top_over_intermediateField [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    Nat.card (adjoin K (Set.range root) ≃ₐ[F] adjoin K (Set.range root)) =
      2 ^ finrank (ZMod 2) (intermediateFieldEquivSubmodule hroot hindep F).ofDual := by
  haveI := isAbelianGalois hroot
  haveI := finiteDimensional_top_over_intermediateField hroot F
  rw [IsGalois.card_aut_eq_finrank F (adjoin K (Set.range root)),
    finrank_top_over_intermediateField hroot hindep F]

/-- **The relative Galois group over a quadratic subfield has order `2 ^ (n - 1)`.** Under
square-class independence, over any quadratic subfield `F` of the degree-`2ⁿ` multiquadratic field
`M = K(rootᵢ : i)`, the relative Galois group `Gal(M/F)` is elementary abelian of order
`2 ^ (|ι| - 1)`: a quadratic subfield is a hyperplane, so its subspace is a line's worth short of
everything. This is the group the genus-field constructions read off over the quadratic base. -/
theorem card_aut_top_over_intermediateField_of_finrank_eq_two [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) (hF : Module.finrank K F = 2) :
    Nat.card (adjoin K (Set.range root) ≃ₐ[F] adjoin K (Set.range root)) =
      2 ^ (Nat.card ι - 1) := by
  rw [card_aut_top_over_intermediateField hroot hindep F]
  congr 1
  have := (finrank_intermediateField_eq_two_iff hroot hindep F).mp hF
  omega

end TauCeti.Multiquadratic
