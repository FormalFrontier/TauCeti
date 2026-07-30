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

is an isomorphism. Cardinalities then come from `IsGalois.card_aut_eq_finrank` together with the
relative degrees of `TauCeti.NumberTheory.Multiquadratic.RelativeDegree`; the one reading recorded
here is the one the genus-field constructions consume, `|Gal(M/F)| = 2 ^ (n - 1)` over a quadratic
subfield.

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

/-- **The relative Galois group has exponent dividing two.** Together with commutativity — which
Mathlib's `IsAbelianGalois` tower instance supplies from
`TauCeti.Multiquadratic.isAbelianGalois` — this says `Gal(M/F)` is elementary abelian, exactly as
`Gal(M/K)` is (`TauCeti.Multiquadratic.aut_exponent_dvd_two`). -/
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

/-- The relative sign-pattern homomorphism underlying
`TauCeti.Multiquadratic.galoisGroupEquivIntermediateFieldSubmodule`: an `F`-automorphism of
`M = K(rootᵢ : i)` is sent to the sign pattern of the `K`-automorphism underlying it, which lands
in the `𝔽₂`-subspace attached to `F`. -/
private noncomputable def relativeSignHom [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    (adjoin K (Set.range root) ≃ₐ[F] adjoin K (Set.range root)) →*
      Multiplicative ↥(intermediateFieldEquivSubmodule hroot hindep F).ofDual :=
  MonoidHom.mk'
    (fun σ => Multiplicative.ofAdd
      ⟨signPattern root (σ.restrictScalars K), signPattern_restrictScalars_mem hroot hindep F σ⟩)
    fun σ τ => congrArg Multiplicative.ofAdd (Subtype.ext
      (signPattern_mul hroot (σ.restrictScalars K) (τ.restrictScalars K)))

/-- Evaluation rule for `relativeSignHom`: it records the sign pattern of the restricted
automorphism. -/
private theorem relativeSignHom_apply [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root)))
    (σ : adjoin K (Set.range root) ≃ₐ[F] adjoin K (Set.range root)) :
    relativeSignHom hroot hindep F σ =
      Multiplicative.ofAdd
        ⟨signPattern root (σ.restrictScalars K),
          signPattern_restrictScalars_mem hroot hindep F σ⟩ :=
  rfl

private theorem relativeSignHom_bijective [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    Function.Bijective (relativeSignHom hroot hindep F) := by
  constructor
  · intro σ τ h
    rw [relativeSignHom_apply, relativeSignHom_apply] at h
    exact AlgEquiv.restrictScalars_injective K (signPattern_injective hroot
      (congrArg Subtype.val (Multiplicative.ofAdd.injective h)))
  · intro v
    obtain ⟨⟨w, hw⟩, rfl⟩ : ∃ u, Multiplicative.ofAdd u = v := ⟨Multiplicative.toAdd v, rfl⟩
    obtain ⟨τ, hτ, hv⟩ :=
      (mem_intermediateFieldEquivSubmodule_apply_ofDual_iff hroot hindep F w).mp hw
    -- `fixingSubgroupEquiv` inverts restriction of scalars, so the `K`-automorphism underlying the
    -- relative automorphism it produces from `τ` is `τ` itself.
    have hres : (IntermediateField.fixingSubgroupEquiv F ⟨τ, hτ⟩).restrictScalars K = τ :=
      congrArg Subtype.val ((IntermediateField.fixingSubgroupEquiv F).symm_apply_apply ⟨τ, hτ⟩)
    -- The membership proof inside the subtype depends on the automorphism, so `hres` cannot be
    -- rewritten into the goal; transport it through `signPattern root` on the values instead.
    refine ⟨IntermediateField.fixingSubgroupEquiv F ⟨τ, hτ⟩, ?_⟩
    rw [relativeSignHom_apply]
    exact congrArg Multiplicative.ofAdd
      (Subtype.ext ((congrArg (signPattern root) hres).trans hv))

/-- **The relative Galois group of a multiquadratic field is the subspace attached to its base.**
Under square-class independence, restricting an `F`-automorphism of `M = K(rootᵢ : i)` to `K` and
reading its sign pattern is an isomorphism of `Gal(M/F)` onto the `𝔽₂`-subspace `U` of `ι → ℤ/2`
that the subfield dictionary attaches to `F`. For `F = ⊥` the subspace is everything and this is
`TauCeti.Multiquadratic.galoisGroupEquiv`. -/
noncomputable def galoisGroupEquivIntermediateFieldSubmodule [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    (adjoin K (Set.range root) ≃ₐ[F] adjoin K (Set.range root)) ≃*
      Multiplicative ↥(intermediateFieldEquivSubmodule hroot hindep F).ofDual :=
  MulEquiv.ofBijective (relativeSignHom hroot hindep F) (relativeSignHom_bijective hroot hindep F)

/-- The relative Galois equivalence sends an automorphism to the sign pattern of its restriction. -/
@[simp] theorem galoisGroupEquivIntermediateFieldSubmodule_apply [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root)))
    (σ : adjoin K (Set.range root) ≃ₐ[F] adjoin K (Set.range root)) :
    galoisGroupEquivIntermediateFieldSubmodule hroot hindep F σ =
      Multiplicative.ofAdd
        ⟨signPattern root (σ.restrictScalars K),
          signPattern_restrictScalars_mem hroot hindep F σ⟩ := by
  rw [galoisGroupEquivIntermediateFieldSubmodule, MulEquiv.ofBijective_apply,
    relativeSignHom_apply]

/-- **The relative Galois group over a quadratic subfield has order `2 ^ (n - 1)`.** Under
square-class independence, over any quadratic subfield `F` of the degree-`2ⁿ` multiquadratic field
`M = K(rootᵢ : i)`, the relative Galois group `Gal(M/F)` is elementary abelian of order
`2 ^ (|ι| - 1)`. This is the group the genus-field constructions read off over the quadratic
base. -/
theorem card_aut_top_over_intermediateField_of_finrank_eq_two [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root)))
    (hF : Module.finrank K F = 2) :
    Nat.card (adjoin K (Set.range root) ≃ₐ[F] adjoin K (Set.range root)) =
      2 ^ (Nat.card ι - 1) := by
  haveI := isAbelianGalois hroot
  haveI := finiteDimensional_top_over_intermediateField hroot F
  rw [IsGalois.card_aut_eq_finrank F (adjoin K (Set.range root)),
    finrank_top_over_intermediateField_of_finrank_eq_two hroot hindep F hF]

end TauCeti.Multiquadratic
