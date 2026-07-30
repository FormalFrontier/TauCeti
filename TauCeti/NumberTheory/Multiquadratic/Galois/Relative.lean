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

Two things happen. First, both halves of the tower inherit the structure of `M / K`: because that
group is abelian, every intermediate field is abelian Galois over `K`, and `M` is abelian Galois
over every intermediate field. Moreover a relative automorphism restricts to a `K`-automorphism,
and those are involutions, so `Gal(M/F)` is again elementary abelian of exponent dividing two.
Second, the sign pattern identifies `Gal(M/F)` precisely: restriction of scalars embeds it into
`Gal(M/K) ≃ (ℤ/2)ⁿ`, its image is exactly the subspace `U` attached to `F`, and the resulting map

`Gal(M/F) ≃* Multiplicative U`

is an isomorphism. The cardinality reading `|Gal(M/F)| = 2 ^ dim U` matches the relative degree, its
complement reads `|Gal(F/K)| = 2 ^ (n - dim U)`, the two multiply to `2ⁿ`, and over a quadratic
subfield the relative group has order `2 ^ (n - 1)`.

This is the group-theoretic half of the relative picture the genus-field constructions consume: the
genus field is multiquadratic over `ℚ`, and the group the genus theory identifies with `Cl/Cl²` is
its Galois group over the quadratic base `ℚ(√d)`, a relative group of exactly this shape.

## Main results

* `TauCeti.Multiquadratic.isAbelianGalois_top_over_intermediateField`: `M / F` is abelian Galois.
* `TauCeti.Multiquadratic.isAbelianGalois_intermediateField`: so is `F / K`.
* `TauCeti.Multiquadratic.aut_top_over_intermediateField_mul_self_eq_one`: every relative
  automorphism is an involution.
* `TauCeti.Multiquadratic.aut_top_over_intermediateField_exponent_dvd_two`: `Gal(M/F)` has exponent
  dividing two.
* `TauCeti.Multiquadratic.galoisGroupEquivIntermediateFieldSubmodule`: the isomorphism
  `Gal(M/F) ≃* Multiplicative U` given by the sign pattern of the restricted automorphism.
* `TauCeti.Multiquadratic.card_aut_top_over_intermediateField`: `|Gal(M/F)| = 2 ^ dim U`.
* `TauCeti.Multiquadratic.card_aut_intermediateField`: `|Gal(F/K)| = 2 ^ (n - dim U)`, the
  complementary codimension reading.
* `TauCeti.Multiquadratic.card_aut_intermediateField_mul_card_aut_top_over_intermediateField`: the
  group-order tower identity `|Gal(F/K)| · |Gal(M/F)| = 2ⁿ`.
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

/-- **A multiquadratic field is abelian Galois over any intermediate field.** Since
`M = K(rootᵢ : i)` is abelian Galois over `K`, it is abelian Galois over every intermediate field
`F` of `M / K`. No square-class independence is needed. -/
theorem isAbelianGalois_top_over_intermediateField [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    IsAbelianGalois F (adjoin K (Set.range root)) :=
  haveI := isAbelianGalois hroot
  inferInstance

/-- **A multiquadratic field is Galois over any intermediate field.** -/
theorem isGalois_top_over_intermediateField [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    IsGalois F (adjoin K (Set.range root)) :=
  (isAbelianGalois_top_over_intermediateField hroot F).toIsGalois

/-- A multiquadratic field is finite-dimensional over any intermediate field. -/
theorem finiteDimensional_top_over_intermediateField [Finite ι]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    FiniteDimensional F (adjoin K (Set.range root)) :=
  haveI := isSplittingField hroot
  haveI : FiniteDimensional K (adjoin K (Set.range root)) :=
    Polynomial.IsSplittingField.finiteDimensional _ (definingPolynomial d)
  Module.Finite.of_restrictScalars_finite K F (adjoin K (Set.range root))

/-- **Every intermediate field of a multiquadratic field is abelian Galois over the base.** The
Galois group of `M / K` is abelian, so every subgroup is normal and every intermediate field `F` is
itself an abelian Galois extension of `K`. No square-class independence is needed. -/
theorem isAbelianGalois_intermediateField [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    IsAbelianGalois K F :=
  haveI := isAbelianGalois hroot
  inferInstance

/-- Restricting an `F`-automorphism of `M` to `K` lands in the subgroup fixing `F`. -/
theorem restrictScalars_mem_fixingSubgroup
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

/-- **The relative Galois group has exponent dividing two.** Together with commutativity
(`TauCeti.Multiquadratic.isAbelianGalois_top_over_intermediateField`) this says `Gal(M/F)` is
elementary abelian, exactly as `Gal(M/K)` is (`TauCeti.Multiquadratic.aut_exponent_dvd_two`). -/
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

/-- The relative sign-pattern homomorphism: an `F`-automorphism of `M = K(rootᵢ : i)` is sent to
the sign pattern of the `K`-automorphism underlying it, which lands in the `𝔽₂`-subspace attached
to `F`. -/
@[expose] noncomputable def relativeSignHom [Finite ι] [NeZero (2 : K)]
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
@[simp] theorem relativeSignHom_apply [Finite ι] [NeZero (2 : K)]
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
    refine ⟨IntermediateField.fixingSubgroupEquiv F ⟨τ, hτ⟩, ?_⟩
    rw [relativeSignHom_apply]
    refine congrArg Multiplicative.ofAdd (Subtype.ext ?_)
    change signPattern root
      ((IntermediateField.fixingSubgroupEquiv F ⟨τ, hτ⟩).restrictScalars K) = w
    rw [hres]
    exact hv

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

/-- **Cardinality of the relative Galois group.** Under square-class independence, `Gal(M/F)` has
order `2 ^ dim U`, where `U` is the `𝔽₂`-subspace of `ι → ℤ/2` attached to `F`. This is the group
reading of the relative degree `TauCeti.Multiquadratic.finrank_top_over_intermediateField`. -/
theorem card_aut_top_over_intermediateField [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    Nat.card (adjoin K (Set.range root) ≃ₐ[F] adjoin K (Set.range root)) =
      2 ^ Module.finrank (ZMod 2) (intermediateFieldEquivSubmodule hroot hindep F).ofDual := by
  haveI := isGalois_top_over_intermediateField hroot F
  haveI := finiteDimensional_top_over_intermediateField hroot F
  rw [IsGalois.card_aut_eq_finrank F (adjoin K (Set.range root)),
    finrank_top_over_intermediateField hroot hindep F]

/-- **Cardinality of the Galois group of an intermediate field over the base.** Under square-class
independence, `Gal(F/K)` has order `2 ^ (n - dim U)`, the codimension reading complementary to
`TauCeti.Multiquadratic.card_aut_top_over_intermediateField`. -/
theorem card_aut_intermediateField [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    Nat.card (F ≃ₐ[K] F) =
      2 ^ (Nat.card ι
        - Module.finrank (ZMod 2) (intermediateFieldEquivSubmodule hroot hindep F).ofDual) := by
  haveI := (isAbelianGalois_intermediateField hroot F).toIsGalois
  haveI := isSplittingField hroot
  haveI : FiniteDimensional K (adjoin K (Set.range root)) :=
    Polynomial.IsSplittingField.finiteDimensional _ (definingPolynomial d)
  rw [IsGalois.card_aut_eq_finrank K F, finrank_intermediateField_eq_two_pow hroot hindep F]

/-- **The group-order tower identity `|Gal(F/K)| · |Gal(M/F)| = 2ⁿ`.** Under square-class
independence, the two Galois groups attached to an intermediate field `F` of a multiquadratic
field — the quotient `Gal(F/K)` and the relative group `Gal(M/F)` — have orders multiplying to
the full degree. This is the group reading of
`TauCeti.Multiquadratic.finrank_intermediateField_mul_finrank_top`. -/
theorem card_aut_intermediateField_mul_card_aut_top_over_intermediateField [Finite ι]
    [NeZero (2 : K)] (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (F : IntermediateField K (adjoin K (Set.range root))) :
    Nat.card (F ≃ₐ[K] F) *
        Nat.card (adjoin K (Set.range root) ≃ₐ[F] adjoin K (Set.range root)) =
      2 ^ Nat.card ι := by
  haveI := (isAbelianGalois_intermediateField hroot F).toIsGalois
  haveI := isGalois_top_over_intermediateField hroot F
  haveI := finiteDimensional_top_over_intermediateField hroot F
  haveI := isSplittingField hroot
  haveI : FiniteDimensional K (adjoin K (Set.range root)) :=
    Polynomial.IsSplittingField.finiteDimensional _ (definingPolynomial d)
  rw [IsGalois.card_aut_eq_finrank K F,
    IsGalois.card_aut_eq_finrank F (adjoin K (Set.range root))]
  exact finrank_intermediateField_mul_finrank_top hroot hindep F

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
  haveI := isGalois_top_over_intermediateField hroot F
  haveI := finiteDimensional_top_over_intermediateField hroot F
  rw [IsGalois.card_aut_eq_finrank F (adjoin K (Set.range root)),
    finrank_top_over_intermediateField_of_finrank_eq_two hroot hindep F hF]

end TauCeti.Multiquadratic
