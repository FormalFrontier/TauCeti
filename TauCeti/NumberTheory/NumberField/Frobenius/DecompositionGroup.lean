/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.NumberTheory.NumberField.Frobenius
public import TauCeti.NumberTheory.RamificationInertia.Galois

/-!
# The Frobenius and the decomposition group at an unramified prime

Let `L / K` be a finite Galois extension of number fields with Galois group `G = Gal(L/K)`, and
let `Q` be a nonzero prime of `𝓞 L` lying over `𝔭 = Q ∩ 𝓞 K`. Mathlib's `IsArithFrobAt`
expresses that an element `σ ∈ G` satisfies `σ x ≡ x ^ #(𝓞 K ⧸ 𝔭) (mod Q)`. Tau Ceti's
`NumberField.exists_isArithFrobAt` supplies such an element, and
`NumberField.isArithFrobAt_eq_of_isUnramifiedAt` proves it unique when `L / K` is unramified at
`Q`. This file identifies what that element is: a generator of the decomposition group of `Q`,
mapping to the Frobenius automorphism of the residue extension.

The link is Mathlib's `Ideal.Quotient.stabilizerHom`, the action of the decomposition group
`MulAction.stabilizer G Q` on the residue extension `(𝓞 L ⧸ Q) / (𝓞 K ⧸ 𝔭)`. Its kernel is the
inertia subgroup, which is trivial exactly when `Q` is unramified, because the cardinality of the
inertia subgroup is the ramification index (`Ideal.card_inertia_eq_ramificationIdx`). So at an
unramified prime the decomposition group embeds in the residue Galois group, and a Frobenius
element is precisely a preimage of the residue Frobenius `x ↦ x ^ #(𝓞 K ⧸ 𝔭)`. Counting through
that embedding turns the classical facts about finite fields into facts about `G`:

* the order of a Frobenius element is the inertia degree `f(Q/𝔭)`;
* the decomposition group has cardinality `f(Q/𝔭)` as well, so the embedding is an isomorphism;
* consequently the decomposition group is `⟨σ⟩`, and it is cyclic.

The last section transports these statements along the action of `G` on the primes above `𝔭`.
Unramifiedness is invariant under that action, and the Frobenius at `τ • Q` is the conjugate
`τ σ τ⁻¹`: Mathlib's `IsArithFrobAt.conj` gives one inclusion and uniqueness at the unramified
prime `τ • Q` gives the other.

## Main results

* `Ideal.isUnramifiedAt_iff_inertia_eq_bot`: unramifiedness at `Q` is triviality of the
  inertia subgroup of `Q` in `Gal(L/K)`.
* `Ideal.stabilizerHom_eq_frobeniusAlgEquivOfAlgebraic`: a Frobenius element at `Q` acts on
  the residue field `𝓞 L ⧸ Q` as the residue Frobenius.
* `Ideal.orderOf_eq_inertiaDeg_of_isArithFrobAt`: a Frobenius element at an unramified `Q`
  has order the inertia degree of `Q` over `𝓞 K`.
* `Ideal.zpowers_eq_stabilizer_of_isArithFrobAt`: a Frobenius element at an unramified `Q`
  generates the decomposition group of `Q`.
* `Ideal.stabilizerEquivResidueAut`: the decomposition group of an unramified prime is
  isomorphic to the automorphism group of the residue extension.
* `Ideal.isCyclic_stabilizer_of_isUnramifiedAt`: the decomposition group of an unramified
  prime is cyclic.
* `Ideal.isArithFrobAt_pointwise_smul_iff_eq_conj`: the Frobenius elements at `τ • Q` are
  exactly the conjugates `τ σ τ⁻¹` of the Frobenius elements `σ` at an unramified `Q`.

## Implementation notes

`FiniteField.frobeniusAlgEquivOfAlgebraic` is stated for a `Fintype` base field, so the residue
identification supplies that instance internally through `Fintype.ofFinite`. Residue rings are
made into fields by the local instance `Ideal.Quotient.field`, following Mathlib's own
ramification files.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
-/

public section

open Ideal Module

open scoped NumberField Pointwise

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-! ### Unramifiedness and the inertia subgroup -/

/-- **Unramified means trivial inertia.** For a finite Galois extension `L / K` of number fields,
`L / K` is unramified at a prime `Q` of `𝓞 L` exactly when the inertia subgroup of `Q` in
`Gal(L/K)` is trivial.

This is the group-theoretic reading of `Ideal.card_inertia_eq_ramificationIdx`: the inertia
subgroup has as many elements as the ramification index of `Q` over `𝓞 K`. -/
theorem isUnramifiedAt_iff_inertia_eq_bot (Q : Ideal (𝓞 L)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 K) Q ↔ Q.inertia (L ≃ₐ[K] L) = ⊥ := by
  rw [← Ideal.ramificationIdx_eq_one_iff (R := 𝓞 K) (q := Q),
    ← Ideal.card_inertia_eq_ramificationIdx (𝓞 K) (L ≃ₐ[K] L) Q]
  exact ⟨Subgroup.eq_bot_of_card_eq _, fun h ↦ by rw [h]; simp⟩

/-! ### The decomposition group at an unramified prime -/

/-- **The decomposition group of an unramified prime embeds in the residue Galois group.**
Mathlib's `Ideal.Quotient.stabilizerHom` has the inertia subgroup as its kernel, and that
subgroup is trivial at an unramified prime. -/
theorem stabilizerHom_injective_of_isUnramifiedAt (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] :
    Function.Injective (Ideal.Quotient.stabilizerHom Q (Q.under (𝓞 K)) (L ≃ₐ[K] L)) := by
  rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom, eq_bot_iff]
  intro σ hσ
  have hσ' : (σ : L ≃ₐ[K] L) ∈ Q.inertia (L ≃ₐ[K] L) := Ideal.coe_mem_inertia.mpr hσ
  rw [(isUnramifiedAt_iff_inertia_eq_bot Q).mp ‹_›, Subgroup.mem_bot] at hσ'
  exact Subgroup.mem_bot.mpr (Subtype.ext hσ')

/-- **The decomposition group of an unramified prime is the residue Galois group.** Mathlib's
`Ideal.Quotient.stabilizerHom` is always surjective for an invariant extension, and at an
unramified prime it is also injective, so it is an isomorphism from the decomposition group of
`Q` onto the automorphism group of the residue extension `(𝓞 L ⧸ Q) / (𝓞 K ⧸ 𝔭)`.

This is the unramified case of Mathlib's `Ideal.Quotient.stabilizerQuotientInertiaEquiv`, where
the inertia subgroup one quotients by is trivial; the point of stating it separately is that the
source is the decomposition group itself, so an element of `Gal(L/K)` can be compared with a
residue automorphism without passing through a quotient. Under it, an arithmetic Frobenius at `Q`
corresponds to the residue Frobenius, by
`Ideal.stabilizerHom_eq_frobeniusAlgEquivOfAlgebraic`. -/
noncomputable def stabilizerEquivResidueAut (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] :
    MulAction.stabilizer (L ≃ₐ[K] L) Q ≃*
      ((𝓞 L ⧸ Q) ≃ₐ[𝓞 K ⧸ Q.under (𝓞 K)] (𝓞 L ⧸ Q)) :=
  MulEquiv.ofBijective (Ideal.Quotient.stabilizerHom Q (Q.under (𝓞 K)) (L ≃ₐ[K] L))
    ⟨stabilizerHom_injective_of_isUnramifiedAt Q,
      Ideal.Quotient.stabilizerHom_surjective (L ≃ₐ[K] L) (Q.under (𝓞 K)) Q⟩

@[simp]
theorem stabilizerEquivResidueAut_apply (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (σ : MulAction.stabilizer (L ≃ₐ[K] L) Q) :
    stabilizerEquivResidueAut Q σ =
      Ideal.Quotient.stabilizerHom Q (Q.under (𝓞 K)) (L ≃ₐ[K] L) σ := by
  unfold stabilizerEquivResidueAut
  exact MulEquiv.ofBijective_apply _ _ _

/-- Applying the residue action to the inverse image of a residue automorphism recovers that
automorphism. -/
@[simp]
theorem stabilizerHom_stabilizerEquivResidueAut_symm_apply (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Algebra.IsUnramifiedAt (𝓞 K) Q]
    (φ : (𝓞 L ⧸ Q) ≃ₐ[𝓞 K ⧸ Q.under (𝓞 K)] (𝓞 L ⧸ Q)) :
    Ideal.Quotient.stabilizerHom Q (Q.under (𝓞 K)) (L ≃ₐ[K] L)
        ((stabilizerEquivResidueAut Q).symm φ) = φ := by
  rw [← stabilizerEquivResidueAut_apply]
  exact (stabilizerEquivResidueAut Q).apply_symm_apply φ

attribute [local instance] Ideal.Quotient.field

omit [IsGalois K L] in
/-- **A Frobenius element induces the residue Frobenius.** The action of an arithmetic Frobenius
`σ` at `Q` on the residue field `𝓞 L ⧸ Q` is the `#(𝓞 K ⧸ 𝔭)`-power map, that is
`FiniteField.frobeniusAlgEquivOfAlgebraic` of the residue extension.

This is the defining congruence `σ x ≡ x ^ #(𝓞 K ⧸ 𝔭) (mod Q)` read as an equality of
automorphisms of `𝓞 L ⧸ Q`; no unramifiedness is needed. -/
theorem stabilizerHom_eq_frobeniusAlgEquivOfAlgebraic (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    let _ : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ
    letI := Fintype.ofFinite (𝓞 K ⧸ Q.under (𝓞 K))
    Ideal.Quotient.stabilizerHom Q (Q.under (𝓞 K)) (L ≃ₐ[K] L) ⟨σ, hσ.mem_stabilizer⟩ =
      FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 K ⧸ Q.under (𝓞 K)) (𝓞 L ⧸ Q) := by
  let _ : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.stabilizerHom_apply, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    ← @Nat.card_eq_fintype_card _ (Fintype.ofFinite _)]
  simpa [MulAction.subgroup_smul_def, MulSemiringAction.toAlgHom_apply] using hσ.mk_apply x

/-- **The order of a Frobenius element is the inertia degree.** For `Q` unramified over `𝓞 K`, an
arithmetic Frobenius `σ` at `Q` has `orderOf σ = f(Q / 𝔭)`.

The decomposition group injects into the residue Galois group, where the image of `σ` is the
residue Frobenius; that automorphism has order the degree of the residue extension, which is the
inertia degree. -/
theorem orderOf_eq_inertiaDeg_of_isArithFrobAt (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q] {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    orderOf σ = Q.inertiaDeg (𝓞 K) := by
  let _ : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ
  have : Fintype (𝓞 K ⧸ Q.under (𝓞 K)) := Fintype.ofFinite _
  have key : orderOf (⟨σ, hσ.mem_stabilizer⟩ : MulAction.stabilizer (L ≃ₐ[K] L) Q) =
      Q.inertiaDeg (𝓞 K) := by
    rw [← orderOf_injective _ (stabilizerHom_injective_of_isUnramifiedAt Q),
      stabilizerHom_eq_frobeniusAlgEquivOfAlgebraic Q hQ hσ,
      FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      Ideal.inertiaDeg_eq_of_isMaximal (Q.under (𝓞 K)) Q]
  exact (Subgroup.orderOf_coe (⟨σ, hσ.mem_stabilizer⟩ :
    MulAction.stabilizer (L ≃ₐ[K] L) Q)).trans key

/-- **The decomposition group of an unramified prime has order the inertia degree.** -/
private theorem card_stabilizer_eq_inertiaDeg_of_isUnramifiedAt (Q : Ideal (𝓞 L))
    [Q.IsPrime] (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q] :
    Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) Q) = Q.inertiaDeg (𝓞 K) := by
  let _ : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ
  rw [Ideal.card_stabilizer_eq_card_inertia_mul_finrank (Q.under (𝓞 K)) Q,
    (isUnramifiedAt_iff_inertia_eq_bot Q).mp ‹_›]
  simp

/-- **A Frobenius element generates the decomposition group.** At an unramified prime `Q` the
cyclic subgroup generated by an arithmetic Frobenius at `Q` is the whole decomposition group,
both having `f(Q / 𝔭)` elements. -/
theorem zpowers_eq_stabilizer_of_isArithFrobAt (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q] {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    Subgroup.zpowers σ = MulAction.stabilizer (L ≃ₐ[K] L) Q := by
  have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (L ≃ₐ[K] L) Q :=
    Subgroup.zpowers_le.mpr hσ.mem_stabilizer
  refine le_antisymm hle ?_
  rw [← Subgroup.subgroupOf_eq_top]
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers,
    orderOf_eq_inertiaDeg_of_isArithFrobAt Q hQ hσ,
    card_stabilizer_eq_inertiaDeg_of_isUnramifiedAt Q hQ]

/-- **The decomposition group of an unramified prime is cyclic.** A Frobenius element exists at
every nonzero prime of `𝓞 L`, and at an unramified prime it generates the decomposition group. -/
theorem isCyclic_stabilizer_of_isUnramifiedAt (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] : IsCyclic (MulAction.stabilizer (L ≃ₐ[K] L) Q) := by
  obtain ⟨σ, hσ⟩ := NumberField.exists_isArithFrobAt K Q hQ
  exact (Subgroup.isCyclic_iff_exists_zpowers_eq_top _).mpr
    ⟨σ, zpowers_eq_stabilizer_of_isArithFrobAt Q hQ hσ⟩

/-! ### Conjugation along the fibre -/

/-- **Frobenius elements are conjugated by the Galois action on primes.** At an unramified prime
`Q` with arithmetic Frobenius `σ`, an element of `Gal(L/K)` is an arithmetic Frobenius at the
translated prime `τ • Q` exactly when it is the conjugate `τ σ τ⁻¹`.

Mathlib's `IsArithFrobAt.conj` gives that `τ σ τ⁻¹` is one; uniqueness at `τ • Q`, which is
unramified by `Ideal.isUnramifiedAt_pointwise_smul_iff`, gives that it is the only one. -/
theorem isArithFrobAt_pointwise_smul_iff_eq_conj (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ Q)
    (τ ρ : L ≃ₐ[K] L) :
    IsArithFrobAt (𝓞 K) ρ (τ • Q) ↔ ρ = τ * σ * τ⁻¹ := by
  have : Algebra.IsUnramifiedAt (𝓞 K) (τ • Q) :=
    (Q.isUnramifiedAt_pointwise_smul_iff τ).mpr ‹_›
  exact ⟨fun hρ ↦ NumberField.isArithFrobAt_eq_of_isUnramifiedAt hρ (hσ.conj τ),
    fun h ↦ h ▸ hσ.conj τ⟩

end Ideal
