/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Basic
public import TauCeti.Algebra.Lie.Subalgebra.Automorphism
public import TauCeti.Algebra.Lie.Weights.Sl2System

/-!
# Automorphisms normalising a Cartan subalgebra

Let `σ` be an automorphism of a Lie algebra `L` which normalises a nilpotent subalgebra `H`, in
the sense that `H.map σ = H`. Then Mathlib's `LieEquiv.ofSubalgebras` restricts `σ` to an
automorphism `σ|H` of `H`, and it carries the root space of `χ : H → R` onto the root space of
`χ ∘ (σ|H)⁻¹`: root-space membership is the condition `∀ y, ∃ k, ((ad y - χ y) ^ k) z = 0`, and it
is transported by rewriting `y` as `σ (σ⁻¹ y)`. So `σ` permutes the weights, and in the Killing
setting it also transports the `sl₂` data attached to a root, sending the coroot of `α` to the
coroot of the permuted root and a normalised system of root vectors to a normalised system again.

This is the input the diagram automorphisms of a split semisimple Lie algebra need. A graph
symmetry of the Dynkin diagram is realised on the Serre presentation as an automorphism permuting
the Chevalley generators, hence normalising the Cartan subalgebra they span, and the
Chevalley--Demazure construction has to know what it does to the remaining root vectors.

The Weyl automorphism `TauCeti.weylAut` of an `sl₂` triple also permutes root spaces, by
`TauCeti.weylAut_map_rootSpace`, which is proved directly from the exponential formula. This
repository has no lemma `H.map weylAut = H`, so that statement is not currently derived from
`TauCeti.map_rootSpace_eq`.

## Main definitions

* `TauCeti.weightPerm`: the induced permutation of the weights of `H` acting on `L`.

## Main results

* `TauCeti.map_mem_rootSpace` and `TauCeti.map_rootSpace_eq`: a normalising automorphism carries
  the root space of `χ` onto the root space of `χ ∘ (σ|H)⁻¹`.
* `TauCeti.weightPerm_neg`: the induced permutation commutes with negation of weights.
* `TauCeti.weightPerm_eq_neg`: an automorphism acting by `-1` on `H` inverts every weight.
* `TauCeti.map_coroot_weightPerm`: a normalising automorphism sends the coroot of a root to the
  coroot of the permuted root.
* `TauCeti.IsSl2System.map`: the family obtained by transporting a normalised system of root
  vectors along a normalising automorphism is again a normalised system.
* `TauCeti.IsSl2System.exists_map_eq_smul`: a normalising automorphism scales each root vector,
  and `TauCeti.IsSl2System.mul_eq_one_of_map_eq_smul`: the scalars at `α` and `-α` are inverse.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §16.5.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.

This supplies part of the pinning data for the explicit Chevalley--Demazure construction in Layer
9 of `TauCetiRoadmap/ReductiveGroups/README.md`, which is consumed by milestones L0 and L1 of the
`CFSGStatement` roadmap.
-/

public section

namespace TauCeti

open LieAlgebra LieModule

universe u v

section RootSpace

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
  {H : LieSubalgebra R L} [LieRing.IsNilpotent H]

variable (σ : L ≃ₗ⁅R⁆ L) (hσ : H.map (σ : L →ₗ⁅R⁆ L) = H)

include hσ

omit [LieRing.IsNilpotent H] in
/-- A normalising automorphism intertwines the two `H`-endomorphisms cutting out the root spaces of
`χ` and of `χ ∘ (σ|H)⁻¹`. -/
private theorem comp_sub_smul_one (χ : H → R) (y : H) :
    (toEnd R H L y - (χ ∘ (σ.ofSubalgebras H H hσ).symm) y • (1 : Module.End R L)) ∘ₗ
        (σ.toLinearEquiv : L →ₗ[R] L) =
      (σ.toLinearEquiv : L →ₗ[R] L) ∘ₗ
        (toEnd R H L ((σ.ofSubalgebras H H hσ).symm y) -
          χ ((σ.ofSubalgebras H H hσ).symm y) • (1 : Module.End R L)) := by
  ext z
  have hy : ⁅y, σ z⁆ = σ ⁅(σ.ofSubalgebras H H hσ).symm y, z⁆ := by
    rw [LieSubalgebra.coe_bracket_of_module, LieSubalgebra.coe_bracket_of_module, σ.map_lie,
      LieEquiv.ofSubalgebras_symm_apply, LieEquiv.apply_symm_apply]
  simp [hy]

/-- A normalising automorphism carries the root space of `χ` into the root space of the weight
`χ ∘ (σ|H)⁻¹` obtained by precomposing with the inverse of its restriction. -/
theorem map_mem_rootSpace {χ : H → R} {z : L} (hz : z ∈ rootSpace H χ) :
    σ z ∈ rootSpace H (χ ∘ (σ.ofSubalgebras H H hσ).symm) := by
  rw [rootSpace, mem_genWeightSpace] at hz ⊢
  intro y
  obtain ⟨k, hk⟩ := hz ((σ.ofSubalgebras H H hσ).symm y)
  refine ⟨k, ?_⟩
  simpa [hk] using LinearMap.congr_fun
    (Module.End.commute_pow_left_of_commute (comp_sub_smul_one σ hσ χ y) k) z

/-- A normalising automorphism carries the root space of `χ` **onto** the root space of
`χ ∘ (σ|H)⁻¹`: the inverse automorphism normalises `H` too, and transports the second root space
back into the first. -/
theorem map_rootSpace_eq (χ : H → R) :
    (rootSpace H χ).toSubmodule.map (σ.toLinearEquiv : L →ₗ[R] L) =
      (rootSpace H (χ ∘ (σ.ofSubalgebras H H hσ).symm)).toSubmodule := by
  ext w
  simp only [Submodule.mem_map, LieSubmodule.mem_toSubmodule]
  refine ⟨?_, fun hw => ⟨σ.symm w, ?_, by simp⟩⟩
  · rintro ⟨z, hz, rfl⟩
    exact map_mem_rootSpace σ hσ hz
  · have hcomp : (χ ∘ (σ.ofSubalgebras H H hσ).symm) ∘
        (σ.symm.ofSubalgebras H H
          (LieSubalgebra.map_symm_eq_self_of_map_eq_self σ hσ)).symm = χ :=
      funext fun y => congrArg χ (Subtype.ext (by simp))
    have h := map_mem_rootSpace σ.symm
      (LieSubalgebra.map_symm_eq_self_of_map_eq_self σ hσ) hw
    rwa [hcomp] at h

/-- The root space of `χ ∘ (σ|H)⁻¹` is nonzero whenever the root space of `χ` is. -/
private theorem genWeightSpace_comp_ofSubalgebras_symm_ne_bot (χ : Weight R H L) :
    genWeightSpace L ((χ : H → R) ∘ (σ.ofSubalgebras H H hσ).symm) ≠ ⊥ := by
  obtain ⟨z, hz, hz₀⟩ := χ.exists_ne_zero
  intro hbot
  have hmem : σ z ∈ genWeightSpace L ((χ : H → R) ∘ (σ.ofSubalgebras H H hσ).symm) :=
    map_mem_rootSpace σ hσ hz
  rw [hbot, LieSubmodule.mem_bot] at hmem
  exact hz₀ (by simpa using congrArg σ.symm hmem)

/-- The weight of `H` acting on `L` obtained from `χ` by precomposing with the inverse of the
restriction of a normalising automorphism. -/
private def weightMap (χ : Weight R H L) : Weight R H L :=
  ⟨(χ : H → R) ∘ (σ.ofSubalgebras H H hσ).symm,
    genWeightSpace_comp_ofSubalgebras_symm_ne_bot σ hσ χ⟩

end RootSpace

section WeightPerm

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
  {H : LieSubalgebra R L} [LieRing.IsNilpotent H]

variable (σ : L ≃ₗ⁅R⁆ L) (hσ : H.map (σ : L →ₗ⁅R⁆ L) = H)

include hσ

/-- The permutation of the weights of `H` acting on `L` induced by an automorphism of `L`
normalising `H`. -/
def weightPerm : Equiv.Perm (Weight R H L) where
  toFun := weightMap σ hσ
  invFun := weightMap σ.symm (LieSubalgebra.map_symm_eq_self_of_map_eq_self σ hσ)
  left_inv χ := by
    ext y
    exact congrArg (χ : H → R) (Subtype.ext (by simp))
  right_inv χ := by
    ext y
    exact congrArg (χ : H → R) (Subtype.ext (by simp))

@[simp]
theorem coe_weightPerm (χ : Weight R H L) :
    (weightPerm σ hσ χ : H → R) =
      (χ : H → R) ∘ (σ.ofSubalgebras H H hσ).symm := (rfl)

@[simp]
theorem weightPerm_apply_apply (χ : Weight R H L) (y : H) :
    weightPerm σ hσ χ y = χ ((σ.ofSubalgebras H H hσ).symm y) := (rfl)

/-- The inverse of the induced permutation is the permutation induced by the inverse
automorphism. -/
theorem weightPerm_symm :
    (weightPerm σ hσ).symm =
      weightPerm σ.symm (LieSubalgebra.map_symm_eq_self_of_map_eq_self σ hσ) :=
  Equiv.ext fun _ => rfl

/-- The inverse of the induced permutation precomposes a weight with the restriction of `σ`
itself. -/
@[simp]
theorem coe_weightPerm_symm (χ : Weight R H L) :
    ((weightPerm σ hσ).symm χ : H → R) =
      (χ : H → R) ∘ σ.ofSubalgebras H H hσ :=
  funext fun y => congrArg (χ : H → R) (Subtype.ext (by simp))

@[simp]
theorem weightPerm_symm_apply_apply (χ : Weight R H L) (y : H) :
    (weightPerm σ hσ).symm χ y = χ (σ.ofSubalgebras H H hσ y) :=
  congrArg (χ : H → R) (Subtype.ext (by simp))

/-- A normalising automorphism carries the root space of a weight into the root space of its
image under the induced permutation. -/
theorem map_mem_rootSpace_weightPerm {χ : Weight R H L} {z : L} (hz : z ∈ rootSpace H χ) :
    σ z ∈ rootSpace H (weightPerm σ hσ χ) :=
  map_mem_rootSpace σ hσ hz

/-- Membership of the image in the image root space detects membership in the original one, the
inverse automorphism transporting it back. -/
theorem map_mem_rootSpace_weightPerm_iff {χ : Weight R H L} {z : L} :
    σ z ∈ rootSpace H (weightPerm σ hσ χ) ↔ z ∈ rootSpace H χ := by
  refine ⟨fun hz => ?_, map_mem_rootSpace_weightPerm σ hσ⟩
  have h := map_mem_rootSpace_weightPerm σ.symm
    (LieSubalgebra.map_symm_eq_self_of_map_eq_self σ hσ) hz
  rwa [LieEquiv.symm_apply_apply, ← weightPerm_symm σ hσ, Equiv.symm_apply_apply] at h

/-- A weight is zero exactly when its image under the induced permutation is. -/
@[simp]
theorem weightPerm_isZero_iff {χ : Weight R H L} :
    (weightPerm σ hσ χ).IsZero ↔ χ.IsZero := by
  simp only [← Weight.coe_eq_zero_iff, coe_weightPerm]
  constructor
  · intro h
    funext y
    simpa using congrFun h (σ.ofSubalgebras H H hσ y)
  · intro h
    funext y
    simpa using congrFun h ((σ.ofSubalgebras H H hσ).symm y)

/-- A weight is zero exactly when its preimage under the induced permutation is. -/
@[simp]
theorem weightPerm_symm_isZero_iff {χ : Weight R H L} :
    ((weightPerm σ hσ).symm χ).IsZero ↔ χ.IsZero := by
  have h := weightPerm_isZero_iff σ hσ (χ := (weightPerm σ hσ).symm χ)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The induced permutation of the weights carries roots to roots. -/
theorem weightPerm_isNonZero {χ : Weight R H L} (hχ : χ.IsNonZero) :
    (weightPerm σ hσ χ).IsNonZero := fun h => hχ ((weightPerm_isZero_iff σ hσ).mp h)

/-- The inverse of the induced permutation of the weights carries roots to roots. -/
theorem weightPerm_symm_isNonZero {χ : Weight R H L} (hχ : χ.IsNonZero) :
    ((weightPerm σ hσ).symm χ).IsNonZero :=
  fun h => hχ ((weightPerm_symm_isZero_iff σ hσ).mp h)

end WeightPerm

section WeightInversion

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

variable (ω : L ≃ₗ⁅K⁆ L) (hω : ∀ y ∈ H, ω y = -y)

omit [CharZero K] in
include hω in
/-- **An automorphism acting by `-1` on the Cartan subalgebra inverts every weight.** The induced
permutation of the weights is negation, so the automorphism carries the root space of `α` onto the
root space of `-α`. -/
theorem weightPerm_eq_neg (α : Weight K H L) :
    weightPerm ω (LieSubalgebra.map_eq_self_of_forall_mem_apply_eq_neg ω hω) α = -α := by
  have hsymm : ∀ y : H, ω.symm (y : L) = -(y : L) := by
    intro y
    have h₁ : ω (-(y : L)) = (y : L) := by rw [hω _ (neg_mem y.2), neg_neg]
    calc ω.symm (y : L) = ω.symm (ω (-(y : L))) := by rw [h₁]
      _ = -(y : L) := ω.symm_apply_apply _
  ext y
  have hy :
      (ω.ofSubalgebras H H (LieSubalgebra.map_eq_self_of_forall_mem_apply_eq_neg ω hω)).symm y =
        -y := by
    refine Subtype.ext ?_
    rw [LieEquiv.ofSubalgebras_symm_apply, hsymm y]
    simp
  rw [weightPerm_apply_apply, hy, map_neg, Weight.coe_neg, Pi.neg_apply]

end WeightInversion

section Killing

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

variable (σ : L ≃ₗ⁅K⁆ L) (hσ : H.map (σ : L →ₗ⁅K⁆ L) = H)

include hσ

omit [CharZero K] in
/-- The induced permutation of the weights commutes with negation, since precomposition with the
restricted automorphism is linear in the weight. -/
@[simp]
theorem weightPerm_neg (α : Weight K H L) :
    weightPerm σ hσ (-α) = -weightPerm σ hσ α := by
  ext y
  simp

omit [CharZero K] in
/-- The inverse of the induced permutation of the weights also commutes with negation. -/
@[simp]
theorem weightPerm_symm_neg (α : Weight K H L) :
    (weightPerm σ hσ).symm (-α) = -((weightPerm σ hσ).symm α) :=
  (weightPerm σ hσ).injective <| by
    rw [Equiv.apply_symm_apply, weightPerm_neg, Equiv.apply_symm_apply]

/-- A normalising automorphism sends the coroot of a root to the coroot of the permuted root. -/
theorem map_coroot_weightPerm {α : Weight K H L} :
    σ (LieAlgebra.IsKilling.coroot α : L) =
      (LieAlgebra.IsKilling.coroot (weightPerm σ hσ α) : L) := by
  by_cases hα : α.IsZero
  · simp only [LieAlgebra.IsKilling.coroot_eq_zero_iff.mpr hα,
      LieAlgebra.IsKilling.coroot_eq_zero_iff.mpr ((weightPerm_isZero_iff σ hσ).mpr hα),
      ZeroMemClass.coe_zero, map_zero]
  obtain ⟨h, e, f, t, he, hf⟩ := LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero hα
  have hh : h = (LieAlgebra.IsKilling.coroot α : L) := t.h_eq_coroot hα he hf
  have he' : σ e ∈ rootSpace H (weightPerm σ hσ α) := map_mem_rootSpace_weightPerm σ hσ he
  have hf' : σ f ∈ rootSpace H (-weightPerm σ hσ α : Weight K H L) := by
    rw [← weightPerm_neg σ hσ α]
    exact map_mem_rootSpace_weightPerm σ hσ hf
  rw [← hh]
  have hh' : (σ : L →ₗ⁅K⁆ L) h ≠ 0 := fun hz => t.h_ne_zero (σ.injective (by simpa using hz))
  exact (t.map (σ : L →ₗ⁅K⁆ L) hh').h_eq_coroot
    (weightPerm_isNonZero σ hσ hα) he' hf'

end Killing

section Sl2System

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

variable (σ : L ≃ₗ⁅K⁆ L) (hσ : H.map (σ : L →ₗ⁅K⁆ L) = H)

namespace IsSl2System

variable {x : Weight K H L → L} (hx : IsSl2System x)

include hx

/-- Transporting a normalised family of root vectors along an automorphism normalising the Cartan
subalgebra gives a normalised family again: the root vector at `α` is the image of the root vector
at the preimage of `α`.

The normalisation survives because a normalising automorphism sends the coroot of a root to the
coroot of the permuted root, by `TauCeti.map_coroot_weightPerm`. -/
theorem map : IsSl2System fun α => σ (x ((weightPerm σ hσ).symm α)) where
  mem_rootSpace α := by
    have h := map_mem_rootSpace_weightPerm σ hσ
      (hx.mem_rootSpace ((weightPerm σ hσ).symm α))
    rwa [Equiv.apply_symm_apply] at h
  lie_neg α hα := by
    have hβ : ((weightPerm σ hσ).symm α).IsNonZero := weightPerm_symm_isNonZero σ hσ hα
    rw [weightPerm_symm_neg, ← σ.map_lie, hx.lie_neg _ hβ,
      map_coroot_weightPerm σ hσ, Equiv.apply_symm_apply]
  eq_zero_of_isZero α hα := by
    rw [hx.eq_zero_of_isZero _ ((weightPerm_symm_isZero_iff σ hσ).mpr hα), map_zero]

/-- A normalising automorphism scales each root vector: the image of `x α` is a nonzero multiple of
the root vector at the permuted root, because the root spaces are lines. -/
theorem exists_map_eq_smul {α : Weight K H L} (hα : α.IsNonZero) :
    ∃ c : K, c ≠ 0 ∧ σ (x α) = c • x (weightPerm σ hσ α) := by
  obtain ⟨c, hc₀, hc⟩ := hx.exists_ne_zero_eq_smul (weightPerm σ hσ α) (hx.map σ hσ)
    (weightPerm_isNonZero σ hσ hα)
  exact ⟨c, hc₀, by rwa [Equiv.symm_apply_apply] at hc⟩

/-- The scalars by which a normalising automorphism scales the root vectors at `α` and at `-α` are
inverse to one another. This is the only constraint the normalisation imposes on them. -/
theorem mul_eq_one_of_map_eq_smul {α : Weight K H L} (hα : α.IsNonZero) {c d : K}
    (hc : σ (x α) = c • x (weightPerm σ hσ α))
    (hd : σ (x (-α)) = d • x (-weightPerm σ hσ α)) : c * d = 1 := by
  refine hx.mul_eq_one_of_eq_smul (weightPerm σ hσ α) (hx.map σ hσ)
    (weightPerm_isNonZero σ hσ hα) ?_ ?_
  · rwa [Equiv.symm_apply_apply]
  · simpa only [weightPerm_symm_neg, Equiv.symm_apply_apply] using hd

end IsSl2System

end Sl2System

end TauCeti
