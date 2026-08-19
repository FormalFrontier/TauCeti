/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Automorphism
public import TauCeti.Algebra.Lie.Weights.Chevalley.System

/-!
# What an automorphism does to a Chevalley system

Let `x` be a family of root vectors normalised against the coroots, and let `σ` be an automorphism
of `L` normalising the splitting Cartan subalgebra `H`. Then `σ` permutes the roots, and since the
root spaces are lines it carries `x α` to a nonzero multiple of `x (σ α)`:

```text
σ (x α) = ε α • x (σ α).
```

Two constraints pin the scalars. The normalisation `⁅x α, x (-α)⁆ = α^∨` is preserved by `σ`,
because `σ` sends `α^∨` to `(σ α)^∨`, and this forces `ε α * ε (-α) = 1`. If `σ` moreover commutes
with the Chevalley involution `ω` of the system, then applying both sides of `ω (x α) = -x (-α)`
gives `ε α = ε (-α)`. Together `ε α ^ 2 = 1`, so **every scalar is `1` or `-1`**.

That conclusion is the general-root form of a diagram automorphism of a split semisimple Lie
algebra. A graph symmetry of the Dynkin diagram is pinned by its action on the simple root vectors,
where the parameter is unchanged; on a general root vector a sign appears, and the signs cannot all
be normalised away. The type-`A` graph automorphism `X ↦ -J Xᵀ J⁻¹` of `sl n` already exhibits them.
What is proved here is that a sign is all that appears.

The hypothesis that `σ` commutes with `ω` is not automatic and is not a weakening: the Chevalley
involution attached to a normalised family is unique (`TauCeti.IsChevalleySystem.unique`), but `σ`
moves the family, so nothing forces the two automorphisms to commute. For the diagram automorphism
of a Serre presentation the commutation is visible on the generators, and it is available as
`TauCeti.GraphTwistedIndex.serreChevalleyInvolution_comm_serreGraphAut`.

Nothing here identifies the signs, and nothing here constructs an automorphism: the input is an
automorphism already in hand.

## Main results

* `TauCeti.IsSl2System.map`: the family obtained by transporting a normalised system along a
  normalising automorphism is again a normalised system.
* `TauCeti.IsSl2System.exists_map_eq_smul`: a normalising automorphism scales each root vector.
* `TauCeti.IsSl2System.mul_eq_one_of_map_eq_smul`: the scalars at `α` and `-α` are inverse.
* `TauCeti.IsChevalleySystem.eq_of_map_eq_smul`: commuting with the Chevalley involution makes
  those two scalars equal.
* `TauCeti.IsChevalleySystem.map_root_eq_or_eq_neg`: hence a root vector is carried to the root
  vector of the permuted root, up to sign.
* `TauCeti.IsChevalleySystem.exists_sign_map_root`: the same statement with the signs collected
  into a single function.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §16.5.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter VIII, §5, no. 3.

This is the general-root sign statement that milestone L1 of
`TauCetiRoadmap/CFSGStatement/README.md` asks to record as a consequence of the pinned
construction, and it supplies part of the diagram-automorphism data for Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`.
-/

public section

namespace TauCeti

open LieAlgebra LieModule LieAlgebra.IsKilling

universe u v

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
    have hβ : ((weightPerm σ hσ).symm α).IsNonZero := fun h => hα <| by
      have h' := (weightPerm_isZero_iff σ hσ (χ := (weightPerm σ hσ).symm α)).mpr h
      rwa [Equiv.apply_symm_apply] at h'
    rw [weightPerm_symm_neg, ← σ.map_lie, hx.lie_neg _ hβ,
      map_coroot_weightPerm σ hσ hβ, Equiv.apply_symm_apply]
  eq_zero_of_isZero α hα := by
    have hβ : ((weightPerm σ hσ).symm α).IsZero :=
      (weightPerm_isZero_iff σ hσ).mp (by rwa [Equiv.apply_symm_apply])
    rw [hx.eq_zero_of_isZero _ hβ, map_zero]

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

namespace IsChevalleySystem

variable {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : IsChevalleySystem ω x)

include hx

/-- If a normalising automorphism commutes with the Chevalley involution of the system, the scalars
it produces at `α` and at `-α` agree. Applying `σ` to `ω (x α) = -x (-α)` and `ω` to
`σ (x α) = c • x (σ α)` gives two expressions for the same vector. -/
theorem eq_of_map_eq_smul (hcomm : ∀ z : L, σ (ω z) = ω (σ z)) {α : Weight K H L}
    (hα : α.IsNonZero) {c d : K} (hc : σ (x α) = c • x (weightPerm σ hσ α))
    (hd : σ (x (-α)) = d • x (-weightPerm σ hσ α)) : c = d := by
  have key : (-c) • x (-weightPerm σ hσ α) = (-d) • x (-weightPerm σ hσ α) := by
    calc (-c) • x (-weightPerm σ hσ α)
        = ω (c • x (weightPerm σ hσ α)) := by
          rw [map_smul, hx.map_root, smul_neg, neg_smul]
      _ = ω (σ (x α)) := by rw [hc]
      _ = σ (ω (x α)) := (hcomm (x α)).symm
      _ = σ (-x (-α)) := by rw [hx.map_root]
      _ = (-d) • x (-weightPerm σ hσ α) := by rw [map_neg, hd, neg_smul]
  have hne : x (-weightPerm σ hσ α) ≠ 0 :=
    hx.toIsSl2System.ne_zero _ (weightPerm_isNonZero σ hσ hα).neg
  simpa using smul_left_injective K hne key

/-- **A normalising automorphism commuting with the Chevalley involution moves each root vector to
the root vector of the permuted root, up to sign.**

The two scalars attached to `α` and `-α` multiply to one and are equal, so each is a square root of
one in a field. No sign is claimed for any particular root: the type-`A` graph automorphism already
shows that they cannot all be made `+1`. -/
theorem map_root_eq_or_eq_neg (hcomm : ∀ z : L, σ (ω z) = ω (σ z)) (α : Weight K H L) :
    σ (x α) = x (weightPerm σ hσ α) ∨ σ (x α) = -x (weightPerm σ hσ α) := by
  by_cases hα : α.IsNonZero
  · obtain ⟨c, _, hc⟩ := hx.toIsSl2System.exists_map_eq_smul σ hσ hα
    obtain ⟨d, _, hd⟩ := hx.toIsSl2System.exists_map_eq_smul σ hσ hα.neg
    rw [weightPerm_neg] at hd
    have hcd : c * d = 1 := hx.toIsSl2System.mul_eq_one_of_map_eq_smul σ hσ hα hc hd
    have hceq : c = d := hx.eq_of_map_eq_smul σ hσ hcomm hα hc hd
    have hsq : c * c = 1 := by nth_rewrite 2 [hceq]; exact hcd
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact Or.inl (by rw [hc, h, one_smul])
    · exact Or.inr (by rw [hc, h, neg_smul, one_smul])
  · rw [not_not] at hα
    rw [hx.toIsSl2System.eq_zero_of_isZero α hα,
      hx.toIsSl2System.eq_zero_of_isZero _ ((weightPerm_isZero_iff σ hσ).mpr hα), map_zero]
    exact Or.inl rfl

/-- The signs of `TauCeti.IsChevalleySystem.map_root_eq_or_eq_neg`, collected into one function.
This is the form `γ (x_α) = ε_α • x_{γ α}` in which a graph automorphism of a pinned group is
usually stated. -/
theorem exists_sign_map_root (hcomm : ∀ z : L, σ (ω z) = ω (σ z)) :
    ∃ ε : Weight K H L → K, (∀ α, ε α = 1 ∨ ε α = -1) ∧
      ∀ α, σ (x α) = ε α • x (weightPerm σ hσ α) := by
  classical
  refine ⟨fun α => if σ (x α) = x (weightPerm σ hσ α) then 1 else -1, fun α => ?_, fun α => ?_⟩
  · by_cases h : σ (x α) = x (weightPerm σ hσ α) <;> simp [h]
  · by_cases h : σ (x α) = x (weightPerm σ hσ α)
    · simp [h]
    · rcases hx.map_root_eq_or_eq_neg σ hσ hcomm α with h' | h'
      · exact absurd h' h
      · simp [h']

end IsChevalleySystem

end TauCeti
