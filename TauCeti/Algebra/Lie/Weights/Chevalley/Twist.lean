/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Automorphism
public import TauCeti.Algebra.Lie.Weights.Chevalley.Involution

/-!
# Rescaling a normalised system against an automorphism inverting the Cartan subalgebra

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, let `H` be a splitting Cartan subalgebra, and let `ω` be a Lie automorphism of
`L` acting by `-1` on `H`. Such an `ω` inverts every weight, so it carries the root space of `α`
onto the root space of `-α`; since those spaces are lines, a normalised family `x` of root vectors
is scaled by `ω`:

```text
ω (x α) = c α • x (-α).
```

A **Chevalley system** is the special case `c ≡ -1`, which is what
`TauCeti.IsSl2System.isChevalleyNormalized_iff_exists_isChevalleySystem` shows to be the same thing
as having the Chevalley integers `±(p + 1)` as structure constants. The family in hand will not
satisfy `c ≡ -1`, and this file is about what has to be true for a rescaling of it to.

Two facts govern the scalars, and both are proved here.

*They are almost multiplicative.* Applying `ω` to `⁅x α, x β⁆ = N(α, β) • x γ` for `γ = α + β`
gives

```text
c γ * N(α, β) = c α * c β * N(-α, -β),
```

and multiplying by `N(α, β)` turns the right-hand factor into the invariant
`N(α, β) N(-α, -β) = -(p + 1)²` of
`TauCeti.IsSl2System.structureConstant_mul_structureConstant_neg_neg`. So `-c γ` differs from
`(-c α) (-c β)` by the square `((p + 1) / N(α, β))²`, and the integrality of
`N(α, β)` is *exactly* the equation `c γ = -(c α * c β)`. In particular the square class of `-c α`
is multiplicative along root sums, which is the induction step of a reduction to the simple
roots.

*Square roots of them rescale the family.* Rescaling `x α` to `s α • x α` preserves the
normalisation exactly when `s α * s (-α) = 1`, and it multiplies `c α` by `s α ^ 2`. So `c α` can be
moved to `-1` precisely when `-c α` is a square, and choosing one root out of each opposite pair
with `TauCeti.exists_rootPairRepresentatives` makes the square roots at `α` and `-α` inverse to
each other. This is `TauCeti.IsSl2System.exists_isChevalleySystem_of_forall_exists_sq`.

Together these reduce the existence of a Chevalley system for a given `ω` to the statement that
`-c α` is a square at every root, and make that statement multiplicative along root sums. Two
things are deliberately left out. The automorphism `ω` is an input and is not produced here; and no
induction over root heights is carried out, so the reduction of the square condition from all roots
to a base is available as a step and is not taken. Carter builds a Chevalley basis by a different
route, a sign recursion over the extraspecial pairs enumerated in
`TauCeti/LinearAlgebra/RootSystem/ExtraspecialPair.lean`; going through an automorphism is the
route Bourbaki's definition of a Chevalley system suggests, and it is the one available when the
Chevalley involution is already visible on a presentation of `L`.

## Main results

* `TauCeti.IsSl2System.exists_ne_zero_map_eq_smul_neg` and
  `TauCeti.IsSl2System.ne_zero_of_map_eq_smul_neg`: the automorphism scales each root vector into
  the opposite root space, by a nonzero scalar.
* `TauCeti.IsSl2System.mul_eq_one_of_map_eq_smul_neg`: the scalars at `α` and `-α` are inverse.
* `TauCeti.IsSl2System.mul_structureConstant_eq_of_map_eq_smul_neg` and
  `TauCeti.IsSl2System.mul_sq_structureConstant_eq_of_map_eq_smul_neg`: the two forms of the
  multiplicativity relation along a root sum.
* `TauCeti.IsSl2System.structureConstant_eq_natCast_or_eq_neg_natCast_iff_of_map_eq_smul_neg`: a
  structure constant is a Chevalley integer exactly when the scalars multiply up to the expected
  sign.
* `TauCeti.IsSl2System.neg_eq_mul_sq_of_map_eq_smul_neg` and
  `TauCeti.IsSl2System.isSquare_neg_of_map_eq_smul_neg`: the square class of `-c α` is
  multiplicative along root sums.
* `TauCeti.IsSl2System.exists_isChevalleySystem_of_forall_exists_sq`: if every `-c α` is a square,
  the family rescales to a Chevalley system for `ω`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter VIII, §2, no. 4.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.2.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.1--4.2.

## Roadmap

Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md` builds the split reductive group scheme over
`ℤ` "via a Chevalley basis and the Kostant `ℤ`-form of the enveloping algebra", and
`TauCeti.IsChevalleySystem` is that Chevalley basis. Everything downstream of it —
`TauCeti.IsChevalleySystem.chevalleyLieLattice`, the adjoint admissible lattice, and the adjoint
elementary Chevalley group — takes one as a hypothesis, so producing one is the open step. This
file supplies the route through an automorphism inverting the Cartan subalgebra. Milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md` is the downstream consumer of the assembled pinned group
scheme.
-/

public section

namespace TauCeti

open LieAlgebra LieModule LieAlgebra.IsKilling

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

variable (ω : L ≃ₗ⁅K⁆ L) (hω : ∀ y ∈ H, ω y = -y)

/-! ## The scalars by which the automorphism moves a normalised family -/

namespace IsSl2System

variable {x : Weight K H L → L} (hx : IsSl2System x)

include hx

include hω in
/-- **An automorphism inverting the Cartan subalgebra scales each root vector into the opposite
root space.** The scalar is nonzero because the root spaces are lines and the automorphism is
injective. -/
theorem exists_ne_zero_map_eq_smul_neg {α : Weight K H L} (hα : α.IsNonZero) :
    ∃ c : K, c ≠ 0 ∧ ω (x α) = c • x (-α) := by
  obtain ⟨c, hc₀, hc⟩ :=
    hx.exists_map_eq_smul ω (map_eq_self_of_forall_mem_apply_eq_neg ω hω) hα
  exact ⟨c, hc₀, by rwa [weightPerm_eq_neg ω hω] at hc⟩

/-- A scalar witnessing the action of the automorphism on a root vector is nonzero. -/
theorem ne_zero_of_map_eq_smul_neg {α : Weight K H L} (hα : α.IsNonZero) {c : K}
    (hc : ω (x α) = c • x (-α)) : c ≠ 0 := by
  rintro rfl
  rw [zero_smul] at hc
  exact hx.ne_zero α hα (by simpa using congrArg ω.symm hc)

include hω in
/-- **The scalars at `α` and `-α` are inverse to one another.** This is the constraint the
normalisation `⁅x α, x (-α)⁆ = α^∨` imposes on an opposite pair; the constraints coming from a
root sum are recorded separately below. -/
theorem mul_eq_one_of_map_eq_smul_neg {α : Weight K H L} (hα : α.IsNonZero) {c d : K}
    (hc : ω (x α) = c • x (-α)) (hd : ω (x (-α)) = d • x α) : c * d = 1 := by
  refine hx.mul_eq_one_of_map_eq_smul ω (map_eq_self_of_forall_mem_apply_eq_neg ω hω) hα ?_ ?_
  · rwa [weightPerm_eq_neg ω hω]
  · rwa [weightPerm_eq_neg ω hω, neg_neg]

/-- **The scalars are multiplicative along a root sum, up to the structure constants.** Applying the
automorphism to `⁅x α, x β⁆ = N(α, β) • x γ` turns it into the bracket at the opposite roots.

The hypothesis on the automorphism is not used: only the three scalars are. -/
theorem mul_structureConstant_eq_of_map_eq_smul_neg (α β γ : Weight K H L) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) {a b c : K}
    (ha : ω (x α) = a • x (-α)) (hb : ω (x β) = b • x (-β)) (hc : ω (x γ) = c • x (-γ)) :
    c * hx.structureConstant α β γ hγ hαβ = a * b *
      hx.structureConstant (-α) (-β) (-γ) hγ.neg
        (Weight.coe_neg_eq_add_of_coe_eq_add (a := (α : H → K)) (b := β)
          (c := (-α : Weight K H L)) (d := (-β : Weight K H L))
          (by simp [add_assoc]) hαβ) := by
  have hneg : ((-γ : Weight K H L) : H → K) =
      ((-α : Weight K H L) : H → K) + ((-β : Weight K H L) : H → K) :=
    Weight.coe_neg_eq_add_of_coe_eq_add (a := (α : H → K)) (b := β)
      (c := (-α : Weight K H L)) (d := (-β : Weight K H L)) (by simp [add_assoc]) hαβ
  refine smul_left_injective K (hx.ne_zero (-γ) hγ.neg) ?_
  calc (c * hx.structureConstant α β γ hγ hαβ) • x (-γ)
      = hx.structureConstant α β γ hγ hαβ • (c • x (-γ)) := by
        rw [smul_smul, mul_comm]
    _ = hx.structureConstant α β γ hγ hαβ • ω (x γ) := by rw [hc]
    _ = ω (hx.structureConstant α β γ hγ hαβ • x γ) := (map_smul _ _ _).symm
    _ = ω ⁅x α, x β⁆ := by rw [← hx.lie_eq_structureConstant_smul α β γ hγ hαβ]
    _ = ⁅ω (x α), ω (x β)⁆ := ω.map_lie (x α) (x β)
    _ = ⁅a • x (-α), b • x (-β)⁆ := by rw [ha, hb]
    _ = (a * b) • ⁅x (-α), x (-β)⁆ := by rw [smul_lie, lie_smul, smul_smul]
    _ = (a * b) • (hx.structureConstant (-α) (-β) (-γ) hγ.neg hneg • x (-γ)) := by
        rw [hx.lie_eq_structureConstant_smul (-α) (-β) (-γ) hγ.neg]
    _ = (a * b * hx.structureConstant (-α) (-β) (-γ) hγ.neg hneg) • x (-γ) := by rw [smul_smul]

/-- **The multiplicativity relation with the opposite structure constant eliminated.** Multiplying
`TauCeti.IsSl2System.mul_structureConstant_eq_of_map_eq_smul_neg` by `N(α, β)` and using
`N(α, β) N(-α, -β) = -(p + 1)²` leaves only the root-string coefficient. -/
theorem mul_sq_structureConstant_eq_of_map_eq_smul_neg (α β γ : Weight K H L) (hα : α.IsNonZero)
    (hβ : β.IsNonZero) (hγ : γ.IsNonZero) (hαβ : (γ : H → K) = (α : H → K) + β) {a b c : K}
    (ha : ω (x α) = a • x (-α)) (hb : ω (x β) = b • x (-β)) (hc : ω (x γ) = c • x (-γ)) :
    c * hx.structureConstant α β γ hγ hαβ ^ 2 =
      -(a * b * ((chainBotCoeff α β + 1 : ℕ) : K) ^ 2) := by
  have h₁ := hx.mul_structureConstant_eq_of_map_eq_smul_neg ω α β γ hγ hαβ ha hb hc
  have h₂ := hx.structureConstant_mul_structureConstant_neg_neg α β γ hα hβ hγ hαβ
  linear_combination hx.structureConstant α β γ hγ hαβ * h₁ + a * b * h₂

/-- **Integrality of a structure constant is multiplicativity of the scalars.** The structure
constant at `(α, β)` is one of the Chevalley integers `±(p + 1)` exactly when the scalar at
`γ = α + β` is the negative of the product of the scalars at `α` and `β`.

Taking every scalar to be `-1`, which is what a Chevalley system does, makes the right-hand
condition hold at every root sum; this is the mechanism behind
`TauCeti.IsSl2System.isChevalleyNormalized_iff_exists_isChevalleySystem`. -/
theorem structureConstant_eq_natCast_or_eq_neg_natCast_iff_of_map_eq_smul_neg
    (α β γ : Weight K H L) (hα : α.IsNonZero) (hβ : β.IsNonZero) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) {a b c : K}
    (ha : ω (x α) = a • x (-α)) (hb : ω (x β) = b • x (-β)) (hc : ω (x γ) = c • x (-γ)) :
    (hx.structureConstant α β γ hγ hαβ = ((chainBotCoeff α β + 1 : ℕ) : K) ∨
        hx.structureConstant α β γ hγ hαβ = -((chainBotCoeff α β + 1 : ℕ) : K)) ↔
      c = -(a * b) := by
  rw [← hx.structureConstant_neg_neg_eq_neg_iff α β γ hα hβ hγ hαβ]
  have h₁ := hx.mul_structureConstant_eq_of_map_eq_smul_neg ω α β γ hγ hαβ ha hb hc
  have hN := hx.structureConstant_ne_zero α β γ hγ hαβ hα hβ
  have hab : a * b ≠ 0 :=
    mul_ne_zero (hx.ne_zero_of_map_eq_smul_neg ω hα ha)
      (hx.ne_zero_of_map_eq_smul_neg ω hβ hb)
  refine ⟨fun h ↦ mul_right_cancel₀ hN ?_, fun h ↦ mul_left_cancel₀ hab ?_⟩
  · rw [h₁, h]
    ring
  · rw [← h₁, h]
    ring

/-- **The square class of the negated scalar is multiplicative along a root sum.** The correcting
factor is the square of the ratio between the root-string coefficient and the structure constant. -/
theorem neg_eq_mul_sq_of_map_eq_smul_neg (α β γ : Weight K H L) (hα : α.IsNonZero)
    (hβ : β.IsNonZero) (hγ : γ.IsNonZero) (hαβ : (γ : H → K) = (α : H → K) + β) {a b c : K}
    (ha : ω (x α) = a • x (-α)) (hb : ω (x β) = b • x (-β)) (hc : ω (x γ) = c • x (-γ)) :
    -c = -a * -b *
      (((chainBotCoeff α β + 1 : ℕ) : K) / hx.structureConstant α β γ hγ hαβ) ^ 2 := by
  have hN := hx.structureConstant_ne_zero α β γ hγ hαβ hα hβ
  have h := hx.mul_sq_structureConstant_eq_of_map_eq_smul_neg ω α β γ hα hβ hγ hαβ ha hb hc
  field_simp
  linear_combination -h

/-- **If the negated scalars at `α` and `β` are squares, so is the one at `α + β`.** Iterating this
along a decomposition of a positive root into simple roots would reduce the square condition of
`TauCeti.IsSl2System.exists_isChevalleySystem_of_forall_exists_sq` to the simple roots; that
induction is not carried out here. -/
theorem isSquare_neg_of_map_eq_smul_neg (α β γ : Weight K H L) (hα : α.IsNonZero)
    (hβ : β.IsNonZero) (hγ : γ.IsNonZero) (hαβ : (γ : H → K) = (α : H → K) + β) {a b c : K}
    (ha : ω (x α) = a • x (-α)) (hb : ω (x β) = b • x (-β)) (hc : ω (x γ) = c • x (-γ))
    (hsa : IsSquare (-a)) (hsb : IsSquare (-b)) : IsSquare (-c) := by
  rw [hx.neg_eq_mul_sq_of_map_eq_smul_neg ω α β γ hα hβ hγ hαβ ha hb hc]
  exact (hsa.mul hsb).mul ⟨_, sq _⟩

/-! ## Rescaling to a Chevalley system -/

include hω in
/-- **A normalised family rescales to a Chevalley system when the negated scalars are squares.**
Writing `ω (x α) = c α • x (-α)`, the hypothesis is that `-c α` is a square at every root; the
conclusion is a normalised family `y` with `ω (y α) = -y (-α)`, that is, a Chevalley system for the
given automorphism.

The rescaling is by a square root `t α` of `-c α` at one root of each opposite pair and by its
inverse at the other, which is what keeps the normalisation `⁅y α, y (-α)⁆ = α^∨` intact. The pair
is chosen by `TauCeti.exists_rootPairRepresentatives`, and the constraint `c α * c (-α) = 1` of
`TauCeti.IsSl2System.mul_eq_one_of_map_eq_smul_neg` is what makes the two square roots inverse to
each other, so that one rescaling serves both roots of the pair. -/
theorem exists_isChevalleySystem_of_forall_exists_sq
    (hsq : ∀ α : Weight K H L, α.IsNonZero → ∃ t : K, ω (x α) = -(t ^ 2) • x (-α)) :
    ∃ y : Weight K H L → L, IsChevalleySystem ω y := by
  classical
  obtain ⟨s, hs⟩ := exists_rootPairRepresentatives K H (L := L)
  have key : ∀ α : Weight K H L, ∃ t : K, α.IsNonZero → ω (x α) = -(t ^ 2) • x (-α) := by
    intro α
    by_cases hα : α.IsNonZero
    · obtain ⟨t, ht⟩ := hsq α hα
      exact ⟨t, fun _ ↦ ht⟩
    · exact ⟨1, fun h ↦ absurd h hα⟩
  choose t ht using key
  have htne : ∀ α : Weight K H L, α.IsNonZero → t α ≠ 0 := by
    intro α hα h₀
    have h : ω (x α) = 0 := by rw [ht α hα, h₀]; simp
    exact hx.ne_zero α hα (by simpa using congrArg ω.symm h)
  have hopp : ∀ α : Weight K H L, α.IsNonZero → ω (x (-α)) = -(t (-α) ^ 2) • x α := by
    intro α hα
    simpa using ht (-α) hα.neg
  have hsqmul : ∀ α : Weight K H L, α.IsNonZero → t α ^ 2 * t (-α) ^ 2 = 1 := by
    intro α hα
    have h := hx.mul_eq_one_of_map_eq_smul_neg ω hω hα (ht α hα) (hopp α hα)
    linear_combination h
  set u : Weight K H L → K := fun α ↦ if α ∈ s then (t α)⁻¹ else t (-α) with hu
  have humem : ∀ α : Weight K H L, α ∈ s → u α = (t α)⁻¹ := fun _ h ↦ ite_eq_left h
  have hunot : ∀ α : Weight K H L, α ∉ s → u α = t (-α) := fun _ h ↦ ite_eq_right h
  have huneg : ∀ α : Weight K H L, α.IsNonZero → α ∈ s → u (-α) = t α := by
    intro α hα h
    rw [hunot _ ((hs α hα).1 h), neg_neg]
  have huneg' : ∀ α : Weight K H L, α.IsNonZero → α ∉ s → u (-α) = (t (-α))⁻¹ := by
    intro α hα h
    exact humem _ (not_not.1 fun h' ↦ h ((hs α hα).2 h'))
  have hu_mul : ∀ α : Weight K H L, α.IsNonZero → u α * u (-α) = 1 := by
    intro α hα
    by_cases h : α ∈ s
    · rw [humem α h, huneg α hα h, inv_mul_cancel₀ (htne α hα)]
    · rw [hunot α h, huneg' α hα h, mul_inv_cancel₀ (htne (-α) hα.neg)]
  have hu_key : ∀ α : Weight K H L, α.IsNonZero → u α * t α ^ 2 = u (-α) := by
    intro α hα
    by_cases h : α ∈ s
    · rw [humem α h, huneg α hα h]
      field_simp
    · rw [hunot α h, huneg' α hα h]
      have h₁ := hsqmul α hα
      have h₂ := htne (-α) hα.neg
      field_simp
      linear_combination h₁
  refine ⟨fun α ↦ u α • x α, ⟨⟨fun α ↦ ?_, fun α hα ↦ ?_, fun α hα ↦ ?_⟩, fun α ↦ ?_⟩⟩
  · exact Submodule.smul_mem _ _ (hx.mem_rootSpace α)
  · rw [smul_lie, lie_smul, smul_smul, hx.lie_neg α hα, hu_mul α hα, one_smul]
  · rw [hx.eq_zero_of_isZero α hα, smul_zero]
  · by_cases hα : α.IsNonZero
    · rw [map_smul, ht α hα, smul_smul, mul_neg, hu_key α hα, neg_smul]
    · rw [hx.eq_zero_of_isZero α (not_not.1 hα),
        hx.eq_zero_of_isZero (-α) (not_not.1 hα).neg, smul_zero, smul_zero, map_zero, neg_zero]

end IsSl2System

end TauCeti
