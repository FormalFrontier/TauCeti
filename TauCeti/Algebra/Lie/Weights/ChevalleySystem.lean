/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Weights.StructureConstant.Normalization

/-!
# Root vectors compatible with a Chevalley involution

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form over a field of
characteristic zero, and let `H` be a splitting Cartan subalgebra. A normalized root-vector system
`x` satisfies

```text
⁅x α, x (-α)⁆ = α∨.
```

A *Chevalley system* additionally comes with a Lie automorphism `ω` exchanging opposite root
vectors with a sign:

```text
ω (x α) = -x (-α).
```

This file packages those two compatible pieces of data as `TauCeti.IsChevalleySystem`. The
compatibility already forces `ω` to act by negation on the Cartan subalgebra and to be an
involution on all of `L`: the coroots span `H`, while the root vectors together with `H` span `L`.

The main mathematical result is the integral normalization of every genuine root-sum bracket. If
`γ = α + β`, then

```text
⁅x α, x β⁆ = ±(p + 1) x γ,
```

where `p = chainBotCoeff α β`. The proof combines the Chevalley-involution symmetry and square
calculation from `TauCeti.Algebra.Lie.Weights.StructureConstant.Normalization` with the root-length
ratio from `TauCeti.Algebra.Lie.Weights.RootString`. The resulting integer-coefficient theorem is
stated both for the named structure constant and directly for the bracket, in the form consumed by
the integral root--coroot span.

## Main definitions and results

* `TauCeti.IsChevalleySystem`: a normalized root-vector system compatible with a Lie automorphism
  exchanging opposite root vectors with a sign.
* `TauCeti.IsChevalleySystem.map_coroot`: the automorphism negates every coroot.
* `TauCeti.IsChevalleySystem.map_cartan`: the automorphism negates the Cartan subalgebra.
* `TauCeti.IsChevalleySystem.involutive`: compatibility on the root vectors forces the
  automorphism to be an involution on all of `L`.
* `TauCeti.IsChevalleySystem.structureConstant_eq_natCast_or_eq_neg_natCast`: every structure
  constant is `p + 1` or its negative.
* `TauCeti.IsChevalleySystem.exists_int_lie_eq_smul`: every root-sum bracket has an integral
  coefficient.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.2.
* R. W. Carter, *Simple Groups of Lie Type*, §4.1.

This supplies the integral Chevalley-basis input to the explicit Chevalley--Demazure construction
in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, consumed by milestone L0 of the
`CFSGStatement` roadmap. The existence of a compatible Chevalley system remains downstream.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- A normalized family of root vectors compatible with a Chevalley involution. The Lie
automorphism `ω` exchanges each root vector with the negative of its opposite.

There is no separate involutivity field: `TauCeti.IsChevalleySystem.involutive` proves it from this
compatibility and the fact that the root vectors and Cartan subalgebra span the ambient Lie
algebra. -/
structure IsChevalleySystem (ω : L ≃ₗ⁅K⁆ L) (x : Weight K H L → L) : Prop where
  /-- The root vectors are normalized against the coroots. -/
  toIsSl2System : IsSl2System x
  /-- The automorphism exchanges each root vector with the negative of its opposite. -/
  map_root (α : Weight K H L) : ω (x α) = -x (-α)

attribute [simp] IsChevalleySystem.map_root

namespace IsChevalleySystem

variable {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : IsChevalleySystem ω x)

include hx

/-- A Chevalley-system automorphism sends every coroot to its negative. This follows from the
normalization of opposite root vectors, rather than being separate data. -/
theorem map_coroot (α : Weight K H L) :
    ω (coroot α : L) = -(coroot α : L) := by
  by_cases hα : α.IsNonZero
  · calc
      ω (coroot α : L) = ω ⁅x α, x (-α)⁆ := by rw [hx.toIsSl2System.lie_neg α hα]
      _ = ⁅ω (x α), ω (x (-α))⁆ := ω.map_lie (x α) (x (-α))
      _ = ⁅-x (-α), -x (-(-α))⁆ := by rw [hx.map_root α, hx.map_root (-α)]
      _ = ⁅x (-α), x α⁆ := by simp
      _ = -⁅x α, x (-α)⁆ := (lie_skew (x (-α)) (x α)).symm
      _ = -(coroot α : L) := by rw [hx.toIsSl2System.lie_neg α hα]
  · rw [coroot_eq_zero_iff.2 (not_not.mp hα)]
    simp

/-- A Chevalley-system automorphism acts by negation on the splitting Cartan subalgebra. It is
enough to check the coroots because they span `H`. -/
theorem map_cartan (h : H) : ω (h : L) = -(h : L) := by
  have hh : h ∈ Submodule.span K (Set.range (rootSystem H).coroot) := by
    rw [RootPairing.IsRootSystem.span_coroot_eq_top]
    trivial
  induction hh using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨α, rfl⟩ := hy
      rw [rootSystem_coroot_apply]
      exact hx.map_coroot α.1
  | zero => simp
  | add y z _ _ hy hz =>
      -- Expose the ambient addition hidden by the subtype coercion in the induction goal.
      change ω ((y : L) + (z : L)) = -((y : L) + (z : L))
      rw [map_add, hy, hz]
      abel
  | smul c y _ hy =>
      -- Expose the ambient scalar action hidden by the subtype coercion in the induction goal.
      change ω (c • (y : L)) = -(c • (y : L))
      rw [map_smul, hy]
      simp

/-- **A Chevalley-system automorphism is an involution.** The compatibility equation on root
vectors forces this globally: the root vectors together with the Cartan subalgebra span `L`. -/
theorem involutive : Function.Involutive ω := by
  intro z
  let f : L →ₗ[K] L := ω.toLinearMap.comp ω.toLinearMap - LinearMap.id
  have hroot : Submodule.span K (Set.range x) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro y ⟨α, rfl⟩
    -- Membership in the kernel is presented through the submodule coercion here.
    change f (x α) = 0
    simp [f, hx.map_root]
  have hcartan : H.toSubmodule ≤ LinearMap.ker f := by
    intro h hh
    -- Membership in the kernel is presented through the submodule coercion here.
    change f h = 0
    simp [f, hx.map_cartan ⟨h, hh⟩]
  have htop : (⊤ : Submodule K L) ≤ LinearMap.ker f := by
    rw [← hx.toIsSl2System.span_range_sup_toSubmodule_eq_top]
    exact sup_le hroot hcartan
  have hz : z ∈ LinearMap.ker f := htop trivial
  rw [LinearMap.mem_ker] at hz
  exact sub_eq_zero.mp (by simpa [f] using hz)

/-- A Chevalley-system automorphism is its own inverse. -/
theorem symm_eq : ω.symm = ω := by
  ext z
  apply ω.injective
  -- Expose the applications hidden by the `LieEquiv` coercions after applying injectivity.
  change ω (ω.symm z) = ω (ω z)
  rw [ω.apply_symm_apply, hx.involutive z]

/-- **Chevalley normalization of structure constants.** If `γ = α + β` is a genuine root sum,
then the structure constant of a Chevalley system is `p + 1` or its negative, where
`p = chainBotCoeff α β`.

The root-length ratio is automatic for normalized root vectors; compatibility with `ω` supplies
the symmetry that turns the root-string product formula into a square. -/
theorem structureConstant_eq_natCast_or_eq_neg_natCast
    (α β γ : Weight K H L) (hα : α.IsNonZero) (hβ : β.IsNonZero) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    hx.toIsSl2System.structureConstant α β γ hγ hαβ =
        ((chainBotCoeff α β + 1 : ℕ) : K) ∨
      hx.toIsSl2System.structureConstant α β γ hγ hαβ =
        -((chainBotCoeff α β + 1 : ℕ) : K) :=
  hx.toIsSl2System.structureConstant_eq_natCast_or_eq_neg_natCast_of_killingForm_ratio
    α β γ hα hβ hγ hαβ ω.toLieHom (hx.map_root α) (hx.map_root β) (hx.map_root γ)
    (hx.toIsSl2System.chainTopCoeff_mul_killingForm_root_neg_eq α β γ hα hβ hγ hαβ)

/-- The structure constant of a genuine root-sum bracket in a Chevalley system is the cast of an
integer. The preceding theorem identifies that integer more precisely as `±(p + 1)`. -/
theorem exists_int_structureConstant
    (α β γ : Weight K H L) (hα : α.IsNonZero) (hβ : β.IsNonZero) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    ∃ z : ℤ, hx.toIsSl2System.structureConstant α β γ hγ hαβ = (z : K) := by
  rcases hx.structureConstant_eq_natCast_or_eq_neg_natCast α β γ hα hβ hγ hαβ with h | h
  · exact ⟨chainBotCoeff α β + 1, by simpa using h⟩
  · exact ⟨-(chainBotCoeff α β + 1 : ℤ), by simpa using h⟩

/-- Every genuine root-sum bracket in a Chevalley system has an integral coefficient. This is the
form needed to prove that the integral span of root vectors and coroots is closed under the Lie
bracket. -/
theorem exists_int_lie_eq_smul
    (α β γ : Weight K H L) (hα : α.IsNonZero) (hβ : β.IsNonZero) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    ∃ z : ℤ, ⁅x α, x β⁆ = (z : K) • x γ := by
  obtain ⟨z, hz⟩ := hx.exists_int_structureConstant α β γ hα hβ hγ hαβ
  refine ⟨z, ?_⟩
  rw [hx.toIsSl2System.lie_eq_structureConstant_smul α β γ hγ hαβ, hz]

end IsChevalleySystem

end TauCeti
