/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Root.IntegralLattice
public import TauCeti.Algebra.Lie.Weights.Chevalley.System

/-!
# The Chevalley lattice is stable under divided powers of the adjoint action

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field of
characteristic zero, let `H` be a splitting Cartan subalgebra, and let `x` be a Chevalley system
of root vectors. `TauCeti.IsChevalleySystem.chevalleyLieLattice` is the `ℤ`-span of the root
vectors and the coroots; it is a finite free full integral form of `L`.

This file proves that this lattice is stable under the *divided powers*

```text
(ad (x α)) ^ n / n !
```

of the adjoint action of each root vector. Stability under `ad (x α)` itself is the statement
that the lattice is a Lie subalgebra, and it already follows from integrality of the structure
constants; the content here is that the factorial in the denominator cancels.

The mechanism is the root string. Writing `p = chainBotCoeff α β` for the length of the
descending part of the `α`-chain through `β`, an induction along that chain gives

```text
(ad (x α)) ^ n (x β) = ± (p + 1)(p + 2) ⋯ (p + n) • x (β + n α),
```

or zero once the chain has been left. The coefficient is a rising factorial, hence is divisible
by `n !` — this is the classical computation of Humphreys §25.5. Two ingredients make the
induction go through: Mathlib's `LieAlgebra.IsKilling.chainBotCoeff_of_eq_zsmul_add`, which says
that moving one step up a root string lengthens its descending part by exactly one, and the
Chevalley normalization
`TauCeti.IsChevalleySystem.structureConstant_eq_natCast_or_eq_neg_natCast`, which identifies each
bracket coefficient as `± (p + 1)`.

The remaining generators of the lattice are handled directly: `x (-α)` spans an `sl₂`-triple with
`x α`, where the chain is short enough to compute by hand, and a coroot `β∨` is sent by the first
bracket to `-α β∨ • x α`, an integral multiple of `x α` because Cartan integers are integers, and
by the second bracket to zero.

Together with the binomial coefficients of the Cartan generators, which act diagonally on root
vectors, this is exactly the invariance needed to make `L` a module over the Kostant `ℤ`-form of
`U(L)` preserving a finite free lattice; that consequence is drawn in
`TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Adjoint`. This advances Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, consumed by milestone L0 of `CFSGStatement`.

## Main results

* `TauCeti.coe_add_natCast_smul_ne_zero`: an ascending root string through a root other than `-α`
  never meets the zero weight.
* `TauCeti.IsChevalleySystem.ad_pow_rootVector_eq_zero_or_exists`: the root-string form of the
  iterated adjoint action, with its rising-factorial coefficient.
* `TauCeti.IsChevalleySystem.inv_factorial_smul_ad_pow_mem_chevalleyLieLattice`: the Chevalley
  lattice is stable under every divided power of `ad (x α)`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §25.5.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- **Root strings avoid the zero weight.** If `α` and `β` are roots with `β ≠ -α`, then no
weight `β + n α` of the ascending `α`-string through `β` is zero.

Only `± α` are multiples of a root `α`, so a vanishing member of the string would force `β = α`
and then `(n + 1) α = 0`. -/
theorem coe_add_natCast_smul_ne_zero {α β : Weight K H L} (hα : α.IsNonZero) (hβ : β.IsNonZero)
    (hαβ : (α : H → K) + β ≠ 0) (n : ℕ) : (β : H → K) + (n : K) • (α : H → K) ≠ 0 := by
  intro h
  have hsmul : (β : H → K) = (-(n : K)) • (α : H → K) := by
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact h
  rcases eq_neg_or_eq_of_eq_smul α β hβ _ hsmul with hb | hb
  · refine hαβ ?_
    rw [hb, Weight.coe_neg]
    abel
  · refine hα ?_
    rw [hb] at h
    have hzero : ((n : K) + 1) • (α : H → K) = 0 := by
      rw [add_smul, one_smul, add_comm]
      exact h
    have hn1 : ((n : K) + 1) ≠ 0 := by
      have : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)
      push_cast at this
      exact this
    exact (smul_eq_zero.mp hzero).resolve_left hn1

namespace IsChevalleySystem

variable {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : IsChevalleySystem ω x)

include hx

/-- **The iterated adjoint action along a root string.** For roots `α` and `β` with `β ≠ -α`, the
`n`-th power of `ad (x α)` sends `x β` either to zero or to an integer multiple of the root
vector at `β + n α`, and the integer is the rising factorial
`(p + 1)(p + 2) ⋯ (p + n)`, where `p` is the descending `α`-chain coefficient at `β`.

Each step multiplies the coefficient by a Chevalley structure constant, which is `± (p + n + 1)`
by the normalization of a Chevalley system. -/
theorem ad_pow_rootVector_eq_zero_or_exists {α β : Weight K H L} (hα : α.IsNonZero)
    (hβ : β.IsNonZero)
    (hαβ : (α : H → K) + β ≠ 0) (n : ℕ) :
    ((ad K L (x α)) ^ n) (x β) = 0 ∨
      ∃ γ : Weight K H L, (γ : H → K) = (β : H → K) + (n : K) • (α : H → K) ∧
        chainBotCoeff (α : H → K) γ = chainBotCoeff (α : H → K) β + n ∧
        ∃ z : ℤ, z.natAbs = (chainBotCoeff (α : H → K) β + 1).ascFactorial n ∧
          ((ad K L (x α)) ^ n) (x β) = (z : K) • x γ := by
  induction n with
  | zero =>
    refine Or.inr ⟨β, by simp, by simp, 1, by simp, by simp⟩
  | succ n ih =>
    rcases ih with h0 | ⟨γ, hγcoe, hγbot, z, hznat, hz⟩
    · exact Or.inl (by rw [pow_succ', Module.End.mul_apply, h0, map_zero])
    have hγ : γ.IsNonZero := by
      rw [Weight.IsNonZero, Weight.IsZero, hγcoe]
      exact coe_add_natCast_smul_ne_zero hα hβ hαβ n
    have hshift : (α : H → K) + (γ : H → K) = (β : H → K) + ((n + 1 : ℕ) : K) • (α : H → K) := by
      rw [hγcoe]
      push_cast
      module
    have hαγ : (α : H → K) + (γ : H → K) ≠ 0 := by
      rw [hshift]
      exact coe_add_natCast_smul_ne_zero hα hβ hαβ (n + 1)
    have hstep : ((ad K L (x α)) ^ (n + 1)) (x β) = (z : K) • ⁅x α, x γ⁆ := by
      rw [pow_succ', Module.End.mul_apply, hz, map_smul, ad_apply]
    by_cases hbot : rootSpace H ((α : H → K) + (γ : H → K)) = ⊥
    · refine Or.inl ?_
      rw [hstep, hx.toIsSl2System.lie_eq_zero_of_rootSpace_add_eq_bot α γ hbot, smul_zero]
    refine Or.inr ?_
    set δ : Weight K H L := ⟨(α : H → K) + (γ : H → K), hbot⟩ with hδ
    have hδcoe : (δ : H → K) = (α : H → K) + (γ : H → K) := rfl
    have hδnz : δ.IsNonZero := by
      rw [Weight.IsNonZero, Weight.IsZero, hδcoe]
      exact hαγ
    have hlie : ⁅x α, x γ⁆ =
        hx.toIsSl2System.structureConstant α γ δ hδnz hδcoe • x δ :=
      hx.toIsSl2System.lie_eq_structureConstant_smul α γ δ hδnz hδcoe
    have hbotδ : chainBotCoeff (α : H → K) δ = chainBotCoeff (α : H → K) β + (n + 1) := by
      have := chainBotCoeff_of_eq_zsmul_add α γ hα δ 1 (by rw [hδcoe, one_smul])
      omega
    have hasc : (chainBotCoeff (α : H → K) β + 1).ascFactorial (n + 1) =
        (chainBotCoeff (α : H → K) γ + 1) * (chainBotCoeff (α : H → K) β + 1).ascFactorial n := by
      rw [Nat.ascFactorial_succ, hγbot]
      ring
    refine ⟨δ, hδcoe.trans hshift, hbotδ, ?_⟩
    rcases hx.structureConstant_eq_natCast_or_eq_neg_natCast α γ δ hα hγ hδnz hδcoe with hN | hN
    · refine ⟨z * ((chainBotCoeff (α : H → K) γ + 1 : ℕ) : ℤ), ?_, ?_⟩
      · rw [Int.natAbs_mul, hznat, Int.natAbs_natCast, hasc, Nat.mul_comm]
      · rw [hstep, hlie, hN, smul_smul, ← smul_smul]
        push_cast
        ring_nf
        module
    · refine ⟨z * (-((chainBotCoeff (α : H → K) γ + 1 : ℕ) : ℤ)), ?_, ?_⟩
      · rw [Int.natAbs_mul, hznat, Int.natAbs_neg, Int.natAbs_natCast, hasc, Nat.mul_comm]
      · rw [hstep, hlie, hN]
        push_cast
        module

/-- **Divided powers of the adjoint action of a root vector send root vectors into the Chevalley
lattice.** The rising factorial produced by the root-string computation is divisible by `n !`,
and the two exceptional strings — the one through `-α` and the degenerate ones — are handled
directly. -/
theorem inv_factorial_smul_ad_pow_rootVector_mem (α β : Weight K H L) (n : ℕ) :
    (n.factorial : K)⁻¹ • ((ad K L (x α)) ^ n) (x β) ∈ hx.chevalleyLieLattice := by
  rcases eq_or_ne (x β) 0 with hxb | hxb
  · rw [hxb, map_zero, smul_zero]
    exact zero_mem _
  rcases eq_or_ne (x α) 0 with hxa | hxa
  · match n with
    | 0 => simp
    | (m + 1) => simp [hxa, zero_pow]
  have hα : α.IsNonZero := fun hz => hxa (hx.toIsSl2System.eq_zero_of_isZero α hz)
  have hβ : β.IsNonZero := fun hz => hxb (hx.toIsSl2System.eq_zero_of_isZero β hz)
  by_cases hαβ : (α : H → K) + β = 0
  · -- the string through `-α`: the `sl₂`-triple computation
    have hβα : β = -α := by
      ext y
      have := congrFun hαβ y
      simp only [Pi.add_apply, Pi.zero_apply] at this
      simp only [Weight.coe_neg, Pi.neg_apply]
      linear_combination this
    subst hβα
    have h1 : (ad K L (x α)) (x (-α)) = (coroot α : L) := hx.toIsSl2System.lie_neg α hα
    have h2 : (ad K L (x α)) ((coroot α : L)) = (-2 : K) • x α := by
      rw [ad_apply, ← lie_skew, hx.toIsSl2System.lie_coroot α α, root_apply_coroot hα]
      module
    have h3 : (ad K L (x α)) ((-2 : K) • x α) = 0 := by
      rw [map_smul, ad_apply, lie_self, smul_zero]
    have h2' : ((ad K L (x α)) ^ 2) (x (-α)) = (-2 : K) • x α := by
      rw [pow_succ', Module.End.mul_apply, pow_one, h1, h2]
    have h3' : ((ad K L (x α)) ^ 3) (x (-α)) = 0 := by
      rw [pow_succ', Module.End.mul_apply, h2', h3]
    match n with
    | 0 => simp
    | 1 =>
      rw [pow_one, h1]
      simp
    | 2 =>
      -- the only nontrivial denominator: `2 !` cancels the `-2` coming from `ad (x α) α∨`
      have hcancel : ((Nat.factorial 2 : K))⁻¹ • ((-2 : K) • x α) = -(x α) := by
        rw [smul_smul]
        norm_num
      rw [h2', hcancel]
      exact neg_mem (hx.rootVector_mem_chevalleyLieLattice α)
    | (m + 3) =>
      rw [pow_add, Module.End.mul_apply, h3', map_zero, smul_zero]
      exact zero_mem _
  -- the generic string, where the rising factorial is divisible by `n !`
  rcases hx.ad_pow_rootVector_eq_zero_or_exists hα hβ hαβ n with h0 | ⟨γ, -, -, z, hznat, hz⟩
  · rw [h0, smul_zero]
    exact zero_mem _
  obtain ⟨w, hw⟩ : ((n.factorial : ℤ)) ∣ z := by
    refine Int.dvd_natAbs.1 ?_
    rw [hznat]
    exact Int.natCast_dvd_natCast.2 (Nat.factorial_dvd_ascFactorial _ _)
  have hfac : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  rw [hz, hw, smul_smul]
  have : (n.factorial : K)⁻¹ * (((n.factorial : ℤ) * w : ℤ) : K) = (w : K) := by
    push_cast
    field_simp
  rw [this, Int.cast_smul_eq_zsmul]
  exact zsmul_mem (hx.rootVector_mem_chevalleyLieLattice γ) w

/-- **Divided powers of the adjoint action of a root vector send coroots into the Chevalley
lattice.** A coroot is annihilated after two brackets, and the single surviving coefficient is a
Cartan integer. -/
theorem inv_factorial_smul_ad_pow_coroot_mem (α β : Weight K H L) (n : ℕ) :
    (n.factorial : K)⁻¹ • ((ad K L (x α)) ^ n) ((coroot β : L)) ∈ hx.chevalleyLieLattice := by
  set m : ℤ := rootCartanWeight α β with hm
  have h1 : (ad K L (x α)) ((coroot β : L)) = ((-m : ℤ) : K) • x α := by
    rw [ad_apply, ← lie_skew, hx.toIsSl2System.lie_coroot_rootVector β α, hm]
    push_cast
    module
  have h2 : (ad K L (x α)) (((-m : ℤ) : K) • x α) = 0 := by
    rw [map_smul, ad_apply, lie_self, smul_zero]
  match n with
  | 0 => simp
  | 1 =>
    rw [pow_one, h1]
    simpa [Int.cast_smul_eq_zsmul] using
      zsmul_mem (hx.rootVector_mem_chevalleyLieLattice α) (-m)
  | (k + 2) =>
    have h2' : ((ad K L (x α)) ^ 2) ((coroot β : L)) = 0 := by
      rw [pow_succ', Module.End.mul_apply, pow_one, h1, h2]
    rw [pow_add, Module.End.mul_apply, h2', map_zero, smul_zero]
    exact zero_mem _

/-- **The Chevalley lattice is stable under the divided powers of the adjoint action of a root
vector.** Every divided power `(ad (x α)) ^ n / n !` maps the lattice into itself.

Since the lattice is spanned over `ℤ` by the root vectors and the coroots, and each divided power
is an additive map, it suffices to check the two families of generators.

This is stability under the root-vector generators of the Kostant form only; the binomial
coefficients of the Cartan generators are treated separately, and stability under the whole
Kostant form is `TauCeti.IsChevalleySystem.chevalleyKostantForm_le_stabilizer`. -/
theorem inv_factorial_smul_ad_pow_mem_chevalleyLieLattice (α : Weight K H L) (n : ℕ) {y : L}
    (hy : y ∈ hx.chevalleyLieLattice) :
    (n.factorial : K)⁻¹ • ((ad K L (x α)) ^ n) y ∈ hx.chevalleyLieLattice := by
  set f : L →ₗ[ℤ] L :=
    (((n.factorial : K)⁻¹ • ((ad K L (x α)) ^ n) : Module.End K L)).restrictScalars ℤ with hf
  have hfapply : ∀ z : L, f z = (n.factorial : K)⁻¹ • ((ad K L (x α)) ^ n) z := fun z => rfl
  have hle : rootCorootSpan x ≤ (rootCorootSpan x).comap f := by
    rw [rootCorootSpan_le_iff]
    refine ⟨fun γ => ?_, fun γ => ?_⟩
    · rw [Submodule.mem_comap, hfapply]
      exact hx.mem_chevalleyLieLattice_iff.1 (hx.inv_factorial_smul_ad_pow_rootVector_mem α γ n)
    · rw [Submodule.mem_comap, hfapply]
      exact hx.mem_chevalleyLieLattice_iff.1 (hx.inv_factorial_smul_ad_pow_coroot_mem α γ n)
  rw [hx.mem_chevalleyLieLattice_iff] at hy ⊢
  have := hle hy
  rwa [Submodule.mem_comap, hfapply] at this

end IsChevalleySystem

end TauCeti
