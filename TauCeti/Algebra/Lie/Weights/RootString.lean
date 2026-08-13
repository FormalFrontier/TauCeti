/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem

public section

/-!
# Structure constants along a root string

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, let `H` be a splitting Cartan subalgebra, and let `α` and `β` be roots with
`α` non-zero. Writing the `α`-string through `β` as `β - pα, …, β, …, β + qα`, so that
`p = chainBotCoeff α β` and `q = chainTopCoeff α β`, this file proves the ladder identity

```text
⁅f, ⁅e, y⁆⁆ = (q * (p + 1)) • y   for y ∈ Lβ
```

for an `sl₂` triple `(h, e, f)` with `e ∈ Lα` and `f ∈ L(-α)`, together with the consequences that
make it the first step of the Chevalley basis theorem. Choosing non-zero root vectors `y ∈ Lβ` and
`z ∈ L(α + β)` and writing `⁅e, y⁆ = N • z` and `⁅f, z⁆ = N' • y`, the identity gives the product
constraint `N * N' = q * (p + 1)`. Integrality of the individual constants and the normalization
`N = ±(p + 1)` additionally require a coherent normalization of root vectors and symmetry
relations among the constants.

## Main results

* `TauCeti.lie_f_lie_e_eq_nsmul_of_mem_rootSpace`: the ladder identity above, and
  `TauCeti.lie_e_lie_f_eq_nsmul_of_mem_rootSpace` its mirror
  `⁅e, ⁅f, y⁆⁆ = (p * (q + 1)) • y`.
* `TauCeti.lie_ne_zero_of_mem_rootSpace`: if `α + β` is a root then `⁅e, y⁆ ≠ 0` for *every*
  non-zero `e ∈ Lα` and `y ∈ Lβ`.
* `TauCeti.exists_mem_rootSpace_lie_eq`: `⁅e, ·⁆` maps `Lβ` *onto* `L(α + β)`, so that
  `⁅Lα, Lβ⁆ = L(α + β)`.
* `TauCeti.exists_lie_eq_smul` and `TauCeti.ne_zero_of_lie_eq_smul`: the structure constant of a
  pair of root vectors exists and is non-zero.
* `TauCeti.mul_eq_of_lie_eq_smul`: the two structure constants of a root string multiply to
  `q * (p + 1)`.

## Implementation notes

The proof is the standard `sl₂` ladder computation, run against the primitive vector at the top of
the string. Mathlib already builds that primitive vector, in the course of proving
`LieAlgebra.IsKilling.exists_mem_rootSpace_lie_ne_zero`, but only records the *existence* of a pair
of root vectors with non-zero bracket. Because each root space is a line
(`LieAlgebra.IsKilling.finrank_rootSpace_eq_one`), the value of `⁅f, ⁅e, ·⁆⁆` on the whole of `Lβ`
is determined by its value on `f ^ q` applied to that primitive vector, which is what turns the
existential into the identity proved here; `TauCeti.lie_ne_zero_of_mem_rootSpace` is then the
universally quantified form of Mathlib's lemma.

The scalar is stated as an `ℕ`-scalar action rather than as a cast into `K` to expose the
combinatorial root-string coefficient directly.

## References

This file advances the target "The Chevalley--Demazure construction" of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, which builds the pinned group scheme over `ℤ` "via a
Chevalley basis and the Kostant `ℤ`-form of the enveloping algebra": the structure constants of a
Chevalley basis are the numbers `N` above. The product constraint `N * N' = q * (p + 1)`, together
with a coherent normalization of root vectors and additional symmetry relations, leads to the
integral normalization `N = ±(p + 1)`.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §25.1.
* R. W. Carter, *Simple Groups of Lie Type*, §4.1.
-/

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-! ### The ladder identity -/

/-- The ladder identity along a root string. If `(h, e, f)` is an `sl₂` triple with `e` in the
root space of a non-zero root `α` and `f` in the root space of `-α`, then for every `y` in the
root space of a non-zero root `β`,

```text
⁅f, ⁅e, y⁆⁆ = (q * (p + 1)) • y,
```

where `β - pα, …, β, …, β + qα` is the `α`-string through `β`.

The scalar is a natural number; this is Humphreys, *Introduction to Lie Algebras and
Representation Theory*, §25.1. -/
theorem lie_f_lie_e_eq_nsmul_of_mem_rootSpace {α β : Weight K H L} (hα : α.IsNonZero)
    (hβ : β.IsNonZero) {h e f : L} (t : IsSl2Triple h e f) (he : e ∈ rootSpace H α)
    (hf : f ∈ rootSpace H (-α)) {y : L} (hy : y ∈ rootSpace H β) :
    ⁅f, ⁅e, y⁆⁆ = (chainTopCoeff α β * (chainBotCoeff α β + 1)) • y := by
  obtain rfl := t.h_eq_coroot hα he hf
  obtain ⟨x, hx, hx₀⟩ := (chainTop α β).exists_ne_zero
  have prim : t.HasPrimitiveVectorWith x (chainLength α β : K) :=
    { ne_zero := hx₀
      lie_h := (chainLength_smul α β hx).symm
      lie_e := by
        have hmem := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
        rwa [genWeightSpace_add_chainTop α β hα] at hmem }
  have hmem : (toEnd K L L f ^ chainTopCoeff α β) x ∈ rootSpace H β := by
    have hco : chainTopCoeff α β • (-⇑α) + chainTop α β = β := by
      rw [coe_chainTop', smul_neg]; abel
    rw [← hco]
    exact toEnd_pow_apply_mem hf hx (chainTopCoeff α β)
  have hmem₀ : (toEnd K L L f ^ chainTopCoeff α β) x ≠ 0 :=
    prim.pow_toEnd_f_ne_zero_of_eq_nat rfl (chainTopCoeff_le_chainLength α β)
  have key : ⁅f, ⁅e, (toEnd K L L f ^ chainTopCoeff α β) x⁆⁆ =
      ((chainTopCoeff α β * (chainBotCoeff α β + 1) : ℕ) : K) •
        (toEnd K L L f ^ chainTopCoeff α β) x := by
    rcases Nat.eq_zero_or_pos (chainTopCoeff α β) with hq | hq
    · rw [hq, pow_zero]
      simp [prim.lie_e]
    · obtain ⟨n, hn⟩ : ∃ n, chainTopCoeff α β = n + 1 := ⟨chainTopCoeff α β - 1, by omega⟩
      rw [hn, prim.lie_e_pow_succ_toEnd_f n, lie_smul, prim.lie_f_pow_toEnd_f n]
      congr 1
      have hlen : (chainLength α β : K) = (chainBotCoeff α β : K) + (n + 1) := by
        rw [← chainBotCoeff_add_chainTopCoeff α β, hn]
        push_cast
        ring
      rw [hlen]
      push_cast
      ring
  rw [← Nat.cast_smul_eq_nsmul K]
  obtain ⟨c, rfl⟩ : ∃ c : K, c • (toEnd K L L f ^ chainTopCoeff α β) x = y :=
    Submodule.mem_span_singleton.mp <| by
      rwa [← toSubmodule_rootSpace_eq_span β hβ _ hmem₀ hmem]
  rw [lie_smul, lie_smul, key, smul_comm]

/-- The ladder identity read down the string instead of up it: with the same notation,

```text
⁅e, ⁅f, y⁆⁆ = (p * (q + 1)) • y   for y ∈ Lβ.
```
-/
theorem lie_e_lie_f_eq_nsmul_of_mem_rootSpace {α β : Weight K H L} (hα : α.IsNonZero)
    (hβ : β.IsNonZero) {h e f : L} (t : IsSl2Triple h e f) (he : e ∈ rootSpace H α)
    (hf : f ∈ rootSpace H (-α)) {y : L} (hy : y ∈ rootSpace H β) :
    ⁅e, ⁅f, y⁆⁆ = (chainBotCoeff α β * (chainTopCoeff α β + 1)) • y := by
  have he' : e ∈ rootSpace H (-⇑(-α : Weight K H L)) := by simpa using he
  have hf' : f ∈ rootSpace H (⇑(-α : Weight K H L)) := by simpa using hf
  simpa using
    lie_f_lie_e_eq_nsmul_of_mem_rootSpace (α := (-α : Weight K H L)) hα.neg hβ t.symm hf' he' hy

/-! ### Consequences for the structure constants -/

/-- If `α + β` is a root then *every* non-zero root vector of `α` brackets every non-zero root
vector of `β` to something non-zero. This is the universally quantified form of Mathlib's
`LieAlgebra.IsKilling.exists_mem_rootSpace_lie_ne_zero`. -/
theorem lie_ne_zero_of_mem_rootSpace {α β : Weight K H L} (hα : α.IsNonZero)
    (hβ : β.IsNonZero) (h_ne_bot : rootSpace H (α + β) ≠ ⊥) {e y : L}
    (he : e ∈ rootSpace H α) (he₀ : e ≠ 0) (hy : y ∈ rootSpace H β) (hy₀ : y ≠ 0) :
    ⁅e, y⁆ ≠ 0 := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mem_rootSpace_lie_ne_zero hα h_ne_bot
  obtain ⟨s, rfl⟩ : ∃ s : K, s • e = a :=
    Submodule.mem_span_singleton.mp <| by
      rwa [← toSubmodule_rootSpace_eq_span α hα _ he₀ he]
  obtain ⟨t, rfl⟩ : ∃ t : K, t • y = b :=
    Submodule.mem_span_singleton.mp <| by
      rwa [← toSubmodule_rootSpace_eq_span β hβ _ hy₀ hy]
  contrapose! hab
  simp [hab]

/-- The bracket with a non-zero root vector of `α` maps the root space of `β` *onto* the root
space of `α + β`. Together with `TauCeti.lie_ne_zero_of_mem_rootSpace` this is the statement
`⁅Lα, Lβ⁆ = L(α + β)` for roots `α`, `β` whose sum is a root. -/
theorem exists_mem_rootSpace_lie_eq {α β : Weight K H L} (hα : α.IsNonZero) (hβ : β.IsNonZero)
    (hαβ : ⇑α + ⇑β ≠ 0) (h_ne_bot : rootSpace H (α + β) ≠ ⊥) {e : L} (he : e ∈ rootSpace H α)
    (he₀ : e ≠ 0) {z : L} (hz : z ∈ rootSpace H (α + β)) :
    ∃ y ∈ rootSpace H β, ⁅e, y⁆ = z := by
  obtain ⟨y₀, hy₀, hy₀'⟩ := β.exists_ne_zero
  have h₁ : ⁅e, y₀⁆ ≠ 0 :=
    lie_ne_zero_of_mem_rootSpace hα hβ h_ne_bot he he₀ hy₀ hy₀'
  have h₂ : ⁅e, y₀⁆ ∈ rootSpace H (α + β) :=
    lie_mem_genWeightSpace_of_mem_genWeightSpace he hy₀
  obtain ⟨c, rfl⟩ : ∃ c : K, c • ⁅e, y₀⁆ = z :=
    Submodule.mem_span_singleton.mp <| by
      rwa [← toSubmodule_rootSpace_eq_span (⟨_, h_ne_bot⟩ : Weight K H L) hαβ _ h₁ h₂]
  exact ⟨c • y₀, SMulMemClass.smul_mem c hy₀, lie_smul c e y₀⟩

/-- The structure constant of a triple of root vectors exists: the bracket of a root vector of `α`
with one of `β` is a multiple of any non-zero root vector of `α + β`. -/
theorem exists_lie_eq_smul {α β : Weight K H L} (hαβ : ⇑α + ⇑β ≠ 0) {e y z : L}
    (he : e ∈ rootSpace H α) (hy : y ∈ rootSpace H β) (hz : z ∈ rootSpace H (α + β))
    (hz₀ : z ≠ 0) : ∃ N : K, ⁅e, y⁆ = N • z := by
  have h_ne_bot : rootSpace H (α + β) ≠ ⊥ := fun h => hz₀ (by simpa [h] using hz)
  have h₂ : ⁅e, y⁆ ∈ rootSpace H (α + β) :=
    lie_mem_genWeightSpace_of_mem_genWeightSpace he hy
  refine (Submodule.mem_span_singleton.mp ?_).imp fun c hc => hc.symm
  rwa [← toSubmodule_rootSpace_eq_span (⟨_, h_ne_bot⟩ : Weight K H L) hαβ _ hz₀ hz]

/-- A structure constant of a pair of roots whose sum is a root is non-zero. -/
theorem ne_zero_of_lie_eq_smul {α β : Weight K H L} (hα : α.IsNonZero)
    (hβ : β.IsNonZero) (h_ne_bot : rootSpace H (α + β) ≠ ⊥) {e y z : L}
    (he : e ∈ rootSpace H α) (he₀ : e ≠ 0) (hy : y ∈ rootSpace H β) (hy₀ : y ≠ 0)
    {N : K} (hN : ⁅e, y⁆ = N • z) : N ≠ 0 := by
  rintro rfl
  rw [zero_smul] at hN
  exact lie_ne_zero_of_mem_rootSpace hα hβ h_ne_bot he he₀ hy hy₀ hN

/-- The two structure constants of a root string multiply to `q * (p + 1)`, where
`β - pα, …, β, …, β + qα` is the `α`-string through `β`. Choosing `e`, `f` and `z` so that
`⁅e, y⁆ = N • z` and `⁅f, z⁆ = N' • y`, this says `N * N' = q * (p + 1)`. Integrality of the
individual constants and the Chevalley normalization `N = ±(p + 1)` additionally require a
coherent normalization of root vectors and symmetry relations among the constants. -/
theorem mul_eq_of_lie_eq_smul {α β : Weight K H L} (hα : α.IsNonZero) (hβ : β.IsNonZero)
    {h e f : L} (t : IsSl2Triple h e f) (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α))
    {y z : L} (hy : y ∈ rootSpace H β) (hy₀ : y ≠ 0) {N N' : K} (hN : ⁅e, y⁆ = N • z)
    (hN' : ⁅f, z⁆ = N' • y) :
    N * N' = (chainTopCoeff α β * (chainBotCoeff α β + 1) : ℕ) := by
  have hmain := lie_f_lie_e_eq_nsmul_of_mem_rootSpace hα hβ t he hf hy
  rw [hN, lie_smul, hN', smul_smul, ← Nat.cast_smul_eq_nsmul K] at hmain
  have hsub := sub_eq_zero.mpr hmain
  rw [← sub_smul, smul_eq_zero] at hsub
  exact sub_eq_zero.mp (hsub.resolve_right hy₀)

end TauCeti
