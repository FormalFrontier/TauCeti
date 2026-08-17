/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Sl2System
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.RootString

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
* `TauCeti.IsSl2System.chainTopCoeff_mul_killingForm_root_neg_eq`: normalized Killing pairings at
  consecutive roots have the reciprocal root-length ratio.

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

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §25.1--25.2.
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

/-! ### The root-length ratio -/

private noncomputable def dualKillingForm : LinearMap.BilinForm K (Module.Dual K H) :=
  (LinearMap.id : Module.Dual K H →ₗ[K] Module.Dual K H).compl₂
    (cartanEquivDual H).symm.toLinearMap

omit [CharZero K] [IsTriangularizable K H L] in
@[simp]
private lemma dualKillingForm_apply (a b : Module.Dual K H) :
    dualKillingForm (H := H) a b = a ((cartanEquivDual H).symm b) :=
  rfl

omit [CharZero K] [IsTriangularizable K H L] in
private lemma dualKillingForm_symm :
    (dualKillingForm (H := H)).IsSymm := by
  constructor
  intro a b
  have h := (LieModule.traceForm_isSymm K H L).eq
    ((cartanEquivDual H).symm a) ((cartanEquivDual H).symm b)
  simpa only [dualKillingForm_apply, cartanEquivDual,
    LinearMap.BilinForm.apply_toDual_symm_apply, RingHom.id_apply] using h

private noncomputable def rootInvariantForm : (rootSystem H).InvariantForm where
  form := dualKillingForm
  symm := LinearMap.BilinForm.isSymm_iff.mp dualKillingForm_symm
  ne_zero i := by
    simpa only [dualKillingForm_apply, rootSystem_root_apply, Weight.toLinear_apply] using
      root_apply_cartanEquivDual_symm_ne_zero (H.isNonZero_coe_root i)
  isOrthogonal_reflection i := by
    intro a b
    have hd : i.1 ((cartanEquivDual H).symm i.1) ≠ 0 :=
      root_apply_cartanEquivDual_symm_ne_zero (H.isNonZero_coe_root i)
    have hai := (dualKillingForm_symm (H := H)).eq a i.1
    have hbi := (dualKillingForm_symm (H := H)).eq b i.1
    -- Definitional equality: `(rootSystem H).reflection i` expands to reflection along `i.1`.
    change dualKillingForm (a - a (coroot i.1) • (i.1 : Module.Dual K H))
      (b - b (coroot i.1) • (i.1 : Module.Dual K H)) = dualKillingForm a b
    simp only [map_sub, LinearMap.sub_apply, map_smul, map_nsmul, LinearMap.smul_apply,
      dualKillingForm_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, coroot]
    simp only [dualKillingForm_apply] at hai hbi
    rw [hai, hbi]
    simp only [Weight.toLinear_apply]
    field_simp
    ring

private lemma rootSystem_chainCoeffs_eq {a b : Weight K H L}
    (ha : a.IsNonZero) (hb : b.IsNonZero)
    (hab : LinearIndependent K ![(a : Module.Dual K H), (b : Module.Dual K H)]) :
    (rootSystem H).chainTopCoeff ⟨a, by simpa [LieSubalgebra.root] using ha⟩
        ⟨b, by simpa [LieSubalgebra.root] using hb⟩ = chainTopCoeff a b ∧
      (rootSystem H).chainBotCoeff ⟨a, by simpa [LieSubalgebra.root] using ha⟩
        ⟨b, by simpa [LieSubalgebra.root] using hb⟩ = chainBotCoeff a b := by
  let P := rootSystem H
  let ia : H.root := ⟨a, by simpa [LieSubalgebra.root] using ha⟩
  let ib : H.root := ⟨b, by simpa [LieSubalgebra.root] using hb⟩
  have hlin : LinearIndependent K ![P.root ia, P.root ib] := by
    simpa only [P, rootSystem_root_apply, ia, ib] using hab
  -- Step 1: Equivalence between range membership in `P.root` and Lie weight space non-triviality.
  have hmem (n : ℤ) :
      P.root ib + n • P.root ia ∈ Set.range P.root ↔ rootSpace H (n • a + b) ≠ ⊥ := by
    constructor
    · rintro ⟨c, hc⟩
      have hc' : (c.1 : H → K) = n • (a : H → K) + b := by
        ext z
        simpa only [P, rootSystem_root_apply, ia, ib, Weight.toLinear_apply,
          LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, add_comm] using DFunLike.congr_fun hc z
      simpa only [hc'] using c.1.genWeightSpace_ne_bot
    · intro h
      let c : Weight K H L := ⟨n • (a : H → K) + b, h⟩
      have hc : c.IsNonZero := by
        intro hc₀
        -- Definitional equality: `c.IsNonZero` is `(c : H → K) ≠ 0`, so `hc₀` means `c.1 = 0`.
        change n • (a : H → K) + b = 0 at hc₀
        have hrel : (n : K) • (a : Module.Dual K H) +
            (1 : K) • (b : Module.Dual K H) = 0 := by
          ext z
          simpa [Weight.toLinear_apply] using congrFun hc₀ z
        exact one_ne_zero (hab.eq_zero_of_pair hrel).2
      refine ⟨⟨c, by simpa [LieSubalgebra.root] using hc⟩, ?_⟩
      ext z
      simp [P, ia, ib, c, Weight.toLinear_apply, add_comm]
  -- Step 2: Compare `chainTopCoeff` via characterization by maximal non-vanishing.
  constructor
  · apply le_antisymm
    · have hz := (rootSpace_zsmul_add_ne_bot_iff a b ha
          (P.chainTopCoeff ia ib)).1 <| (hmem _).1 <| by
          simpa [Nat.cast_smul_eq_nsmul] using
            (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).2 le_rfl
      exact_mod_cast hz.1
    · rw [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin]
      have := (hmem (chainTopCoeff a b)).2 <| by
        simpa [Nat.cast_smul_eq_nsmul] using
          genWeightSpace_nsmul_add_ne_bot_of_le a b (le_refl (chainTopCoeff a b))
      simpa [Nat.cast_smul_eq_nsmul] using this
  -- Step 3: Compare `chainBotCoeff` via characterization by minimal non-vanishing.
  · apply le_antisymm
    · have hroot := (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin).2 le_rfl
      have := (hmem (-(P.chainBotCoeff ia ib : ℤ))).1 (by
        simpa [Nat.cast_smul_eq_nsmul, sub_eq_add_neg, neg_smul] using hroot)
      have hz := (rootSpace_zsmul_add_ne_bot_iff a b ha _).1 this |>.2
      simp only [neg_neg] at hz
      exact_mod_cast hz
    · rw [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin]
      have hroot := (rootSpace_zsmul_add_ne_bot_iff a b ha
        (-(chainBotCoeff a b : ℤ))).2 (by simp)
      have := (hmem (-(chainBotCoeff a b : ℤ))).2 hroot
      simpa [Nat.cast_smul_eq_nsmul, sub_eq_add_neg, neg_smul] using this

namespace IsSl2System

variable {x : Weight K H L → L} (hx : IsSl2System x)

include hx

/-- **Root-string ratio for normalized Killing pairings.** If `γ = α + β`, then

```text
q B(x β, x (-β)) = (p + 1) B(x γ, x (-γ)),
```

where `p = chainBotCoeff α β` and `q = chainTopCoeff α β`. This reciprocal form of the
invariant root-length identity supplies the cancellation used to normalize Chevalley structure
constants. -/
theorem chainTopCoeff_mul_killingForm_root_neg_eq
    (α β γ : Weight K H L) (hα : α.IsNonZero) (hβ : β.IsNonZero) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    (chainTopCoeff α β : K) * killingForm K L (x β) (x (-β)) =
      (chainBotCoeff α β + 1 : ℕ) * killingForm K L (x γ) (x (-γ)) := by
  let P := rootSystem H
  let i : H.root := ⟨α, by simpa [LieSubalgebra.root] using hα⟩
  let j : H.root := ⟨β, by simpa [LieSubalgebra.root] using hβ⟩
  let k : H.root := ⟨γ, by simpa [LieSubalgebra.root] using hγ⟩
  have hk : P.root k = P.root i + P.root j := by
    ext z
    simpa only [P, rootSystem_root_apply, i, j, k, Weight.toLinear_apply,
      LinearMap.add_apply, Pi.add_apply] using congrFun hαβ z
  have hlin := P.linearIndependent_of_add_mem_range_root' ⟨k, hk⟩
  have hcoeff := rootSystem_chainCoeffs_eq hα hβ (by
    simpa only [P, rootSystem_root_apply, i, j] using hlin)
  have hlength :=
    TauCeti.RootPairing.InvariantForm.chainTopCoeff_mul_apply_root_self_eq
      (P := P) (rootInvariantForm (H := H)) hk
  have hβkill := hx.killingForm_root_neg_eq β hβ
  have hγkill := hx.killingForm_root_neg_eq γ hγ
  simp only [rootInvariantForm, dualKillingForm_apply] at hlength
  rw [hcoeff.1, hcoeff.2] at hlength
  -- Definitional equality: `P.root k` reduces to `γ` and `P.root j` to `β`.
  change (chainTopCoeff α β : K) *
      (γ : Module.Dual K H) ((cartanEquivDual H).symm (γ : Module.Dual K H)) =
    (chainBotCoeff α β + 1 : ℕ) *
      (β : Module.Dual K H) ((cartanEquivDual H).symm (β : Module.Dual K H)) at hlength
  simp only [Weight.toLinear_apply] at hlength
  rw [hβkill, hγkill]
  have hβne := root_apply_cartanEquivDual_symm_ne_zero hβ
  have hγne := root_apply_cartanEquivDual_symm_ne_zero hγ
  field_simp
  rw [hlength]
  ring

end IsSl2System

end TauCeti
