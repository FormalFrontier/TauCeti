/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import Mathlib.Algebra.Lie.Weights.Chain
public import TauCeti.Algebra.Lie.Sl2.WeightMultiplicity
public import TauCeti.Algebra.Lie.Weights.Diagonalizable
public import TauCeti.Algebra.Lie.Weights.Integrality
public import TauCeti.Algebra.Lie.Weights.Reflection
public import TauCeti.LinearAlgebra.Eigenspace.Separation

public section

/-!
# Weyl invariance of the weight multiplicities of a module

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, let `H` be a Cartan subalgebra and let `M` be a
finite-dimensional `L`-module. The weight spaces of `M` are honest simultaneous eigenspaces of `H`
(`TauCeti.genWeightSpace_eq_weightSpace`), so `χ ↦ dim Mχ` counts honest multiplicities. This file
proves that this multiplicity function is **invariant under the Weyl group** of the root system of
`H`; in particular the set of weights of `M` is stable under every reflection `s_α`.

The proof is the **direct rank-one argument**, not a corollary of Weyl's complete reducibility
theorem. That matters for the order of the development: the highest-weight theory wants Weyl
invariance of multiplicities *before* complete reducibility for `L`, whose usual proof consumes the
weight theory, and routing this statement through complete reducibility would make the dependency
circular. Only complete reducibility for `sl₂` is used here, through
`TauCeti.finrank_eigenspace_toEnd_neg`.

The argument, for a root `α` and a linear form `χ`, runs as follows.

* Cut the `α`-string through `χ` off at both ends: choose indices `p` and `q` beyond the two of
  interest, with `M_{p α + χ} = M_{q α + χ} = 0`, which is possible because a finite-dimensional
  module has only finitely many weights (`LieModule.eventually_genWeightSpace_smul_add_eq_bot`).
  Mathlib's `LieModule.genWeightSpaceChain` is then a module over the `sl₂` triple
  `(α^∨, eₐ, fₐ)` attached to `α`: it is stable under `H`, and its two cut-off lemmas say exactly
  that it is stable under `eₐ` and `fₐ`.
* Inside the string the coroot `α^∨` separates the weights: it acts on `M_{k α + χ}` by
  `2k + χ(α^∨)`, and these scalars are distinct, so each summand of the string is recovered from a
  single eigenspace of `α^∨` (`TauCeti.biSup_inf_eigenspace_eq_self`).
* The `sl₂` engine says the `c`- and `(-c)`-eigenspaces of the Cartan element have equal dimension
  on the string. Reading that back through the previous step turns it into the equality of the
  multiplicities at `k α + χ` and at `(-k - χ(α^∨)) α + χ`, whose `k = 0` case is the reflection
  `s_α χ = χ - χ(α^∨) • α`.

Integrality of `χ(α^∨)` enters only to know that the reflected form lies on the string at all; when
it fails, neither form is a weight and both multiplicities are zero, by
`TauCeti.genWeightSpaceOf_coroot_eq_bot_of_forall_ne_intCast`.

## Main results

* `TauCeti.finrank_weightSpace_neg_sub_zsmul_add`: the multiplicities along an `α`-string are
  symmetric about the midpoint of the reflection.
* `TauCeti.finrank_weightSpace_sub_apply_coroot_smul`: **the reflection `s_α` preserves weight
  multiplicities**, with no integrality hypothesis.
* `TauCeti.weightSpace_sub_apply_coroot_smul_eq_bot_iff`: consequently the set of weights of `M` is
  stable under the reflections.
* `TauCeti.finrank_weightSpace_weylGroup_smul`: **Weyl invariance.** The multiplicity function on
  the dual `Module.Dual K H` is invariant under the whole Weyl group of
  `LieAlgebra.IsKilling.rootSystem H`, and `TauCeti.weightSpace_weylGroup_smul_eq_bot_iff` records
  the resulting stability of the set of weights.

## References

This is the "Weyl-invariance of multiplicities, directly from `sl₂`" item of Layer 2 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §21.2.
-/

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w

section Killing

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M]

omit [CharZero K] [IsAlgClosed K] [IsKilling K L] [FiniteDimensional K L] [H.IsCartanSubalgebra]
  [LieModule K L M] [FiniteDimensional K M] in
/-- The type underlying a Lie submodule is the type underlying its carrier submodule, so the two
have the same dimension. This states once the definitional equality that the dimension counts
below pass through. -/
private theorem finrank_toSubmodule (N : LieSubmodule K H M) :
    finrank K N.toSubmodule = finrank K N :=
  rfl

omit [CharZero K] [IsAlgClosed K] [IsKilling K L] [FiniteDimensional K L]
  [H.IsCartanSubalgebra] in
/-- A weight space is trivial exactly when its dimension is zero. -/
private theorem weightSpace_eq_bot_iff_finrank_eq_zero (ψ : H → K) :
    weightSpace M ψ = ⊥ ↔ finrank K (weightSpace M ψ) = 0 := by
  rw [← LieSubmodule.toSubmodule_eq_bot, ← Submodule.finrank_eq_zero, finrank_toSubmodule]

/-! ### The `α`-string as a module over the `sl₂` triple attached to `α` -/

omit [IsAlgClosed K] [IsKilling K L] [FiniteDimensional K L] in
/-- **Cutting a weight chain off beyond a given index.** Along a nonzero direction `β` the weight
spaces `M_{j β + χ}` vanish for all large `j`, a finite-dimensional module having only finitely
many weights. This is the `ℤ`-indexed form, beyond an arbitrary bound `b`, of Mathlib's
`LieModule.eventually_genWeightSpace_smul_add_eq_bot`. -/
private theorem exists_lt_genWeightSpace_zsmul_add_eq_bot {β : H → K} (hβ : β ≠ 0) (χ : H → K)
    (b : ℤ) : ∃ j : ℤ, b < j ∧ genWeightSpace M (j • β + χ) = ⊥ := by
  obtain ⟨j, hj, hj'⟩ :=
    ((Filter.eventually_gt_atTop b.toNat).and
      (eventually_genWeightSpace_smul_add_eq_bot M β χ hβ)).exists
  exact ⟨(j : ℤ), lt_of_le_of_lt (Int.self_le_toNat b) (by exact_mod_cast hj),
    by rwa [natCast_zsmul]⟩

section Chain

variable {α : Weight K H L} {χ : H → K} {p q : ℤ} {h e f : L}

/-- **A cut-off root string is a module over the `sl₂` triple attached to the root.** If the weight
spaces at the two ends `p` and `q` of the `α`-string through `χ` vanish, then Mathlib's
`LieModule.genWeightSpaceChain M α χ p q` is stable under the raising and lowering elements of an
`sl₂` triple `(h, e, f)` with `e` in the root space of `α` and `f` in that of `-α`, by the two
cut-off lemmas `LieModule.lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left` and
`..._right`, and so is a Lie submodule for the subalgebra generated by the triple.

Its underlying submodule is the chain itself, recorded in
`TauCeti.chainSl2LieSubmodule_toSubmodule`. -/
private def chainSl2LieSubmodule (ht : IsSl2Triple h e f) (he : e ∈ rootSpace H α)
    (hf : f ∈ rootSpace H (-α)) (hp : genWeightSpace M (p • ⇑α + χ) = ⊥)
    (hq : genWeightSpace M (q • ⇑α + χ) = ⊥) :
    LieSubmodule K (ht.toLieSubalgebra K) M :=
  ht.lieSubmoduleOfStable (genWeightSpaceChain M (⇑α) χ p q).toSubmodule
    (fun _ hm ↦ lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right M (⇑α) χ p q hq he hm)
    (fun _ hm ↦ lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left M (⇑α) χ p q hp hf hm)

omit [CharZero K] [IsAlgClosed K] [IsKilling K L] [FiniteDimensional K L]
  [FiniteDimensional K M] in
/-- The submodule underlying `TauCeti.chainSl2LieSubmodule` is the weight chain itself. -/
private theorem chainSl2LieSubmodule_toSubmodule (ht : IsSl2Triple h e f) (he : e ∈ rootSpace H α)
    (hf : f ∈ rootSpace H (-α)) (hp : genWeightSpace M (p • ⇑α + χ) = ⊥)
    (hq : genWeightSpace M (q • ⇑α + χ) = ⊥) :
    (chainSl2LieSubmodule ht he hf hp hq).toSubmodule =
      (genWeightSpaceChain M (⇑α) χ p q).toSubmodule :=
  ht.lieSubmoduleOfStable_toSubmodule _ _ _

omit [CharZero K] [IsAlgClosed K] [IsKilling K L] [FiniteDimensional K L]
  [H.IsCartanSubalgebra] [FiniteDimensional K M] in
/-- **The Cartan element of the triple acts as the coroot.** On a Lie submodule for the subalgebra
generated by an `sl₂` triple whose Cartan element `h` is an element `x` of the Cartan subalgebra,
the action of `h` is the restriction of the action of `x` on the ambient module. -/
private theorem toEnd_h_eq_restrict (ht : IsSl2Triple h e f)
    (N : LieSubmodule K (ht.toLieSubalgebra K) M) {x : H} (hh : h = (x : L))
    (hA : ∀ v ∈ N.toSubmodule, toEnd K H M x v ∈ N.toSubmodule) :
    toEnd K (ht.toLieSubalgebra K) N ⟨h, ht.h_mem_toLieSubalgebra⟩ =
      (toEnd K H M x).restrict hA := by
  refine LinearMap.ext fun v ↦ Subtype.ext ?_
  rw [LinearMap.coe_restrict_apply]
  simp only [toEnd_apply_apply, LieSubmodule.coe_bracket, LieSubalgebra.coe_bracket_of_module, hh]

/-- **A weight space of a cut-off string is an eigenspace of the coroot on the string.** The coroot
`α^∨` acts on `M_{j α + χ}` by the scalar `2 j + n`, where `n = χ(α^∨)`, and these scalars are
distinct along the string; so each summand of the string is exactly the corresponding eigenspace of
the restriction of `α^∨` to the string (`TauCeti.biSup_inf_eigenspace_eq_self`), and in particular
has its dimension. -/
private theorem finrank_weightSpace_eq_finrank_eigenspace_restrict {n : ℤ} (hα : α.IsNonZero)
    (hn : χ (IsKilling.coroot α) = (n : K)) {N : Submodule K M}
    (hN : N = (genWeightSpaceChain M (⇑α) χ p q).toSubmodule)
    (hA : ∀ v ∈ N, toEnd K H M (IsKilling.coroot α) v ∈ N) {j : ℤ} (hj : j ∈ Set.Ioo p q) :
    finrank K (weightSpace M (j • ⇑α + χ)) =
      finrank K (Module.End.eigenspace
        ((toEnd K H M (IsKilling.coroot α)).restrict hA) ((2 * j + n : ℤ) : K)) := by
  subst hN
  set A : Module.End K M := toEnd K H M (IsKilling.coroot α)
  set g : ℤ → K := fun i ↦ ((2 * i + n : ℤ) : K) with hgdef
  have hval : ∀ i : ℤ, (i • ⇑α + χ) (IsKilling.coroot α) = g i := by
    intro i
    simp [hgdef, IsKilling.root_apply_coroot hα, hn, zsmul_eq_mul, mul_comm]
  have hginj : Function.Injective g := by
    intro i i' hii'
    have : 2 * i + n = 2 * i' + n := Int.cast_injective hii'
    omega
  have hWle : ∀ i : ℤ, (weightSpace M (i • ⇑α + χ)).toSubmodule ≤ A.eigenspace (g i) := by
    intro i m hm
    rw [Module.End.mem_eigenspace_iff, ← hval i]
    exact (mem_weightSpace _ m).1 hm _
  have hNsup : (genWeightSpaceChain M (⇑α) χ p q).toSubmodule =
      ⨆ i ∈ Set.Ioo p q, (weightSpace M (i • ⇑α + χ)).toSubmodule := by
    rw [genWeightSpaceChain_def]
    simp only [genWeightSpace_eq_weightSpace, LieSubmodule.iSup_toSubmodule]
  rw [← Submodule.finrank_map_subtype_eq (genWeightSpaceChain M (⇑α) χ p q).toSubmodule,
    ← Submodule.inf_genEigenspace A _ hA, hNsup,
    biSup_inf_eigenspace_eq_self (s := Set.Ioo p q) A
      (fun i ↦ (weightSpace M (i • ⇑α + χ)).toSubmodule) g
      (fun i (_ : i ∈ Set.Ioo p q) m hm ↦ hWle i hm) hj
      fun i _ hij ↦ fun hcon ↦ hij (hginj hcon),
    finrank_toSubmodule]

end Chain

/-! ### Reflection symmetry of the multiplicities -/

/-- **Reflection symmetry of the weight multiplicities along a root string.** Let `α` be a weight
of `L` and let `χ` be a function on the Cartan subalgebra whose value on the coroot `α^∨` is the
integer `n`. Then along the whole `α`-string through `χ`, the multiplicities are symmetric about
the midpoint of the reflection: the weight spaces at `(-k - n) • α + χ` and at `k • α + χ` have the
same dimension.

For `k = 0` this is the reflection `s_α χ = χ - χ(α^∨) • α`, which is
`TauCeti.finrank_weightSpace_sub_apply_coroot_smul` below. -/
theorem finrank_weightSpace_neg_sub_zsmul_add {α : Weight K H L} {χ : H → K} {n : ℤ}
    (hn : χ (IsKilling.coroot α) = (n : K)) (k : ℤ) :
    finrank K (weightSpace M ((-k - n) • ⇑α + χ)) = finrank K (weightSpace M (k • ⇑α + χ)) := by
  by_cases hα : α.IsNonZero
  swap
  · -- A zero weight translates nothing, so the two indices name the same weight space.
    have hz : (⇑α : H → K) = 0 := Weight.IsZero.eq (not_not.1 hα)
    rw [show ((-k - n) • ⇑α + χ) = k • ⇑α + χ by rw [hz, smul_zero, smul_zero]]
  obtain ⟨h, e, f, ht, he, hf⟩ := IsKilling.exists_isSl2Triple_of_weight_isNonZero hα
  have hh : h = (IsKilling.coroot α : L) := ht.h_eq_coroot hα he hf
  -- Cut the string off beyond both indices `k` and `-k - n`.
  set B : ℤ := (k.natAbs : ℤ) + (n.natAbs : ℤ) + 1 with hBdef
  obtain ⟨q, hqb, hq⟩ := exists_lt_genWeightSpace_zsmul_add_eq_bot (M := M) hα χ B
  obtain ⟨r, hrb, hr⟩ :=
    exists_lt_genWeightSpace_zsmul_add_eq_bot (M := M) (neg_ne_zero.2 hα) χ B
  set p : ℤ := -r with hpdef
  have hp : genWeightSpace M (p • ⇑α + χ) = ⊥ := by
    rwa [hpdef, neg_smul, ← smul_neg]
  -- The cut string, as a module over the `sl₂` triple, and the operator whose eigenspaces separate
  -- its summands.
  set N' : LieSubmodule K (ht.toLieSubalgebra K) M :=
    chainSl2LieSubmodule ht he hf hp hq with hN'def
  have hN'S : N'.toSubmodule = (genWeightSpaceChain M (⇑α) χ p q).toSubmodule := by
    rw [hN'def, chainSl2LieSubmodule_toSubmodule]
  have hA : ∀ v ∈ N'.toSubmodule, toEnd K H M (IsKilling.coroot α) v ∈ N'.toSubmodule := by
    rw [hN'S]
    intro v hv
    rw [LieSubmodule.mem_toSubmodule] at hv ⊢
    exact (genWeightSpaceChain M (⇑α) χ p q).lie_mem hv
  -- The `sl₂` engine: the eigenvalues `c` and `-c` have equal multiplicity on the string.
  have hsym : ∀ c : K,
      finrank K (Module.End.eigenspace ((toEnd K H M (IsKilling.coroot α)).restrict hA) c) =
      finrank K (Module.End.eigenspace ((toEnd K H M (IsKilling.coroot α)).restrict hA) (-c)) := by
    intro c
    rw [← toEnd_h_eq_restrict ht N' hh hA]
    exact finrank_eigenspace_toEnd_neg (M := N') ht.isSl2Triple_restrict c
  -- Both indices lie inside the cut, and their eigenvalues are opposite.
  have hmemk : k ∈ Set.Ioo p q := ⟨by omega, by omega⟩
  have hmemk' : (-k - n) ∈ Set.Ioo p q := ⟨by omega, by omega⟩
  rw [finrank_weightSpace_eq_finrank_eigenspace_restrict hα hn hN'S hA hmemk',
    finrank_weightSpace_eq_finrank_eigenspace_restrict hα hn hN'S hA hmemk,
    show ((2 * (-k - n) + n : ℤ) : K) = -((2 * k + n : ℤ) : K) by push_cast; ring, ← hsym]

/-- A form taking a non-integral value on the coroot `α^∨` is not a weight: it fails integrality,
`TauCeti.genWeightSpaceOf_coroot_eq_bot_of_forall_ne_intCast`, already for the single operator
`α^∨`. -/
private theorem weightSpace_eq_bot_of_forall_apply_coroot_ne_intCast (α : Weight K H L)
    {ψ : H → K} (hψ : ∀ z : ℤ, ψ (IsKilling.coroot α) ≠ (z : K)) :
    weightSpace M ψ = ⊥ :=
  eq_bot_iff.2 <| (weightSpace_le_genWeightSpace M ψ).trans <|
    (genWeightSpace_le_genWeightSpaceOf M (IsKilling.coroot α) ψ).trans_eq
      (genWeightSpaceOf_coroot_eq_bot_of_forall_ne_intCast hψ)

/-- **The reflection in a root preserves weight multiplicities.** For a weight `α` of a
Killing-semisimple Lie algebra and any function `χ` on the Cartan subalgebra, the weight spaces of
a finite-dimensional module at `χ` and at its reflection `s_α χ = χ - χ(α^∨) • α` have the same
dimension.

No integrality hypothesis is needed: if `χ(α^∨)` is not an integer then neither `χ` nor `s_α χ` is
a weight of `M`, both weight spaces are trivial, and the statement is `0 = 0`. -/
@[simp] theorem finrank_weightSpace_sub_apply_coroot_smul (α : Weight K H L) (χ : H → K) :
    finrank K (weightSpace M (χ - χ (IsKilling.coroot α) • ⇑α)) =
      finrank K (weightSpace M χ) := by
  by_cases hα : α.IsNonZero
  swap
  · -- A zero weight reflects nothing.
    have hz : (⇑α : H → K) = 0 := Weight.IsZero.eq (not_not.1 hα)
    rw [show (χ - χ (IsKilling.coroot α) • ⇑α) = χ by rw [hz, smul_zero, sub_zero]]
  by_cases hint : ∃ n : ℤ, χ (IsKilling.coroot α) = (n : K)
  · obtain ⟨n, hn⟩ := hint
    have hkey := finrank_weightSpace_neg_sub_zsmul_add (M := M) hn 0
    rw [hn]
    have h₁ : ((0 : ℤ) • ⇑α + χ) = χ := by simp
    have h₂ : ((-0 - n) • ⇑α + χ) = χ - (n : K) • ⇑α := by
      rw [Int.cast_smul_eq_zsmul K]
      module
    rwa [h₁, h₂] at hkey
  · -- Neither `χ` nor its reflection is a weight, so both weight spaces vanish.
    push Not at hint
    have hrefl : (χ - χ (IsKilling.coroot α) • ⇑α) (IsKilling.coroot α) =
        -χ (IsKilling.coroot α) := by
      simp only [Pi.sub_apply, Pi.smul_apply, IsKilling.root_apply_coroot hα, smul_eq_mul]
      ring
    have hint' : ∀ z : ℤ, (χ - χ (IsKilling.coroot α) • ⇑α) (IsKilling.coroot α) ≠ (z : K) := by
      intro z hz
      rw [hrefl, neg_eq_iff_eq_neg] at hz
      exact hint (-z) (by rw [hz, Int.cast_neg])
    rw [weightSpace_eq_bot_of_forall_apply_coroot_ne_intCast α hint,
      weightSpace_eq_bot_of_forall_apply_coroot_ne_intCast α hint']

/-- **The set of weights is stable under the reflections.** A form `χ` on the Cartan subalgebra is
a weight of a finite-dimensional module exactly when its reflection `s_α χ` is. -/
@[simp] theorem weightSpace_sub_apply_coroot_smul_eq_bot_iff (α : Weight K H L) (χ : H → K) :
    weightSpace M (χ - χ (IsKilling.coroot α) • ⇑α) = ⊥ ↔ weightSpace M χ = ⊥ := by
  rw [weightSpace_eq_bot_iff_finrank_eq_zero, weightSpace_eq_bot_iff_finrank_eq_zero,
    finrank_weightSpace_sub_apply_coroot_smul]

/-! ### Invariance under the Weyl group -/

/-- **The reflections of the root system preserve weight multiplicities.** -/
@[simp] theorem finrank_weightSpace_rootSystem_reflection (i : H.root) (χ : Dual K H) :
    finrank K (weightSpace M ⇑((IsKilling.rootSystem H).reflection i χ)) =
      finrank K (weightSpace M ⇑χ) := by
  rw [coe_rootSystem_reflection_apply]
  exact finrank_weightSpace_sub_apply_coroot_smul _ _

private theorem finrank_weightSpace_weylGroup_smul_of_mem
    {w : (IsKilling.rootSystem H).Aut} (hw : w ∈ (IsKilling.rootSystem H).weylGroup)
    (χ : Dual K H) :
    finrank K (weightSpace M ⇑(w • χ)) = finrank K (weightSpace M ⇑χ) := by
  induction hw using RootPairing.weylGroup.induction generalizing χ with
  | mem i =>
    rw [RootPairing.Equiv.reflection_smul]
    exact finrank_weightSpace_rootSystem_reflection i χ
  | one => rw [one_smul]
  | mul x y hx hy ihx ihy => rw [mul_smul, ihx, ihy]

/-- **Weyl invariance of the weight multiplicities.** For a finite-dimensional module `M` over a
Killing-semisimple Lie algebra, the function `χ ↦ dim Mχ` on the dual `Module.Dual K H` is
invariant under the Weyl group of the root system of `H`.

This is the direct, rank-one proof: it descends through
`TauCeti.finrank_weightSpace_sub_apply_coroot_smul` to the `sl₂` triple attached to each root, and
so is available before — and independently of — Weyl's complete reducibility theorem. -/
@[simp] theorem finrank_weightSpace_weylGroup_smul
    (w : (IsKilling.rootSystem H).weylGroup) (χ : Dual K H) :
    finrank K (weightSpace M ⇑(w • χ)) = finrank K (weightSpace M ⇑χ) :=
  finrank_weightSpace_weylGroup_smul_of_mem w.property χ

/-- **The set of weights is stable under the Weyl group.** A form `χ` on the Cartan subalgebra is
a weight of a finite-dimensional module exactly when its translate `w • χ` under an element of the
Weyl group is. -/
@[simp] theorem weightSpace_weylGroup_smul_eq_bot_iff
    (w : (IsKilling.rootSystem H).weylGroup) (χ : Dual K H) :
    weightSpace M ⇑(w • χ) = ⊥ ↔ weightSpace M ⇑χ = ⊥ := by
  rw [weightSpace_eq_bot_iff_finrank_eq_zero, weightSpace_eq_bot_iff_finrank_eq_zero,
    finrank_weightSpace_weylGroup_smul]

end Killing

end TauCeti
