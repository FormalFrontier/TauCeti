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
public import TauCeti.LinearAlgebra.Eigenspace.Invariant

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
  single eigenspace of `α^∨` (`TauCeti.biSup_inf_eigenspace_eq`).
* The `sl₂` engine says the `c`- and `(-c)`-eigenspaces of the Cartan element have equal dimension
  on the string. Reading that back through the previous step turns it into the equality of the
  multiplicities at `k α + χ` and at `(-k - χ(α^∨)) α + χ`, whose `k = 0` case is the reflection
  `s_α χ = χ - χ(α^∨) • α`.

Integrality of `χ(α^∨)` (`TauCeti.exists_int_apply_coroot`) enters only to know that the
reflected form lies on the string at all; when it fails, neither form is a weight and both
multiplicities are zero.

## Main results

* `TauCeti.finrank_weightSpace_zsmul_add`: the multiplicities along an `α`-string are symmetric
  about the midpoint of the reflection.
* `TauCeti.finrank_weightSpace_sub_apply_coroot_smul`: **the reflection `s_α` preserves weight
  multiplicities**, with no integrality hypothesis.
* `TauCeti.weightSpace_sub_apply_coroot_smul_eq_bot_iff`: consequently the set of weights of `M` is
  stable under the reflections.
* `TauCeti.finrank_weightSpace_weylGroup_smul`: **Weyl invariance.** The multiplicity function on
  `Module.Dual K H` is invariant under the whole Weyl group of `LieAlgebra.IsKilling.rootSystem H`.

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

/-- **Reflection symmetry of the weight multiplicities along a root string.** Let `α` be a root
and let `χ` be a function on the Cartan subalgebra whose value on the coroot `α^∨` is the integer
`n`. Then along the whole `α`-string through `χ`, the multiplicities are symmetric about the
midpoint of the reflection: the weight spaces at `k • α + χ` and at `(-k - n) • α + χ` have the
same dimension.

For `k = 0` this is the reflection `s_α χ = χ - χ(α^∨) • α`, which is
`TauCeti.finrank_weightSpace_sub_apply_coroot_smul` below. -/
theorem finrank_weightSpace_zsmul_add {α : Weight K H L} (hα : α.IsNonZero) {χ : H → K} {n : ℤ}
    (hn : χ (IsKilling.coroot α) = (n : K)) (k : ℤ) :
    finrank K (weightSpace M ((-k - n) • ⇑α + χ)) = finrank K (weightSpace M (k • ⇑α + χ)) := by
  obtain ⟨h, e, f, ht, he, hf⟩ := IsKilling.exists_isSl2Triple_of_weight_isNonZero hα
  have hh : h = (IsKilling.coroot α : L) := ht.h_eq_coroot hα he hf
  -- Cut the string off beyond both indices `k` and `-k - n`.
  obtain ⟨q₀, hqb₀, hq₀⟩ :=
    ((Filter.eventually_gt_atTop
      ((k.natAbs : ℤ) + (n.natAbs : ℤ) + 1).toNat).and
      (eventually_genWeightSpace_smul_add_eq_bot M (⇑α) χ hα)).exists
  let q : ℤ := q₀
  have hqb : (k.natAbs : ℤ) + (n.natAbs : ℤ) + 1 < q := by
    change (k.natAbs : ℤ) + (n.natAbs : ℤ) + 1 < (q₀ : ℤ)
    exact lt_of_le_of_lt (Int.self_le_toNat _) (by exact_mod_cast hqb₀)
  have hq : genWeightSpace M (q • ⇑α + χ) = ⊥ := by
    simpa only [q, natCast_zsmul] using hq₀
  obtain ⟨r₀, hrb₀, hp₀⟩ :=
    ((Filter.eventually_gt_atTop
      ((k.natAbs : ℤ) + (n.natAbs : ℤ) + 1).toNat).and
      (eventually_genWeightSpace_smul_add_eq_bot M (-⇑α) χ (neg_ne_zero.2 hα))).exists
  let p : ℤ := -(r₀ : ℤ)
  have hrb : (k.natAbs : ℤ) + (n.natAbs : ℤ) + 1 < (r₀ : ℤ) :=
    lt_of_le_of_lt (Int.self_le_toNat _) (by exact_mod_cast hrb₀)
  have hpb : p < -((k.natAbs : ℤ) + (n.natAbs : ℤ) + 1) := by
    dsimp only [p]
    omega
  have hp : genWeightSpace M (p • ⇑α + χ) = ⊥ := by
    change genWeightSpace M ((-(r₀ : ℤ)) • ⇑α + χ) = ⊥
    rw [neg_smul, ← smul_neg]
    simpa only [natCast_zsmul] using hp₀
  set N : LieSubmodule K H M := genWeightSpaceChain M (⇑α) χ p q with hNdef
  -- The operator whose eigenspaces separate the string.
  set A : Module.End K M := toEnd K H M (IsKilling.coroot α) with hAdef
  have hA : ∀ v ∈ N.toSubmodule, A v ∈ N.toSubmodule := fun v hv ↦ N.lie_mem hv
  -- The string is a module over the `sl₂` subalgebra attached to `α`.
  have hmem : ∀ x ∈ ht.toLieSubalgebra K, ∀ m ∈ N, ⁅x, m⁆ ∈ N := by
    intro x hx m hm
    obtain ⟨c₁, c₂, c₃, rfl⟩ := IsSl2Triple.mem_toLieSubalgebra_iff.1 hx
    have h₁ : ⁅e, m⁆ ∈ N :=
      lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right M (⇑α) χ p q hq he hm
    have h₂ : ⁅f, m⁆ ∈ N :=
      lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left M (⇑α) χ p q hp hf hm
    have h₃ : ⁅⁅e, f⁆, m⁆ ∈ N := by
      rw [ht.lie_e_f, hh]; exact hA m hm
    rw [← LieSubmodule.mem_toSubmodule] at h₁ h₂ h₃ ⊢
    simpa only [add_lie, smul_lie] using
      add_mem (add_mem (Submodule.smul_mem _ c₁ h₁) (Submodule.smul_mem _ c₂ h₂))
        (Submodule.smul_mem _ c₃ h₃)
  let N' : LieSubmodule K (ht.toLieSubalgebra K) M :=
    { toSubmodule := N.toSubmodule, lie_mem := fun {x m} hm ↦ hmem x x.2 m hm }
  -- On the string, the coroot acts as the Cartan element of the triple.
  have hop : toEnd K (ht.toLieSubalgebra K) N' ⟨h, ht.h_mem_toLieSubalgebra⟩ = A.restrict hA := by
    ext v
    -- There is no application lemma that simultaneously unfolds `toEnd` on the restricted
    -- Lie algebra and `Module.End.restrict`; expose their common underlying action explicitly.
    change ⁅h, (v : M)⁆ = A (v : M)
    simp only [hAdef, hh, toEnd_apply_apply, LieSubalgebra.coe_bracket_of_module]
  -- The `sl₂` engine: the eigenvalues `c` and `-c` have equal multiplicity on the string.
  have hsym : ∀ c : K, finrank K (Module.End.eigenspace (A.restrict hA) c) =
      finrank K (Module.End.eigenspace (A.restrict hA) (-c)) := by
    intro c
    rw [← hop]
    exact finrank_eigenspace_toEnd_neg (M := N') ht.isSl2Triple_restrict c
  -- The eigenvalue of the coroot along the string, as a function of the index.
  set g : ℤ → K := fun j ↦ (j • ⇑α + χ) (IsKilling.coroot α) with hgdef
  have hg : ∀ j : ℤ, g j = 2 * j + n := by
    intro j
    simp [hgdef, IsKilling.root_apply_coroot hα, hn, zsmul_eq_mul, mul_comm]
  have hginj : Function.Injective g := by
    intro i j hij
    rw [hg, hg, add_left_inj] at hij
    exact_mod_cast mul_left_cancel₀ (by norm_num : (2 : K) ≠ 0) hij
  -- Each weight space of the string is the corresponding eigenspace of the coroot.
  have hWle : ∀ j : ℤ, (weightSpace M (j • ⇑α + χ)).toSubmodule ≤ A.eigenspace (g j) := by
    intro j m hm
    rw [Module.End.mem_eigenspace_iff]
    exact (mem_weightSpace _ m).1 hm _
  have hNsup : N.toSubmodule =
      ⨆ j ∈ Set.Ioo p q, (weightSpace M (j • ⇑α + χ)).toSubmodule := by
    rw [hNdef, genWeightSpaceChain_def]
    simp only [genWeightSpace_eq_weightSpace, LieSubmodule.iSup_toSubmodule]
  have hcut : ∀ j ∈ Set.Ioo p q,
      finrank K (weightSpace M (j • ⇑α + χ)) =
        finrank K (Module.End.eigenspace (A.restrict hA) (g j)) := by
    intro j hj
    rw [← Submodule.finrank_map_subtype_eq N.toSubmodule,
      ← N.toSubmodule.inf_genEigenspace A hA, hNsup,
      biSup_inf_eigenspace_eq (s := Set.Ioo p q) A
        (fun i ↦ (weightSpace M (i • ⇑α + χ)).toSubmodule) g
        (fun i (_ : i ∈ Set.Ioo p q) m hm ↦ hWle i hm) hj
        fun i _ hik ↦ fun hcon ↦ hik (hginj hcon)]
    exact (LinearEquiv.refl K (weightSpace M (j • ⇑α + χ))).finrank_eq
  -- Both indices lie inside the cut.
  have hmemk : k ∈ Set.Ioo p q := ⟨by omega, by omega⟩
  have hmemk' : (-k - n) ∈ Set.Ioo p q := ⟨by omega, by omega⟩
  have hgk : g (-k - n) = -g k := by rw [hg, hg]; push_cast; ring
  rw [hcut _ hmemk', hcut _ hmemk, hgk, ← hsym]

/-- **The reflection in a root preserves weight multiplicities.** For a root `α` of a
Killing-semisimple Lie algebra and any function `χ` on the Cartan subalgebra, the weight spaces of
a finite-dimensional module at `χ` and at its reflection `s_α χ = χ - χ(α^∨) • α` have the same
dimension.

No integrality hypothesis is needed: if `χ(α^∨)` is not an integer then neither `χ` nor `s_α χ` is
a weight of `M`, both weight spaces are trivial, and the statement is `0 = 0`. -/
theorem finrank_weightSpace_sub_apply_coroot_smul {α : Weight K H L} (hα : α.IsNonZero)
    (χ : H → K) :
    finrank K (weightSpace M (χ - χ (IsKilling.coroot α) • ⇑α)) =
      finrank K (weightSpace M χ) := by
  by_cases hint : ∃ n : ℤ, χ (IsKilling.coroot α) = (n : K)
  · obtain ⟨n, hn⟩ := hint
    have hkey := finrank_weightSpace_zsmul_add (M := M) hα hn 0
    rw [hn]
    have h₁ : ((0 : ℤ) • ⇑α + χ) = χ := by simp
    have h₂ : ((-0 - n) • ⇑α + χ) = χ - (n : K) • ⇑α := by
      rw [Int.cast_smul_eq_zsmul K]
      module
    rwa [h₁, h₂] at hkey
  · -- Neither `χ` nor its reflection is a weight, so both weight spaces vanish.
    push Not at hint
    have hbot : ∀ ψ : H → K, ψ (IsKilling.coroot α) = χ (IsKilling.coroot α) ∨
        ψ (IsKilling.coroot α) = -χ (IsKilling.coroot α) → weightSpace M ψ = ⊥ := by
      intro ψ hψ
      by_contra hne
      have hne' : genWeightSpace M ψ ≠ ⊥ := by rwa [genWeightSpace_eq_weightSpace]
      obtain ⟨z, hz⟩ := exists_int_apply_coroot (M := M) ⟨ψ, hne'⟩ α
      rcases hψ with hψ | hψ
      · exact hint z (by rw [← hψ, ← hz]; rfl)
      · refine hint (-z) ?_
        rw [Int.cast_neg, ← hz, ← Weight.toLinear_apply, Weight.coe_coe,
          Weight.coe_weight_mk, hψ, neg_neg]
    have hrefl : (χ - χ (IsKilling.coroot α) • ⇑α) (IsKilling.coroot α) =
        -χ (IsKilling.coroot α) := by
      simp only [Pi.sub_apply, Pi.smul_apply, IsKilling.root_apply_coroot hα, smul_eq_mul]
      ring
    rw [hbot _ (Or.inl rfl), hbot _ (Or.inr hrefl)]

/-- **The set of weights is stable under the reflections.** A form `χ` on the Cartan subalgebra is
a weight of a finite-dimensional module exactly when its reflection `s_α χ` is. -/
theorem weightSpace_sub_apply_coroot_smul_eq_bot_iff {α : Weight K H L} (hα : α.IsNonZero)
    (χ : H → K) :
    weightSpace M (χ - χ (IsKilling.coroot α) • ⇑α) = ⊥ ↔ weightSpace M χ = ⊥ := by
  have key : ∀ ψ : H → K, weightSpace M ψ = ⊥ ↔ finrank K (weightSpace M ψ) = 0 := fun ψ ↦ by
    rw [← LieSubmodule.toSubmodule_eq_bot, ← Submodule.finrank_eq_zero]
    rfl
  rw [key, key, finrank_weightSpace_sub_apply_coroot_smul hα χ]

/-! ### Invariance under the Weyl group -/

/-- The reflection of the root system of `H` in a root `i`, read on the weight space
`Module.Dual K H`, is the reflection `χ ↦ χ - χ(αᵢ^∨) • αᵢ`. -/
@[simp] theorem coe_rootSystem_reflection_apply (i : H.root) (χ : Dual K H) :
    ⇑((IsKilling.rootSystem H).reflection i χ) =
      ⇑χ - χ (IsKilling.coroot (i : Weight K H L)) • ⇑(i : Weight K H L) := by
  ext x
  simp [RootPairing.reflection_apply, Weight.toLinear_apply]

/-- **The reflections of the root system preserve weight multiplicities.** -/
@[simp] theorem finrank_weightSpace_rootSystem_reflection (i : H.root) (χ : Dual K H) :
    finrank K (weightSpace M ⇑((IsKilling.rootSystem H).reflection i χ)) =
      finrank K (weightSpace M ⇑χ) := by
  rw [coe_rootSystem_reflection_apply]
  exact finrank_weightSpace_sub_apply_coroot_smul (LieSubalgebra.isNonZero_coe_root i) _

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
Killing-semisimple Lie algebra, the function `χ ↦ dim Mχ` on the weight space `Module.Dual K H` is
invariant under the Weyl group of the root system of `H`.

This is the direct, rank-one proof: it descends through
`TauCeti.finrank_weightSpace_sub_apply_coroot_smul` to the `sl₂` triple attached to each root, and
so is available before — and independently of — Weyl's complete reducibility theorem. -/
@[simp] theorem finrank_weightSpace_weylGroup_smul
    (w : (IsKilling.rootSystem H).weylGroup) (χ : Dual K H) :
    finrank K (weightSpace M ⇑(w • χ)) = finrank K (weightSpace M ⇑χ) :=
  finrank_weightSpace_weylGroup_smul_of_mem w.property χ

end Killing

end TauCeti
