/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Spectrum
public import TauCeti.Algebra.Lie.Sl2.WeightMultiplicity
public import TauCeti.Algebra.Lie.Submodule.LocallyFinite
public import TauCeti.LinearAlgebra.Eigenspace.Semisimple
public import TauCeti.LinearAlgebra.Eigenspace.Separation
public import Mathlib.Algebra.Lie.Weights.Killing

public section

/-!
# The weights of an integrable module are stable under the root reflections

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, let `H` be a Cartan subalgebra and let `α` be a root. A module
`M` is **integrable along `α`** when every vector of `M` lies in a finitely generated subspace
stable under the `sl₂` triple of `α`, that is when
`TauCeti.locallyFiniteSubmodule K M (t.toLieSubalgebra K) = ⊤` for such a triple `t`. This file
proves that the weights of an integrable module are stable under the reflection `s_α`.

`M` is **not** assumed finite-dimensional, and that is the point. For a finite-dimensional module
`TauCeti/Algebra/Lie/Weights/WeylInvariance.lean` already proves the stronger statement that the
reflections preserve the weight *multiplicities*. But the modules Layer 4 of the highest weight
roadmap has to bound are the irreducible highest weight modules `L(λ)`, whose
finite-dimensionality is the thing to be proved; what is available for them beforehand is
integrability (`TauCeti/Algebra/Lie/HighestWeight/Integrable.lean`). Reflection stability of the
weight support, together with the weight cone `λ - Q⁺`, is what confines those weights to a finite
set.

## The argument

Fix a weight `χ` of `M`, a nonzero vector `v` of `M_χ`, and a finitely generated subspace `N`
containing `v` and stable under the `sl₂` triple of `α`. The subspace

`W = ⨆ k : ℤ, (M_{k α + χ} ⊓ N)`

is a finite-dimensional module over that triple: the raising and lowering vectors move
`M_{k α + χ}` to `M_{(k ± 1) α + χ}` and preserve `N`, while `W ≤ N` is finite-dimensional because
`N` is. So the rank-one theory applies to `W`, in two ways.

* The Cartan element `α^∨` acts diagonalizably on a finite-dimensional module over an `sl₂` triple
  (`TauCeti.iSup_eigenspace_toEnd_eq_top`), with integer eigenvalues
  (`TauCeti.exists_int_of_hasEigenvalue`). Diagonalizable endomorphisms are semisimple
  (`TauCeti.isSemisimple_of_iSup_eigenspace_eq_top`), so the generalized eigenvectors lying in `W`
  are honest eigenvectors, and `χ (α^∨) = m` is an integer.
* Its eigenspaces at opposite eigenvalues have equal dimension
  (`TauCeti.finrank_eigenspace_toEnd_neg`). The eigenvalue `m` is attained, by `v`, so `-m` is
  attained too.

An eigenvector for `-m` inside `W` has to lie in the summand `M_{-m α + χ} ⊓ N`, because `α^∨` acts
on the summand `M_{k α + χ} ⊓ N` by `2 k + m` and these scalars are distinct
(`TauCeti.biSup_inf_eigenspace_eq_self`). That summand is therefore nonzero, and
`-m α + χ = χ - χ(α^∨) α` is the reflection of `χ`.

## Main results

* `TauCeti.exists_int_apply_coroot_of_genWeightSpace_ne_bot`: a weight of a module integrable along
  `α` takes an integer value on the coroot `α^∨`, so the reflection statement below needs no
  integrality hypothesis.
* `TauCeti.genWeightSpace_sub_apply_coroot_smul_ne_bot`: **the weights of a module integrable along
  `α` are stable under the reflection `s_α`**, and
  `TauCeti.genWeightSpace_sub_apply_coroot_smul_eq_bot_iff` records the resulting equivalence, the
  reflection being an involution.

## References

This is the weight-stability half of the "weight-cone bound" milestone of Layer 4, "the
classification of finite-dimensional irreducibles", of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §21.2.
* V. G. Kac, *Infinite Dimensional Lie Algebras*, 3rd ed., §3.6.
-/

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w

/-! ### Reflection stability of the weights of an integrable module -/

section Killing

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  {α : Weight K H L} {χ : H → K} {h e f : L}

/-- Both statements of this file at once: for a module integrable along a nonzero root `α`, the
value of a weight `χ` on the coroot `α^∨` is an integer `m`, and `-m • α + χ` is again a weight.

The two are proved together because both come out of the same finite-dimensional module over the
`sl₂` triple of `α`, cut out of `M` by the `α`-string of `χ` and a finitely generated stable
subspace. -/
private theorem exists_int_apply_coroot_and_genWeightSpace_zsmul_add_ne_bot (hα : α.IsNonZero)
    (t : IsSl2Triple h e f) (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α))
    (hlf : locallyFiniteSubmodule K M (t.toLieSubalgebra K : Set L) = ⊤)
    (hχ : genWeightSpace M χ ≠ ⊥) :
    ∃ m : ℤ, χ (IsKilling.coroot α) = (m : K) ∧
      genWeightSpace M ((-m : ℤ) • ⇑α + χ) ≠ ⊥ := by
  classical
  have hh : h = (IsKilling.coroot α : L) := t.h_eq_coroot hα he hf
  -- a nonzero vector of the weight space, and a finitely generated stable subspace around it
  obtain ⟨v, hvmem, hv0⟩ := (Submodule.ne_bot_iff _).1
    (fun hbot ↦ hχ (by rwa [← LieSubmodule.toSubmodule_eq_bot]))
  have hvlf : v ∈ locallyFiniteSubmodule K M (t.toLieSubalgebra K : Set L) := by
    rw [hlf]; trivial
  obtain ⟨N, hNfg, hNst, hvN⟩ := mem_locallyFiniteSubmodule.1 hvlf
  -- the `α`-string of `χ`, truncated to `N`
  set A : Module.End K M := toEnd K H M (IsKilling.coroot α) with hAdef
  set n : K := χ (IsKilling.coroot α) with hndef
  set g : ℤ → K := fun k ↦ n + 2 * k with hgdef
  set P : ℤ → Submodule K M := fun k ↦ (genWeightSpace M (k • ⇑α + χ)).toSubmodule ⊓ N with hPdef
  set W : Submodule K M := ⨆ k : ℤ, P k with hWdef
  have hWN : W ≤ N := iSup_le fun _ ↦ inf_le_right
  have hvW : v ∈ W := le_iSup P 0 ⟨by simpa using hvmem, hvN⟩
  -- a root vector shifts the string by its own root and preserves `N`, hence preserves `W`
  have hshift : ∀ (x : L) (β : H → K), x ∈ rootSpace H β → x ∈ (t.toLieSubalgebra K : Set L) →
      (∀ k : ℤ, ∃ j : ℤ, β + (k • ⇑α + χ) = j • ⇑α + χ) → ∀ u ∈ W, ⁅x, u⁆ ∈ W := by
    intro x β hx hxt hjump u hu
    have hle : W ≤ W.comap (toEnd K L M x) := by
      rw [hWdef]
      refine iSup_le fun k w hw ↦ ?_
      obtain ⟨j, hj⟩ := hjump k
      have hmapped := mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H M β
        (k • ⇑α + χ) hx hw.1
      rw [hj] at hmapped
      exact le_iSup P j ⟨hmapped, hNst x hxt w hw.2⟩
    simpa using hle hu
  have hWe : ∀ u ∈ W, ⁅e, u⁆ ∈ W :=
    hshift e ⇑α he t.e_mem_toLieSubalgebra fun k ↦ ⟨k + 1, by rw [add_zsmul, one_zsmul]; abel⟩
  have hWf : ∀ u ∈ W, ⁅f, u⁆ ∈ W :=
    hshift f (-⇑α) hf t.f_mem_toLieSubalgebra fun k ↦ ⟨k - 1, by rw [sub_zsmul, one_zsmul]; abel⟩
  -- `W` as a finite-dimensional module over the subalgebra generated by the triple
  set 𝒲 : LieSubmodule K (t.toLieSubalgebra K) M := t.lieSubmoduleOfStable W hWe hWf with h𝒲def
  have h𝒲W : 𝒲.toSubmodule = W := t.lieSubmoduleOfStable_toSubmodule W hWe hWf
  have hmem𝒲 : ∀ {u : M}, u ∈ 𝒲 ↔ u ∈ W := by
    intro u; rw [← LieSubmodule.mem_toSubmodule, h𝒲W]
  have : FiniteDimensional K N := (Submodule.fg_iff_finiteDimensional N).1 hNfg
  -- `LieSubmodule.mem_toSubmodule` is definitional, so the two subtypes below are the same type.
  have : FiniteDimensional K 𝒲 := by
    have : FiniteDimensional K (𝒲.toSubmodule : Submodule K M) := by
      rw [h𝒲W]; exact Submodule.finiteDimensional_of_le hWN
    exact this
  -- the action of the Cartan element of the triple on `𝒲`, and its comparison with `A`
  set B : Module.End K 𝒲 :=
    toEnd K (t.toLieSubalgebra K) 𝒲 ⟨h, t.h_mem_toLieSubalgebra⟩ with hBdef
  have hcoeB : ∀ u : 𝒲, ((B u : 𝒲) : M) = A (u : M) := by
    intro u
    simp only [hBdef, hAdef, toEnd_apply_apply, LieSubmodule.coe_bracket,
      LieSubalgebra.coe_bracket_of_module, hh]
  have hcoeStep : ∀ (c : K) (u : 𝒲), (((B - c • 1) u : 𝒲) : M) = (A - c • 1) (u : M) := by
    intro c u
    simp [hcoeB]
  have hcoePow : ∀ (c : K) (k : ℕ) (u : 𝒲),
      ((((B - c • 1) ^ k) u : 𝒲) : M) = ((A - c • 1) ^ k) (u : M) := by
    intro c k
    induction k with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hcoeStep]
  -- generalized eigenvectors of `A` inside `W` are honest eigenvectors of `A`
  have hdiag : ⨆ c : K, B.eigenspace c = ⊤ :=
    iSup_eigenspace_toEnd_eq_top (M := 𝒲) t.isSl2Triple_restrict
  have hss : B.IsFinitelySemisimple :=
    (isSemisimple_of_iSup_eigenspace_eq_top hdiag).isFinitelySemisimple
  have hhonest : ∀ (c : K) (u : M) (hu : u ∈ W), u ∈ A.maxGenEigenspace c → A u = c • u := by
    intro c u hu hgen
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hgen
    have hmem : (⟨u, hmem𝒲.2 hu⟩ : 𝒲) ∈ B.maxGenEigenspace c :=
      (Module.End.mem_maxGenEigenspace _ _ _).2
        ⟨k, Subtype.ext (by rw [hcoePow c k]; simpa using hk)⟩
    rw [hss.maxGenEigenspace_eq_eigenspace c, Module.End.mem_eigenspace_iff] at hmem
    have := congrArg (fun w : 𝒲 ↦ (w : M)) hmem
    simpa [hcoeB] using this
  -- the coroot acts on the `k`-th summand of the string by `2 k + n`
  have hval : ∀ k : ℤ, (k • ⇑α + χ) (IsKilling.coroot α) = g k := by
    intro k
    simp only [hgdef, hndef, Pi.add_apply, Pi.smul_apply, IsKilling.root_apply_coroot hα]
    push_cast [zsmul_eq_mul]
    ring
  have hPeig : ∀ k : ℤ, P k ≤ A.eigenspace (g k) := by
    intro k u hu
    have hgen : u ∈ A.maxGenEigenspace (g k) := by
      obtain ⟨j, hj⟩ := (mem_genWeightSpace M (k • ⇑α + χ) u).1 hu.1 (IsKilling.coroot α)
      exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨j, by rwa [hval k] at hj⟩
    exact Module.End.mem_eigenspace_iff.2 (hhonest _ u (le_iSup P k hu) hgen)
  -- the eigenvalue `n` is attained on `𝒲`, hence so is `-n`
  have hvB : (⟨v, hmem𝒲.2 hvW⟩ : 𝒲) ∈ B.eigenspace n := by
    refine Module.End.mem_eigenspace_iff.2 (Subtype.ext ?_)
    rw [hcoeB]
    have := Module.End.mem_eigenspace_iff.1 (hPeig 0 ⟨by simpa using hvmem, hvN⟩)
    simpa [hgdef] using this
  have hnB : B.eigenspace n ≠ ⊥ := fun hbot ↦ hv0 (by
    have := (Submodule.eq_bot_iff _).1 hbot _ hvB
    simpa [Subtype.ext_iff] using this)
  obtain ⟨m, hm⟩ := exists_int_of_hasEigenvalue (M := 𝒲) t.isSl2Triple_restrict
    (Module.End.hasEigenvalue_iff.2 hnB)
  have hsym := finrank_eigenspace_toEnd_neg (L := ↥(t.toLieSubalgebra K)) (M := 𝒲)
    t.isSl2Triple_restrict n
  have hnegB : B.eigenspace (-n) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hsym
    exact hnB (Submodule.finrank_eq_zero.1 hsym)
  obtain ⟨u, humem, hu0⟩ := (Submodule.ne_bot_iff _).1 hnegB
  -- an eigenvector of eigenvalue `-n` lies in the `(-m)`-th summand of the string
  have hginj : Function.Injective g := by
    intro k k' hkk'
    have : (2 : K) * k = 2 * k' := by
      simpa only [hgdef, add_right_inj] using hkk'
    exact_mod_cast mul_left_cancel₀ (two_ne_zero (α := K)) this
  have hgm : g (-m) = -n := by
    rw [hgdef, hm]
    push_cast
    ring
  have huA : A (u : M) = g (-m) • (u : M) := by
    have := congrArg (fun w : 𝒲 ↦ (w : M)) (Module.End.mem_eigenspace_iff.1 humem)
    rw [hgm]
    simpa [hcoeB] using this
  have huP : (u : M) ∈ P (-m) := by
    have hloc := biSup_inf_eigenspace_eq_self (s := (Set.univ : Set ℤ)) A P g
      (fun j _ ↦ hPeig j) (Set.mem_univ (-m)) fun j _ hj hcon ↦ hj (hginj hcon)
    rw [← hloc]
    refine ⟨?_, Module.End.mem_eigenspace_iff.2 huA⟩
    have huW : (u : M) ∈ W := hmem𝒲.1 u.2
    simpa [hWdef] using huW
  refine ⟨m, hm, fun hbot ↦ hu0 (Subtype.ext ?_)⟩
  have : (u : M) ∈ (genWeightSpace M ((-m : ℤ) • ⇑α + χ)).toSubmodule := huP.1
  rw [hbot] at this
  simpa using this

/-- **A weight of an integrable module is integral on the coroot.** If a module `M` is integrable
along a nonzero root `α`, in the sense that every vector lies in a finitely generated subspace
stable under an `sl₂` triple `(h, e, f)` of `α`, then every weight `χ` of `M` takes an integer
value on the coroot `α^∨`.

This is the rank-one integrality statement for a module that is not assumed finite-dimensional:
the string of `χ` truncated to a stable finitely generated subspace is a finite-dimensional module
over the triple, and `TauCeti.exists_int_of_hasEigenvalue` applies to it. For a finite-dimensional
module `TauCeti.exists_int_apply_coroot` says the same with no integrability hypothesis. -/
theorem exists_int_apply_coroot_of_genWeightSpace_ne_bot (hα : α.IsNonZero)
    (t : IsSl2Triple h e f) (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α))
    (hlf : locallyFiniteSubmodule K M (t.toLieSubalgebra K : Set L) = ⊤)
    (hχ : genWeightSpace M χ ≠ ⊥) :
    ∃ m : ℤ, χ (IsKilling.coroot α) = (m : K) := by
  obtain ⟨m, hm, -⟩ :=
    exists_int_apply_coroot_and_genWeightSpace_zsmul_add_ne_bot hα t he hf hlf hχ
  exact ⟨m, hm⟩

/-- **The weights of an integrable module are stable under the root reflections.** Let `α` be a
nonzero root with `sl₂` triple `(h, e, f)`, and let `M` be a module integrable along `α`: every
vector of `M` lies in a finitely generated subspace stable under the triple. Then the reflection
`s_α χ = χ - χ(α^∨) α` of a weight of `M` is again a weight of `M`.

`M` is not assumed finite-dimensional. For a finite-dimensional module
`TauCeti.finrank_weightSpace_sub_apply_coroot_smul` gives the stronger conclusion that the
reflection preserves the multiplicity. -/
theorem genWeightSpace_sub_apply_coroot_smul_ne_bot (hα : α.IsNonZero) (t : IsSl2Triple h e f)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α))
    (hlf : locallyFiniteSubmodule K M (t.toLieSubalgebra K : Set L) = ⊤)
    (hχ : genWeightSpace M χ ≠ ⊥) :
    genWeightSpace M (χ - χ (IsKilling.coroot α) • ⇑α) ≠ ⊥ := by
  obtain ⟨m, hm, hne⟩ :=
    exists_int_apply_coroot_and_genWeightSpace_zsmul_add_ne_bot hα t he hf hlf hχ
  have hrewrite : χ - χ (IsKilling.coroot α) • ⇑α = (-m : ℤ) • ⇑α + χ := by
    rw [hm, ← Int.cast_smul_eq_zsmul K (-m) (⇑α : H → K)]
    push_cast
    module
  rwa [hrewrite]

/-- **The weights of an integrable module are exactly the reflections of its weights.** With the
hypotheses of `TauCeti.genWeightSpace_sub_apply_coroot_smul_ne_bot`, a form `χ` on the Cartan
subalgebra is a weight of `M` exactly when its reflection `s_α χ` is: the reflection is an
involution, so the forward implication applies in both directions. -/
theorem genWeightSpace_sub_apply_coroot_smul_eq_bot_iff (hα : α.IsNonZero) (t : IsSl2Triple h e f)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α))
    (hlf : locallyFiniteSubmodule K M (t.toLieSubalgebra K : Set L) = ⊤) :
    genWeightSpace M (χ - χ (IsKilling.coroot α) • ⇑α) = ⊥ ↔ genWeightSpace M χ = ⊥ := by
  set ψ : H → K := χ - χ (IsKilling.coroot α) • ⇑α with hψdef
  have hψval : ψ (IsKilling.coroot α) = -χ (IsKilling.coroot α) := by
    simp only [hψdef, Pi.sub_apply, Pi.smul_apply, IsKilling.root_apply_coroot hα, smul_eq_mul]
    ring
  have hinv : ψ - ψ (IsKilling.coroot α) • ⇑α = χ := by
    rw [hψval, hψdef]
    module
  refine not_iff_not.1 ⟨fun hψ ↦ ?_, fun hχ ↦ ?_⟩
  · have := genWeightSpace_sub_apply_coroot_smul_ne_bot (χ := ψ) hα t he hf hlf hψ
    rwa [hinv] at this
  · exact genWeightSpace_sub_apply_coroot_smul_ne_bot hα t he hf hlf hχ

end Killing

end TauCeti
