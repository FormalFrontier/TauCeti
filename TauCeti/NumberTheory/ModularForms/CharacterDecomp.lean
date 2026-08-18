/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
public import TauCeti.NumberTheory.ModularForms.DiamondOperators

/-!
# Character decomposition of modular forms for `Γ₁(N)`

For each character `χ : (ZMod N)ˣ →* ℂˣ`, the nebentypus character space
`modFormCharSpace k χ` and its cusp-form analogue `cuspFormCharSpace k χ` are cut out in
`TauCeti/NumberTheory/ModularForms/DiamondOperators.lean` as simultaneous
diamond-eigenspaces. This file proves the internal direct sum decomposition

  `M_k(Γ₁(N)) = ⨁_{χ} M_k(Γ₁(N), χ)`

together with its cusp-form analogues and the refinement to diamond-invariant
submodules, by simultaneous diagonalization of the commuting finite-order diamond
operators (`TauCeti/LinearAlgebra/Eigenspace/JointEigenvector/Basic.lean`).

Beyond the standing `N ≠ 0` hypothesis (`[NeZero N]`, a section variable that most
declarations here need, the independence statements being the exception), the statements are
unconditional: the diamond group `(ZMod N)ˣ` is finite and
commutative, so the classical character projectors decompose every vector
(`iSup_iInf_eigenspace_unitHom_eq_top_of_commGroup`), with no finite-dimensionality
hypotheses anywhere — matching the roadmap's canonical statement.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/CharacterDecomp.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), realizing
Layer 0 of the ModularForms roadmap.

## Main results

* `iSup_modFormCharSpace_eq_top`, `iSup_cuspFormCharSpace_eq_top`: the character spaces
  span `M_k(Γ₁(N))` resp. `S_k(Γ₁(N))`.
* `iSupIndep_modFormCharSpace`, `iSupIndep_cuspFormCharSpace`: the families are
  supremum-independent.
* `isInternal_modFormCharSpace`, `isInternal_cuspFormCharSpace`: the `DirectSum.IsInternal`
  statements.
* `iSup_inf_modFormCharSpace_of_invariant`, `iSup_inf_cuspFormCharSpace_of_invariant`:
  any diamond-invariant submodule is the supremum of its intersections with the
  character spaces, with finsupp-indexed corollaries
  `exists_finsupp_of_diamondOp_invariant`/`exists_finsupp_of_diamondOpCusp_invariant`.
* `linearMap_ext_of_mem_modFormCharSpace`, `linearMap_ext_of_mem_cuspFormCharSpace`: two
  endomorphisms agreeing on every character space are equal — the gluing principle for
  extending Hecke-operator identities proven per character space to the whole space.

## References

* Diamond–Shurman, *A first course in modular forms*, §5.2
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups DirectSum

noncomputable section

variable {N : ℕ} [NeZero N] {k : ℤ}

private instance : NeZero ((Nat.card (ZMod N)ˣ : ℂ)) :=
  ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

private instance : NeZero (Monoid.exponent (ZMod N)ˣ) :=
  ⟨Monoid.exponent_ne_zero_of_finite⟩

private instance : NeZero ((Monoid.exponent (ZMod N)ˣ : ℂ)) :=
  ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩

private lemma isUnit_card_unitsZMod :
    IsUnit ((Nat.card ((ZMod N)ˣ) : ℂ)) :=
  isUnit_iff_ne_zero.mpr (NeZero.ne _)

/-- **Character decomposition of a diamond-invariant submodule of `M_k(Γ₁(N))`.**
If `p ⊆ M_k(Γ₁(N))` is stable under every diamond operator `⟨d⟩` for
`d ∈ (ZMod N)ˣ`, then `p` equals the supremum of its intersections with the
nebentypus character subspaces `modFormCharSpace k χ`. Specializing `p = ⊤`
recovers `iSup_modFormCharSpace_eq_top`. -/
theorem iSup_inf_modFormCharSpace_of_invariant
    (k : ℤ) (p : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpHom k d f ∈ p) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, p ⊓ modFormCharSpace k χ) = p := by
  have h : (⨆ χ₀ : (ZMod N)ˣ →* ℂˣ,
      p ⊓ ⨅ d : (ZMod N)ˣ, (diamondOpHom k d).eigenspace ((χ₀ d : ℂ))) = p :=
    iSup_inf_iInf_eigenspace_unitHom_of_invariant_of_commGroup
      isUnit_card_unitsZMod p hp
  simpa only [modFormCharSpace_def] using h

/-- **Character decomposition of a diamond-invariant submodule of `S_k(Γ₁(N))`.**
The cusp-form analogue of `iSup_inf_modFormCharSpace_of_invariant`. -/
theorem iSup_inf_cuspFormCharSpace_of_invariant
    (k : ℤ) (p : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpCuspHom k d f ∈ p) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, p ⊓ cuspFormCharSpace k χ) = p := by
  have h : (⨆ χ₀ : (ZMod N)ˣ →* ℂˣ,
      p ⊓ ⨅ d : (ZMod N)ˣ, (diamondOpCuspHom k d).eigenspace ((χ₀ d : ℂ))) = p :=
    iSup_inf_iInf_eigenspace_unitHom_of_invariant_of_commGroup
      isUnit_card_unitsZMod p hp
  simpa only [cuspFormCharSpace_def] using h

/-- **The character subspaces `modFormCharSpace k χ` span the whole space**:
modular forms for `Γ₁(N)` decompose into the span of nebentypus character
spaces, one for each character `(ZMod N)ˣ →* ℂˣ`. -/
@[simp]
theorem iSup_modFormCharSpace_eq_top (k : ℤ) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, modFormCharSpace k χ) =
    (⊤ : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  simpa only [top_inf_eq] using
    iSup_inf_modFormCharSpace_of_invariant k ⊤ fun _ _ _ ↦ Submodule.mem_top

omit [NeZero N] in
/-- **The character subspaces form an independent family.** -/
theorem iSupIndep_modFormCharSpace (k : ℤ) :
    iSupIndep (fun χ : (ZMod N)ˣ →* ℂˣ ↦ modFormCharSpace (N := N) k χ) := by
  have h : iSupIndep (fun χ₀ : (ZMod N)ˣ →* ℂˣ ↦
      ⨅ d : (ZMod N)ˣ, (diamondOpHom k d).eigenspace ((χ₀ d : ℂ))) :=
    iSupIndep_iInf_eigenspace_unitHom (ρ := diamondOpHom k)
  simpa only [modFormCharSpace_def] using h

/-- **Internal direct sum decomposition**: `M_k(Γ₁(N))` decomposes as the direct
sum of the nebentypus character spaces `modFormCharSpace k χ`. -/
theorem isInternal_modFormCharSpace (k : ℤ) [DecidableEq ((ZMod N)ˣ →* ℂˣ)] :
    DirectSum.IsInternal (fun χ : (ZMod N)ˣ →* ℂˣ ↦ modFormCharSpace k χ) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_modFormCharSpace k) (iSup_modFormCharSpace_eq_top k)

omit [NeZero N] in
/-- **The cusp-form character subspaces form an independent family.** -/
theorem iSupIndep_cuspFormCharSpace (k : ℤ) :
    iSupIndep (fun χ : (ZMod N)ˣ →* ℂˣ ↦ cuspFormCharSpace (N := N) k χ) := by
  have h : iSupIndep (fun χ₀ : (ZMod N)ˣ →* ℂˣ ↦
      ⨅ d : (ZMod N)ˣ, (diamondOpCuspHom k d).eigenspace ((χ₀ d : ℂ))) :=
    iSupIndep_iInf_eigenspace_unitHom (ρ := diamondOpCuspHom k)
  simpa only [cuspFormCharSpace_def] using h

/-- **The cusp-form character subspaces span the whole space.** -/
@[simp]
theorem iSup_cuspFormCharSpace_eq_top (k : ℤ) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, cuspFormCharSpace k χ) =
    (⊤ : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  simpa only [top_inf_eq] using
    iSup_inf_cuspFormCharSpace_of_invariant k ⊤ fun _ _ _ ↦ Submodule.mem_top

/-- **Internal direct sum decomposition of cusp forms**: `S_k(Γ₁(N))` decomposes as the
direct sum of the nebentypus character spaces `cuspFormCharSpace k χ`. -/
theorem isInternal_cuspFormCharSpace (k : ℤ) [DecidableEq ((ZMod N)ˣ →* ℂˣ)] :
    DirectSum.IsInternal (fun χ : (ZMod N)ˣ →* ℂˣ ↦ cuspFormCharSpace k χ) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_cuspFormCharSpace k) (iSup_cuspFormCharSpace_eq_top k)

section InvariantSubmodule

/-- **Finsupp-indexed character decomposition of a modular form in a
diamond-invariant submodule.** Consumer-facing corollary of
`iSup_inf_modFormCharSpace_of_invariant`: any element of a diamond-invariant
submodule `p ⊆ M_k(Γ₁(N))` is a finitely-supported sum of nebentypus-character
components, each landing simultaneously in `p` and in its character subspace. -/
theorem exists_finsupp_of_diamondOp_invariant
    (k : ℤ) (p : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpHom k d f ∈ p)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ p) :
    ∃ g : ((ZMod N)ˣ →* ℂˣ) →₀ ModularForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ χ : (ZMod N)ˣ →* ℂˣ, g χ ∈ p ⊓ modFormCharSpace k χ) ∧
        (g.sum fun _ y ↦ y) = f :=
  (Submodule.mem_iSup_iff_exists_finsupp _ _).mp <|
    (iSup_inf_modFormCharSpace_of_invariant k p hp).symm ▸ hf

/-- **Finsupp-indexed character decomposition of a cusp form in a
diamond-invariant submodule.** Cusp-form analogue of
`exists_finsupp_of_diamondOp_invariant`. -/
theorem exists_finsupp_of_diamondOpCusp_invariant
    (k : ℤ) (p : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpCuspHom k d f ∈ p)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ p) :
    ∃ g : ((ZMod N)ˣ →* ℂˣ) →₀ CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ χ : (ZMod N)ˣ →* ℂˣ, g χ ∈ p ⊓ cuspFormCharSpace k χ) ∧
        (g.sum fun _ y ↦ y) = f :=
  (Submodule.mem_iSup_iff_exists_finsupp _ _).mp <|
    (iSup_inf_cuspFormCharSpace_of_invariant k p hp).symm ▸ hf

end InvariantSubmodule

/-- **Extensionality along the character decomposition**: two `ℂ`-linear maps out of
`M_k(Γ₁(N))` that agree on every nebentypus subspace `modFormCharSpace k χ` are equal.
This is the gluing principle by which identities of Hecke operators proven per character
space extend to the whole space of modular forms. -/
theorem linearMap_ext_of_mem_modFormCharSpace
    {W : Type*} [AddCommMonoid W] [Module ℂ W]
    {S T : (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) →ₗ[ℂ] W}
    (h : ∀ (χ : (ZMod N)ˣ →* ℂˣ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      f ∈ modFormCharSpace k χ → S f = T f) : S = T := by
  refine LinearMap.ext fun f ↦ ?_
  have hf : f ∈ ⨆ χ : (ZMod N)ˣ →* ℂˣ, modFormCharSpace k χ :=
    iSup_modFormCharSpace_eq_top (N := N) k ▸ Submodule.mem_top
  exact Submodule.iSup_induction _ (motive := fun g ↦ S g = T g) hf h (by simp only [map_zero])
    fun x y hx hy ↦ by simp only [map_add, hx, hy]

/-- **Extensionality along the cusp-form character decomposition**: two `ℂ`-linear maps out of
`S_k(Γ₁(N))` that agree on every nebentypus subspace
`cuspFormCharSpace k χ` are equal. -/
theorem linearMap_ext_of_mem_cuspFormCharSpace
    {W : Type*} [AddCommMonoid W] [Module ℂ W]
    {S T : (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) →ₗ[ℂ] W}
    (h : ∀ (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      f ∈ cuspFormCharSpace k χ → S f = T f) : S = T := by
  refine LinearMap.ext fun f ↦ ?_
  have hf : f ∈ ⨆ χ : (ZMod N)ˣ →* ℂˣ, cuspFormCharSpace k χ :=
    iSup_cuspFormCharSpace_eq_top (N := N) k ▸ Submodule.mem_top
  exact Submodule.iSup_induction _ (motive := fun g ↦ S g = T g) hf h (by simp only [map_zero])
    fun x y hx hy ↦ by simp only [map_add, hx, hy]

end
