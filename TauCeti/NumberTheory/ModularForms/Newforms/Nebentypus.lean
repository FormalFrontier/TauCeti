/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CharacterDecomp
public import TauCeti.NumberTheory.ModularForms.Newforms.Basic
public import TauCeti.NumberTheory.ModularForms.Petersson.Unitary

/-!
# The old and new subspaces at a fixed nebentypus

The old subspace `S_k(Γ₁(N))ᵒˡᵈ` and its Petersson-orthogonal complement, the new subspace
`S_k(Γ₁(N))ⁿᵉʷ` (`TauCeti/NumberTheory/ModularForms/Newforms/Basic.lean`), are both stable under
the diamond operators: the old one because the level-raising maps intertwine the diamonds, the
new one because the diamonds are Petersson-unitary
(`TauCeti/NumberTheory/ModularForms/Petersson/Unitary.lean`). Both therefore decompose along the
nebentypus character spaces `S_k(N, χ) = cuspFormCharSpace k χ`, and this file records what that
decomposition says about newness.

The main statement is the *refinement at a fixed nebentypus*: for a cusp form `f ∈ S_k(N, χ)`,
being new is orthogonality to the old forms **of the same nebentypus** alone,

`f ∈ S_k(Γ₁(N))ⁿᵉʷ ↔ f ⊥ (S_k(Γ₁(N))ᵒˡᵈ ⊓ S_k(N, χ))`,

because old forms of a different nebentypus are automatically orthogonal to `f`. Equivalently,
in the form Layer 3 of the ModularForms roadmap asks for, the new subspace of `S_k(N, χ)` —
the orthogonal complement, taken inside `S_k(N, χ)`, of the old forms there — is
`S_k(Γ₁(N))ⁿᵉʷ ⊓ S_k(N, χ)`: newness may be read at level `Γ₁(N)` and then intersected. The
old/new decomposition then restricts to each nebentypus space,
`S_k(N, χ) = S_k(N, χ)ᵒˡᵈ ⊕ S_k(N, χ)ⁿᵉʷ`.

What is *not* proved here is the roadmap's explicit description of the old part of `S_k(N, χ)`
as `Σ_{M ∣ N, cond χ ∣ M} Σ_{d ∣ N/M} V_d S_k(M, χ_M)`; that identification of
`S_k(Γ₁(N))ᵒˡᵈ ⊓ S_k(N, χ)` needs the descent of `χ` to the divisor levels, and the conductor
theory it rests on.

## Main results

* `TauCeti.diamondOpCusp_mem_cuspFormsNew`: the new subspace is diamond-stable.
* `TauCeti.iSup_inf_cuspFormsOld_cuspFormCharSpace`,
  `TauCeti.iSup_inf_cuspFormsNew_cuspFormCharSpace`: the old and the new subspace are each the
  supremum of their nebentypus components.
* `TauCeti.mem_cuspFormsNew_iff_of_mem_cuspFormCharSpace`: a form of nebentypus `χ` is new
  exactly when it is orthogonal to the old forms of nebentypus `χ`.
* `TauCeti.cuspFormsNew_inf_cuspFormCharSpace`: `S_k(N, χ)ⁿᵉʷ = S_k(Γ₁(N))ⁿᵉʷ ⊓ S_k(N, χ)`.
* `TauCeti.sup_cuspFormsOld_cuspFormsNew_inf_cuspFormCharSpace` and
  `TauCeti.disjoint_cuspFormsOld_cuspFormsNew_inf_cuspFormCharSpace`: the old/new decomposition
  of `S_k(N, χ)`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Section 5.6.
* Miyake, *Modular forms*, Section 4.6.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

open _root_.CuspForm

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-! ### Diamond stability of the new subspace -/

/-- **The new subspace is diamond-stable.** The old subspace is carried onto itself by `⟨u⟩`,
and `⟨u⟩` is Petersson-unitary, so it preserves the orthogonal complement as well. -/
theorem diamondOpCusp_mem_cuspFormsNew (u : (ZMod N)ˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsNew N k) :
    diamondOpCusp k u f ∈ cuspFormsNew N k := by
  rw [cuspFormsNew_def] at hf ⊢
  exact CuspForm.diamondOpCusp_mem_peterssonOrthogonal
    (fun _ _ hg ↦ diamondOpCusp_mem_cuspFormsOld _ hg) u hf

/-! ### The nebentypus components of the old and new subspaces -/

/-- **The old subspace is the sum of its nebentypus components.** -/
theorem iSup_inf_cuspFormsOld_cuspFormCharSpace (N : ℕ) [NeZero N] (k : ℤ) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, cuspFormsOld N k ⊓ cuspFormCharSpace k χ) = cuspFormsOld N k :=
  iSup_inf_cuspFormCharSpace_of_invariant k _ fun _ _ hf ↦ by
    rw [diamondOpCuspHom_apply]; exact diamondOpCusp_mem_cuspFormsOld _ hf

/-- **The new subspace is the sum of its nebentypus components.** -/
theorem iSup_inf_cuspFormsNew_cuspFormCharSpace (N : ℕ) [NeZero N] (k : ℤ) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, cuspFormsNew N k ⊓ cuspFormCharSpace k χ) = cuspFormsNew N k :=
  iSup_inf_cuspFormCharSpace_of_invariant k _ fun _ _ hf ↦ by
    rw [diamondOpCuspHom_apply]; exact diamondOpCusp_mem_cuspFormsNew _ hf

/-! ### Newness at a fixed nebentypus -/

/-- **Newness is tested against the old forms of the same nebentypus.** A cusp form of
nebentypus `χ` is new exactly when it is Petersson-orthogonal to the old forms of nebentypus
`χ`: the old subspace is the sum of its nebentypus components, and the components with
`ψ ≠ χ` are orthogonal to `f` for free, the nebentypus decomposition being an orthogonal one. -/
theorem mem_cuspFormsNew_iff_of_mem_cuspFormCharSpace
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    f ∈ cuspFormsNew N k ↔
      f ∈ CuspForm.peterssonOrthogonal (cuspFormsOld N k ⊓ cuspFormCharSpace k χ) := by
  have hold : CuspForm.peterssonOrthogonal (cuspFormsOld N k) =
      ⨅ ψ : (ZMod N)ˣ →* ℂˣ,
        CuspForm.peterssonOrthogonal (cuspFormsOld N k ⊓ cuspFormCharSpace k ψ) := by
    rw [← CuspForm.peterssonOrthogonal_iSup, iSup_inf_cuspFormsOld_cuspFormCharSpace]
  rw [cuspFormsNew_def, hold, Submodule.mem_iInf]
  refine ⟨fun h ↦ h χ, fun h ψ ↦ ?_⟩
  rcases eq_or_ne ψ χ with rfl | hψ
  · exact h
  · exact CuspForm.mem_peterssonOrthogonal_iff.mpr fun g hg ↦
      CuspForm.peterssonInnerCosets_eq_zero_of_mem_cuspFormCharSpace_of_ne hψ hg.2 hf

/-- **The new subspace of `S_k(N, χ)`.** The orthogonal complement of the old forms of
nebentypus `χ`, taken inside `S_k(N, χ)`, is what one gets by intersecting the new subspace of
`S_k(Γ₁(N))` with `S_k(N, χ)`: newness may be read at level `Γ₁(N)` and then restricted to a
nebentypus. This is the milestone `S_k(N, χ)ⁿᵉʷ = S_k(Γ₁(N))ⁿᵉʷ ⊓ S_k(N, χ)` of Layer 3 of the
ModularForms roadmap. -/
theorem cuspFormsNew_inf_cuspFormCharSpace (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    cuspFormsNew N k ⊓ cuspFormCharSpace k χ =
      CuspForm.peterssonOrthogonal (cuspFormsOld N k ⊓ cuspFormCharSpace k χ) ⊓
        cuspFormCharSpace k χ := by
  ext f
  simp only [Submodule.mem_inf]
  exact ⟨fun h ↦ ⟨(mem_cuspFormsNew_iff_of_mem_cuspFormCharSpace h.2).mp h.1, h.2⟩,
    fun h ↦ ⟨(mem_cuspFormsNew_iff_of_mem_cuspFormCharSpace h.2).mpr h.1, h.2⟩⟩

/-- **The old/new decomposition restricts to each nebentypus space**: `S_k(N, χ)` is spanned by
its old and its new part. Inside `S_k(N, χ)` the two are complementary, by the modular law and
the completeness of the Petersson-orthogonal complement. -/
theorem sup_cuspFormsOld_cuspFormsNew_inf_cuspFormCharSpace (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    cuspFormsOld N k ⊓ cuspFormCharSpace k χ ⊔ cuspFormsNew N k ⊓ cuspFormCharSpace k χ =
      cuspFormCharSpace k χ :=
  calc cuspFormsOld N k ⊓ cuspFormCharSpace k χ ⊔ cuspFormsNew N k ⊓ cuspFormCharSpace k χ
      = cuspFormsOld N k ⊓ cuspFormCharSpace k χ ⊔
          CuspForm.peterssonOrthogonal (cuspFormsOld N k ⊓ cuspFormCharSpace k χ) ⊓
            cuspFormCharSpace k χ := by
        rw [cuspFormsNew_inf_cuspFormCharSpace]
    _ = (cuspFormsOld N k ⊓ cuspFormCharSpace k χ ⊔
          CuspForm.peterssonOrthogonal (cuspFormsOld N k ⊓ cuspFormCharSpace k χ)) ⊓
            cuspFormCharSpace k χ := (sup_inf_assoc_of_le _ inf_le_right).symm
    _ = cuspFormCharSpace k χ := by
        rw [CuspForm.sup_peterssonOrthogonal_eq_top, top_inf_eq]

/-- **The old and new parts of `S_k(N, χ)` meet only in `0`.** -/
theorem disjoint_cuspFormsOld_cuspFormsNew_inf_cuspFormCharSpace (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Disjoint (cuspFormsOld N k ⊓ cuspFormCharSpace k χ)
      (cuspFormsNew N k ⊓ cuspFormCharSpace k χ) :=
  (disjoint_cuspFormsOld_cuspFormsNew N k).mono inf_le_left inf_le_left

end TauCeti
