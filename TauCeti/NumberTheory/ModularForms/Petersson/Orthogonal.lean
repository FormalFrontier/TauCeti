/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex
import TauCeti.NumberTheory.ModularForms.SturmBound

/-!
# Petersson-orthogonal complements

The Petersson pairing `CuspForm.peterssonInnerCosets` on `S_k(Γ)` is a positive-definite
Hermitian form, so every subspace `V ≤ S_k(Γ)` has a Petersson-orthogonal complement

`Vᗮ = {f ∈ S_k(Γ) | ⟪g, f⟫ = 0 for every g ∈ V}`,

and `V` and `Vᗮ` intersect only in `0`. This file introduces that complement as
`TauCeti.CuspForm.peterssonOrthogonal` and gives it the order-theoretic API the old/new
decomposition of Layer 3 of the ModularForms roadmap needs: it reverses `≤`, it turns a
supremum of subspaces into an infimum of complements, and orthogonality to the range of a
linear map is tested on the map's values alone.

The complement is built by hand rather than as `Submodule.orthogonal`, because
`peterssonInnerCosets` is bundled only as an `InnerProductSpace.Core` and, deliberately, no
`InnerProductSpace` instance on `S_k(Γ)` is derived from it — see the note on
`CuspForm.peterssonInnerCosetsCore`. Everything below uses only the Hermitian axioms recorded
in that core, so it transfers unchanged if such an instance is ever installed.

## Main definitions

* `TauCeti.CuspForm.peterssonOrthogonal`: the Petersson-orthogonal complement of a subspace of
  `S_k(Γ)`.
* `TauCeti.CuspForm.peterssonInnerCosetsRight`: pairing against a fixed form, as a `ℂ`-linear
  functional.

## Main results

* `TauCeti.CuspForm.mem_peterssonOrthogonal_iff'`: orthogonality may equivalently be tested in
  the other argument of the pairing, by Hermitian symmetry.
* `TauCeti.CuspForm.disjoint_peterssonOrthogonal`: a subspace and its complement meet only in
  `0`; this is positive definiteness.
* `TauCeti.CuspForm.peterssonOrthogonal_peterssonOrthogonal`: taking the complement twice
  recovers the original subspace.
* `TauCeti.CuspForm.sup_peterssonOrthogonal_eq_top`: a subspace and its complement span the full
  cusp-form space.
* `TauCeti.CuspForm.peterssonOrthogonal_iSup`: the complement of a supremum is the infimum of
  the complements.
* `TauCeti.CuspForm.mem_peterssonOrthogonal_iff_le_ker`: membership in a complement, restated as
  an inclusion of subspaces, which is how orthogonality is checked on a generating family.
* `TauCeti.CuspForm.mem_peterssonOrthogonal_range_iff`: orthogonality to the range of a linear
  map is orthogonality to each of its values.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Section 5.6.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane

open scoped MatrixGroups ModularForm ComplexConjugate

namespace TauCeti

open _root_.CuspForm

namespace CuspForm

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}
variable {V W : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)}
  {f : CuspForm (Γ.map (mapGL ℝ)) k}

/-- The **Petersson-orthogonal complement** of a subspace `V` of `S_k(Γ)`: the cusp forms
pairing to zero against every element of `V`. It is a subspace because the Petersson pairing
is additive and `ℂ`-linear in its second argument. -/
def peterssonOrthogonal (V : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) :
    Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k) where
  carrier := {f | ∀ g ∈ V, peterssonInnerCosets g f = 0}
  add_mem' hf₁ hf₂ g hg := by
    rw [peterssonInnerCosets_add_right, hf₁ g hg, hf₂ g hg, add_zero]
  zero_mem' g _ := peterssonInnerCosets_zero_right g
  smul_mem' c _ hf g hg := by rw [peterssonInnerCosets_smul_right, hf g hg, mul_zero]

/-- Membership in the Petersson-orthogonal complement is orthogonality to every element. -/
theorem mem_peterssonOrthogonal_iff :
    f ∈ peterssonOrthogonal V ↔ ∀ g ∈ V, peterssonInnerCosets g f = 0 := Iff.rfl

/-- Orthogonality may be tested in either argument: the Petersson pairing is Hermitian, so one
of `⟪g, f⟫` and `⟪f, g⟫` vanishes exactly when the other does. -/
theorem mem_peterssonOrthogonal_iff' :
    f ∈ peterssonOrthogonal V ↔ ∀ g ∈ V, peterssonInnerCosets f g = 0 := by
  rw [mem_peterssonOrthogonal_iff]
  refine ⟨fun h g hg ↦ ?_, fun h g hg ↦ ?_⟩
  · rw [← peterssonInnerCosets_conj_symm f g, h g hg, map_zero]
  · rw [← peterssonInnerCosets_conj_symm g f, h g hg, map_zero]

/-- The Petersson-orthogonal complement reverses inclusions. -/
theorem peterssonOrthogonal_le_peterssonOrthogonal (h : V ≤ W) :
    peterssonOrthogonal W ≤ peterssonOrthogonal V :=
  fun _ hf g hg ↦ hf g (h hg)

/-- Everything is orthogonal to the zero subspace. -/
@[simp]
theorem peterssonOrthogonal_bot :
    peterssonOrthogonal (⊥ : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) = ⊤ :=
  eq_top_iff.mpr fun f _ g hg ↦ by
    rw [(Submodule.mem_bot ℂ).mp hg, peterssonInnerCosets_zero_left]

/-- Only `0` is orthogonal to all of `S_k(Γ)`: this is positive definiteness. -/
@[simp]
theorem peterssonOrthogonal_top :
    peterssonOrthogonal (⊤ : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) = ⊥ :=
  eq_bot_iff.mpr fun f hf ↦
    (Submodule.mem_bot ℂ).mpr (peterssonInnerCosets_definite f (hf f Submodule.mem_top))

/-- **A subspace and its Petersson-orthogonal complement meet only in `0`.** A form in both
pairs with itself to zero, and the pairing is positive definite. -/
theorem disjoint_peterssonOrthogonal (V : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) :
    Disjoint V (peterssonOrthogonal V) := by
  rw [Submodule.disjoint_def]
  exact fun f hfV hfO ↦ peterssonInnerCosets_definite f (hfO f hfV)

/-- A subspace is contained in its double Petersson-orthogonal complement. -/
theorem le_peterssonOrthogonal_peterssonOrthogonal
    (V : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) :
    V ≤ peterssonOrthogonal (peterssonOrthogonal V) := by
  intro f hf g hg
  rw [← peterssonInnerCosets_conj_symm g f, hg f hf, map_zero]

/-- **Taking the Petersson-orthogonal complement twice recovers the original subspace.** -/
theorem peterssonOrthogonal_peterssonOrthogonal
    (V : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) :
    peterssonOrthogonal (peterssonOrthogonal V) = V := by
  let _ : Module.Finite ℂ (CuspForm (Γ.map (mapGL ℝ)) k) :=
    Module.Finite.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective
  let _ : InnerProductSpace.Core ℂ (CuspForm (Γ.map (mapGL ℝ)) k) :=
    peterssonInnerCosetsCore
  let _ : NormedAddCommGroup (CuspForm (Γ.map (mapGL ℝ)) k) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let _ : NormedSpace ℂ (CuspForm (Γ.map (mapGL ℝ)) k) :=
    InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ)
  let peterssonPreCore : PreInnerProductSpace.Core ℂ (CuspForm (Γ.map (mapGL ℝ)) k) :=
    { inner := peterssonInnerCosets
      conj_inner_symm := peterssonInnerCosets_conj_symm
      re_inner_nonneg := peterssonInnerCosets_self_re_nonneg
      add_left := peterssonInnerCosets_add_left
      smul_left := fun f g c ↦ peterssonInnerCosets_smul_left c f g }
  let _ : InnerProductSpace ℂ (CuspForm (Γ.map (mapGL ℝ)) k) :=
    { peterssonPreCore with
      norm_sq_eq_re_inner := fun f ↦ by
        change √((peterssonInnerCosetsCore : InnerProductSpace.Core ℂ
          (CuspForm (Γ.map (mapGL ℝ)) k)).inner f f).re ^ 2 = (peterssonInnerCosets f f).re
        rw [peterssonInnerCosetsCore_inner]
        exact Real.sq_sqrt (peterssonInnerCosets_self_re_nonneg f) }
  have hpeterssonOrthogonal
      (W : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) : peterssonOrthogonal W = Wᗮ := by
    ext f
    rw [mem_peterssonOrthogonal_iff, Submodule.mem_orthogonal]
    constructor
    · intro h g hg
      change peterssonInnerCosets g f = 0
      exact h g hg
    · intro h g hg
      have hgf := h g hg
      change peterssonInnerCosets g f = 0 at hgf
      exact hgf
  rw [hpeterssonOrthogonal, hpeterssonOrthogonal, Submodule.orthogonal_orthogonal]

/-- **A subspace and its Petersson-orthogonal complement span the full cusp-form space.** -/
theorem sup_peterssonOrthogonal_eq_top
    (V : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) :
    V ⊔ peterssonOrthogonal V = ⊤ := by
  have horth : peterssonOrthogonal (V ⊔ peterssonOrthogonal V) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    have hfV : f ∈ peterssonOrthogonal V := fun g hg ↦ hf g (Submodule.mem_sup_left hg)
    have hfVV : f ∈ peterssonOrthogonal (peterssonOrthogonal V) :=
      fun g hg ↦ hf g (Submodule.mem_sup_right hg)
    rw [peterssonOrthogonal_peterssonOrthogonal] at hfVV
    exact Submodule.disjoint_def.mp (disjoint_peterssonOrthogonal V) f hfVV hfV
  calc
    V ⊔ peterssonOrthogonal V =
        peterssonOrthogonal (peterssonOrthogonal (V ⊔ peterssonOrthogonal V)) :=
      (peterssonOrthogonal_peterssonOrthogonal _).symm
    _ = peterssonOrthogonal ⊥ := congrArg peterssonOrthogonal horth
    _ = ⊤ := peterssonOrthogonal_bot

/-- **The complement of a supremum is the infimum of the complements.** Orthogonality to a
family of subspaces spreads to the subspace they generate, since the pairing is additive in
its first argument. -/
theorem peterssonOrthogonal_iSup {ι : Sort*}
    (V : ι → Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) :
    peterssonOrthogonal (⨆ i, V i) = ⨅ i, peterssonOrthogonal (V i) := by
  refine le_antisymm
    (le_iInf fun i ↦ peterssonOrthogonal_le_peterssonOrthogonal (le_iSup V i)) fun f hf ↦ ?_
  rw [Submodule.mem_iInf] at hf
  intro g hg
  refine Submodule.iSup_induction V (motive := fun g ↦ peterssonInnerCosets g f = 0) hg
    (fun i y hy ↦ hf i y hy) (peterssonInnerCosets_zero_left f) fun g₁ g₂ h₁ h₂ ↦ ?_
  rw [peterssonInnerCosets_add_left, h₁, h₂, add_zero]

/-- Pairing against a fixed form on the left, as a `ℂ`-linear functional: the Petersson product
is linear in its second argument. -/
noncomputable def peterssonInnerCosetsRight (f : CuspForm (Γ.map (mapGL ℝ)) k) :
    CuspForm (Γ.map (mapGL ℝ)) k →ₗ[ℂ] ℂ where
  toFun := peterssonInnerCosets f
  map_add' := peterssonInnerCosets_add_right f
  map_smul' c g := peterssonInnerCosets_smul_right c f g

@[simp]
theorem peterssonInnerCosetsRight_apply (f g : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosetsRight f g = peterssonInnerCosets f g := (rfl)

/-- **The orthogonal complement, as an adjunction.** A form lies in `Vᗮ` exactly when `V` sits
inside the kernel of pairing against it; this is the form in which orthogonality is checked on
a generating family, since the right-hand side is an inequality of subspaces. -/
theorem mem_peterssonOrthogonal_iff_le_ker :
    f ∈ peterssonOrthogonal V ↔ V ≤ LinearMap.ker (peterssonInnerCosetsRight f) :=
  mem_peterssonOrthogonal_iff'

/-- **Orthogonality to a range is orthogonality to the values.** -/
theorem mem_peterssonOrthogonal_range_iff {E : Type*} [AddCommGroup E] [Module ℂ E]
    (L : E →ₗ[ℂ] CuspForm (Γ.map (mapGL ℝ)) k) :
    f ∈ peterssonOrthogonal (LinearMap.range L) ↔ ∀ e, peterssonInnerCosets (L e) f = 0 := by
  refine ⟨fun h e ↦ h _ ⟨e, rfl⟩, ?_⟩
  rintro h _ ⟨e, rfl⟩
  exact h e

end CuspForm

end TauCeti
