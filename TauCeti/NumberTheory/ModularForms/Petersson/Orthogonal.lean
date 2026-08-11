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

The complement uses Mathlib's `Submodule.orthogonalBilin`, applied to the Petersson pairing
bundled as a sesquilinear form. Deliberately, no `InnerProductSpace` instance on `S_k(Γ)` is
derived from `CuspForm.peterssonInnerCosetsCore`; see the note on that definition.

## Main definitions

* `TauCeti.CuspForm.peterssonOrthogonal`: the Petersson-orthogonal complement of a subspace of
  `S_k(Γ)`.
* `TauCeti.CuspForm.peterssonInnerCosetsₛₗ`: the Petersson pairing as a sesquilinear form.

## Main results

* `TauCeti.CuspForm.mem_peterssonOrthogonal_iff'`: orthogonality may equivalently be tested in
  the other argument of the pairing, by Hermitian symmetry.
* `TauCeti.CuspForm.peterssonOrthogonal_disjoint`: a subspace and its complement meet only in
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

/-- The Petersson pairing as a sesquilinear form: conjugate-linear in the first cusp form and
linear in the second. -/
noncomputable def peterssonInnerCosetsₛₗ :
    CuspForm (Γ.map (mapGL ℝ)) k →ₗ⋆[ℂ] CuspForm (Γ.map (mapGL ℝ)) k →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun := peterssonInnerCosets f
      map_add' := peterssonInnerCosets_add_right f
      map_smul' c g := peterssonInnerCosets_smul_right c f g }
  map_add' f₁ f₂ := LinearMap.ext fun g ↦ peterssonInnerCosets_add_left f₁ f₂ g
  map_smul' c f := LinearMap.ext fun g ↦ peterssonInnerCosets_smul_left c f g

@[simp]
theorem peterssonInnerCosetsₛₗ_apply_apply (f g : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosetsₛₗ f g = peterssonInnerCosets f g := (rfl)

/-- The **Petersson-orthogonal complement** of a subspace `V` of `S_k(Γ)`: the cusp forms
pairing to zero against every element of `V`. It is a subspace because the Petersson pairing
is additive and `ℂ`-linear in its second argument. -/
noncomputable def peterssonOrthogonal (V : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) :
    Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k) :=
  V.orthogonalBilin peterssonInnerCosetsₛₗ

/-- Membership in the Petersson-orthogonal complement is orthogonality to every element. -/
@[simp]
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
@[gcongr]
theorem peterssonOrthogonal_le (h : V ≤ W) :
    peterssonOrthogonal W ≤ peterssonOrthogonal V :=
  Submodule.orthogonalBilin_le h

/-- Everything is orthogonal to the zero subspace. -/
@[simp]
theorem peterssonOrthogonal_bot :
    peterssonOrthogonal (⊥ : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) = ⊤ :=
  eq_top_iff.mpr fun f _ g hg ↦ by
    rw [(Submodule.mem_bot ℂ).mp hg, peterssonInnerCosetsₛₗ_apply_apply,
      peterssonInnerCosets_zero_left]

/-- Only `0` is orthogonal to all of `S_k(Γ)`: this is positive definiteness. -/
@[simp]
theorem peterssonOrthogonal_top :
    peterssonOrthogonal (⊤ : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) = ⊥ :=
  eq_bot_iff.mpr fun f hf ↦
    (Submodule.mem_bot ℂ).mpr (peterssonInnerCosets_definite f (hf f Submodule.mem_top))

/-- **A subspace and its Petersson-orthogonal complement meet only in `0`.** A form in both
pairs with itself to zero, and the pairing is positive definite. -/
theorem peterssonOrthogonal_disjoint (V : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) :
    Disjoint V (peterssonOrthogonal V) := by
  rw [Submodule.disjoint_def]
  exact fun f hfV hfO ↦ peterssonInnerCosets_definite f (hfO f hfV)

/-- A subspace is contained in its double Petersson-orthogonal complement. -/
theorem le_peterssonOrthogonal_peterssonOrthogonal
    (V : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) :
    V ≤ peterssonOrthogonal (peterssonOrthogonal V) :=
  Submodule.le_orthogonalBilin_orthogonalBilin fun f g hfg ↦ by
    have hfg' : peterssonInnerCosets f g = 0 := by simpa using hfg
    rw [peterssonInnerCosetsₛₗ_apply_apply, ← peterssonInnerCosets_conj_symm g f,
      hfg', map_zero]

section PeterssonInnerProductSpace

/-- The Petersson core, installed locally to access Mathlib's inner-product-space API. -/
noncomputable local instance peterssonInnerCosetsCoreInstance :
    InnerProductSpace.Core ℂ (CuspForm (Γ.map (mapGL ℝ)) k) :=
  peterssonInnerCosetsCore

/-- The normed additive structure induced locally by the Petersson core. -/
noncomputable local instance peterssonNormedAddCommGroup :
    NormedAddCommGroup (CuspForm (Γ.map (mapGL ℝ)) k) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

/-- The inner-product-space structure induced locally by the Petersson core. -/
noncomputable local instance peterssonInnerProductSpace :
    InnerProductSpace ℂ (CuspForm (Γ.map (mapGL ℝ)) k) :=
  InnerProductSpace.ofCore _

/-- The inner product induced locally from the Petersson core evaluates to the Petersson
pairing. -/
private theorem peterssonInner_apply (f g : CuspForm (Γ.map (mapGL ℝ)) k) :
    inner ℂ f g = peterssonInnerCosets f g :=
  peterssonInnerCosetsCore_inner f g

/-- The locally induced inner-product orthogonal is the Petersson-orthogonal complement. -/
private theorem peterssonOrthogonal_eq_orthogonal
    (W : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) : peterssonOrthogonal W = Wᗮ := by
  ext f
  rw [mem_peterssonOrthogonal_iff, Submodule.mem_orthogonal]
  simp only [peterssonInner_apply]

/-- **Taking the Petersson-orthogonal complement twice recovers the original subspace.** -/
@[simp]
theorem peterssonOrthogonal_peterssonOrthogonal
    (V : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) :
    peterssonOrthogonal (peterssonOrthogonal V) = V := by
  let _ : Module.Finite ℂ (CuspForm (Γ.map (mapGL ℝ)) k) :=
    Module.Finite.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective
  rw [peterssonOrthogonal_eq_orthogonal, peterssonOrthogonal_eq_orthogonal,
    Submodule.orthogonal_orthogonal]

/-- **A subspace and its Petersson-orthogonal complement span the full cusp-form space.** -/
theorem sup_peterssonOrthogonal_eq_top
    (V : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) :
    V ⊔ peterssonOrthogonal V = ⊤ := by
  let _ : Module.Finite ℂ (CuspForm (Γ.map (mapGL ℝ)) k) :=
    Module.Finite.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective
  rw [peterssonOrthogonal_eq_orthogonal]
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

end PeterssonInnerProductSpace

/-- **The complement of a supremum is the infimum of the complements.** Orthogonality to a
family of subspaces spreads to the subspace they generate, since the pairing is additive in
its first argument. -/
theorem peterssonOrthogonal_iSup {ι : Sort*}
    (V : ι → Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) k)) :
    peterssonOrthogonal (⨆ i, V i) = ⨅ i, peterssonOrthogonal (V i) := by
  refine le_antisymm
    (le_iInf fun i ↦ peterssonOrthogonal_le (le_iSup V i)) fun f hf ↦ ?_
  rw [Submodule.mem_iInf] at hf
  intro g hg
  refine Submodule.iSup_induction V (motive := fun g ↦ peterssonInnerCosets g f = 0) hg
    (fun i y hy ↦ hf i y hy) (peterssonInnerCosets_zero_left f) fun g₁ g₂ h₁ h₂ ↦ ?_
  rw [peterssonInnerCosets_add_left, h₁, h₂, add_zero]

/-- **The orthogonal complement, as an adjunction.** A form lies in `Vᗮ` exactly when `V` sits
inside the kernel of pairing against it; this is the form in which orthogonality is checked on
a generating family, since the right-hand side is an inequality of subspaces. -/
theorem mem_peterssonOrthogonal_iff_le_ker :
    f ∈ peterssonOrthogonal V ↔ V ≤ LinearMap.ker (peterssonInnerCosetsₛₗ f) :=
  ⟨fun hf g hg ↦ by
    rw [LinearMap.mem_ker, peterssonInnerCosetsₛₗ_apply_apply]
    exact mem_peterssonOrthogonal_iff'.mp hf g hg,
  fun h ↦ mem_peterssonOrthogonal_iff'.mpr fun g hg ↦ by
    simpa only [LinearMap.mem_ker, peterssonInnerCosetsₛₗ_apply_apply] using h hg⟩

/-- **Orthogonality to a range is orthogonality to the values.** -/
theorem mem_peterssonOrthogonal_range_iff {E : Type*} [AddCommGroup E] [Module ℂ E]
    (L : E →ₗ[ℂ] CuspForm (Γ.map (mapGL ℝ)) k) :
    f ∈ peterssonOrthogonal (LinearMap.range L) ↔ ∀ e, peterssonInnerCosets (L e) f = 0 := by
  refine ⟨fun h e ↦ h _ ⟨e, rfl⟩, ?_⟩
  rintro h _ ⟨e, rfl⟩
  exact h e

end CuspForm

end TauCeti
