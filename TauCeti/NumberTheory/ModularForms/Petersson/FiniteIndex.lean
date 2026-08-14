/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.Basic
public import TauCeti.NumberTheory.ModularForms.Petersson.Basic
public import TauCeti.GroupTheory.Index
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# The Petersson inner product for a finite-index subgroup

The Petersson pairing of `Mathlib.NumberTheory.ModularForms.Petersson` is integrated over
the standard fundamental domain `𝒟` of `SL₂(ℤ)`, which is too small for forms on a proper
subgroup `Γ ≤ SL₂(ℤ)`: a fundamental domain for `Γ` is tiled by `[SL₂(ℤ) : Γ·{±I}]` translates of
`𝒟`. This file defines the pairing on `S_k(Γ)` as the corresponding sum over cosets,

`⟪f, g⟫ = ∑_{[δ] ∈ SL₂(ℤ)/Γ·{±I}} ∫_𝒟 conj((f ∣[k] δ⁻¹)(τ)) (g ∣[k] δ⁻¹)(τ) (Im τ)^k dμ`,

and establishes that it is a positive-definite Hermitian form: conjugate-symmetric, additive
and complex-linear in the second argument, conjugate-linear in the first, and vanishing on
the diagonal only at `0`.

The sum runs over the cosets of `Γ·{±I}`, not of `Γ`: since `-I` acts trivially on `ℍ`, the
cosets of `q` and `-q` carry the same translate of `𝒟`, so indexing by `Γ` alone would count
every translate twice whenever `-I ∉ Γ`. The summand does not depend on the chosen
representative: the `Γ` part of the subgroup fixes a `Γ`-invariant form, and `-I` scales it by
the real sign `(-1)^k`, which the conjugate-linear pairing cancels against itself.

Finite index is what makes the sum finite, and it is also exactly what makes the image of `Γ`
in `GL(2, ℝ)` arithmetic, which the definiteness argument needs. Taking `Γ = Γ₁(N)` gives the
classical level-`N` Petersson product.

The pairing is deliberately left un-normalized by the volume of the fundamental domain: a
positive-definite Hermitian form is all that the adjoint theory downstream needs.

## Main definitions

* `CuspForm.peterssonInnerCosets`: the Petersson inner product on `S_k(Γ)`.

## Main results

* `Subgroup.mem_withCenter_iff`: an element of `Γ·{±I}` is `±` one of `Γ`.
* `CuspForm.exists_slash_eq_smul_of_mem_withCenter`: slashing by an element of `Γ·{±I}` scales
  every form by one and the same unimodular constant.
* `CuspForm.peterssonInner_slash_of_mem_withCenter`: the summand is independent of the coset
  representative, which is what makes the sum well defined.
* `CuspForm.peterssonInnerCosets_conj_symm`: Hermitian symmetry.
* `CuspForm.peterssonInnerCosets_add_left`/`_right`, `_smul_right`, `_smul_left`:
  sesquilinearity.
* `CuspForm.peterssonInnerCosets_definite`: positive definiteness.
* `CuspForm.peterssonInnerCosetsCore`: the pairing bundled as an `InnerProductSpace.Core`.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/PeterssonLevelN.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), with the
bespoke hyperbolic measure replaced by the `volume` of `ℍ` used throughout TauCeti, and
stated for an arbitrary finite-index subgroup rather than only `Γ₁(N)`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Section 5.4.
-/

public section

open MeasureTheory UpperHalfPlane ModularGroup Complex
open Matrix.SpecialLinearGroup

open scoped MatrixGroups ModularForm ComplexConjugate

namespace Subgroup

/-- The coset space of `Γ.withCenter` is finite when `Γ` has finite index; this is what makes
the defining sum of `CuspForm.peterssonInnerCosets` a finite one. -/
noncomputable instance fintypeQuotientWithCenter {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] :
    Fintype (SL(2, ℤ) ⧸ Γ.withCenter) :=
  Subgroup.fintypeQuotientOfFiniteIndex

end Subgroup

namespace CuspForm

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}

/-- The **Petersson inner product** on `S_k(Γ)` for a finite-index `Γ ≤ SL₂(ℤ)`: the sum,
over the cosets of `Γ·{±I}` in `SL₂(ℤ)`, of the level-one pairing of the correspondingly
slashed forms. The subgroup is `Γ.withCenter`, not `Γ`, because `-I` acts trivially on `ℍ`.
For `Γ = Γ₁(N)` this is the classical level-`N` Petersson product. -/
noncomputable def peterssonInnerCosets
    (f g : CuspForm (Γ.map (mapGL ℝ)) k) : ℂ :=
  ∑ q : SL(2, ℤ) ⧸ Γ.withCenter,
    UpperHalfPlane.peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑g ∣[k] (q.out)⁻¹)

/-- Unfolding: the pairing is the coset sum of level-one pairings. -/
theorem peterssonInnerCosets_def (f g : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets f g = ∑ q : SL(2, ℤ) ⧸ Γ.withCenter,
      UpperHalfPlane.peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑g ∣[k] (q.out)⁻¹) := (rfl)

/-- Hermitian symmetry of the coset pairing. -/
@[simp]
theorem peterssonInnerCosets_conj_symm (f g : CuspForm (Γ.map (mapGL ℝ)) k) :
    conj (peterssonInnerCosets g f) = peterssonInnerCosets f g := by
  simp only [peterssonInnerCosets, map_sum, peterssonInner_conj_symm]

/-- The coset pairing vanishes when its second argument does. -/
@[simp]
theorem peterssonInnerCosets_zero_right (f : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets f 0 = 0 := by
  simp [peterssonInnerCosets]

/-- The coset pairing vanishes when its first argument does. -/
@[simp]
theorem peterssonInnerCosets_zero_left (g : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets 0 g = 0 := by
  simp [peterssonInnerCosets]

omit [Γ.FiniteIndex] in
private theorem out_one_mem_WithCenter :
    ((QuotientGroup.mk 1 : SL(2, ℤ) ⧸ Γ.withCenter)).out ∈ Γ.withCenter := by
  have h : (QuotientGroup.mk
      ((QuotientGroup.mk 1 : SL(2, ℤ) ⧸ Γ.withCenter)).out : SL(2, ℤ) ⧸ Γ.withCenter) =
      QuotientGroup.mk 1 := Quotient.out_eq _
  simpa using (Γ.withCenter).inv_mem (QuotientGroup.eq.mp h)

omit [Γ.FiniteIndex] in
/-- Membership in `Γ·{±I}`: its elements are exactly `±` the elements of `Γ`. The adjoined
centre of `SL₂(ℤ)` is `{±I}`, so the supremum only adds the negatives. -/
@[simp]
theorem _root_.Subgroup.mem_withCenter_iff {γ : SL(2, ℤ)} :
    γ ∈ Γ.withCenter ↔ ∃ γ' ∈ Γ, γ = γ' ∨ γ = -γ' := by
  refine ⟨fun hγ ↦ ?_, ?_⟩
  · rw [Subgroup.withCenter_def, ← SetLike.mem_coe, Subgroup.mul_normal] at hγ
    obtain ⟨a, ha, b, hb, rfl⟩ := hγ
    obtain ⟨r, hr, hscal⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hb
    have hb1 : b = 1 ∨ b = -1 := by
      have : r = 1 ∨ r = -1 :=
        Int.isUnit_iff.mp (IsUnit.of_mul_eq_one r (by simpa [pow_two] using hr))
      rcases this with rfl | rfl
      · exact Or.inl (Subtype.ext (by simpa using hscal.symm))
      · exact Or.inr (Subtype.ext (by simpa using hscal.symm))
    refine ⟨a, ha, ?_⟩
    rcases hb1 with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  · rintro ⟨γ', hγ', rfl | rfl⟩
    · exact Γ.le_withCenter hγ'
    · have hcenter : (-1 : SL(2, ℤ)) ∈ Subgroup.center SL(2, ℤ) :=
        Subgroup.mem_center_iff.mpr fun g ↦ by rw [neg_one_mul, mul_neg_one]
      exact Subgroup.withCenter_def Γ ▸ mul_neg_one γ' ▸ Subgroup.mul_mem_sup hγ' hcenter

omit [Γ.FiniteIndex] in
/-- **Slashing by `Γ·{±I}` scales every form by one and the same unimodular constant**: by `1`
on `Γ` itself, where the forms are invariant, and by `(-1)^k` on its negatives, since `-I` acts
trivially on `ℍ` and contributes only the automorphy factor. Unimodularity `conj c * c = 1` is
what makes the constant invisible to the conjugate-linear Petersson pairing. -/
theorem exists_slash_eq_smul_of_mem_withCenter {γ : SL(2, ℤ)} (hγ : γ ∈ Γ.withCenter) :
    ∃ c : ℂ, conj c * c = 1 ∧ ∀ f : CuspForm (Γ.map (mapGL ℝ)) k, ⇑f ∣[k] γ = c • ⇑f := by
  obtain ⟨γ', hγ', hcase⟩ := Subgroup.mem_withCenter_iff.mp hγ
  rcases hcase with rfl | rfl
  · exact ⟨1, by simp, fun f ↦ by rw [SlashInvariantFormClass.SL_slash_eq f _ hγ', one_smul]⟩
  · refine ⟨(-1 : ℂ) ^ k, ?_, fun f ↦ ?_⟩
    · have hreal : conj ((-1 : ℂ) ^ k) = (-1 : ℂ) ^ k := by simp
      rw [hreal, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← two_mul, zpow_mul]
      norm_num
    · -- the `SL(2, ℤ)` slash action goes through `mapGL ℝ`, which sends `-I` to `-I`
      have hcoe : ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = -1 := mapGL_neg_one
      rw [← mul_neg_one γ', SlashAction.slash_mul, ModularForm.SL_slash (γ := (-1 : SL(2, ℤ))),
        hcoe, ModularForm.slash_neg_one, SlashInvariantFormClass.SL_slash_eq f _ hγ']

omit [Γ.FiniteIndex] in
/-- **The summand does not depend on the coset representative**: the level-one-domain pairing
is unchanged by slashing with `Γ·{±I}`. The `Γ` part fixes a `Γ`-invariant form, and `-I`
scales it by the real sign `(-1)^k`, which the conjugate-linear pairing cancels against
itself. This is what lets the defining sum be reindexed over the coset space. -/
theorem peterssonInner_slash_of_mem_withCenter
    (f g : CuspForm (Γ.map (mapGL ℝ)) k) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ.withCenter) :
    UpperHalfPlane.peterssonInner k fd (⇑f ∣[k] γ) (⇑g ∣[k] γ) = peterssonInnerFd f g := by
  obtain ⟨c, hc, hslash⟩ := exists_slash_eq_smul_of_mem_withCenter (k := k) hγ
  rw [hslash f, hslash g, peterssonInner_smul_left, peterssonInner_smul_right, ← mul_assoc, hc,
    one_mul, peterssonInnerFd_def]

omit [Γ.FiniteIndex] in
/-- Each summand of the self-pairing is a non-negative real: the integrand is
`‖(f ∣[k] q.out⁻¹)(τ)‖² (Im τ)^k`. -/
private theorem peterssonInnerCosets_summand_nonneg
    (f : CuspForm (Γ.map (mapGL ℝ)) k) (q : SL(2, ℤ) ⧸ Γ.withCenter) :
    ∃ r : ℝ, 0 ≤ r ∧
      UpperHalfPlane.peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑f ∣[k] (q.out)⁻¹) = (r : ℂ) := by
  set h := ⇑f ∣[k] (q.out)⁻¹ with hh
  refine ⟨∫ τ in fd, normSq (h τ) * τ.im ^ k, ?_,
    UpperHalfPlane.peterssonInner_self_eq_ofReal k fd h⟩
  have hnn := UpperHalfPlane.peterssonInner_self_re_nonneg k fd h
  rwa [UpperHalfPlane.peterssonInner_self_eq_ofReal, Complex.ofReal_re] at hnn

/-- **Positive definiteness** of the Petersson inner product: every summand of the
self-pairing is non-negative, so the whole sum vanishes only if the identity-coset summand
does, and that summand is the level-one pairing. -/
theorem peterssonInnerCosets_definite (f : CuspForm (Γ.map (mapGL ℝ)) k)
    (hpet : peterssonInnerCosets f f = 0) : f = 0 := by
  apply peterssonInnerFd_definite f
  rw [← peterssonInner_slash_of_mem_withCenter f f
    ((Γ.withCenter).inv_mem out_one_mem_WithCenter)]
  choose r hr_nonneg hr_eq using peterssonInnerCosets_summand_nonneg f
  have hsum : ((∑ q, r q : ℝ) : ℂ) = 0 := by
    rw [Complex.ofReal_sum]
    simp_rw [← hr_eq]
    exact hpet
  rw [hr_eq (QuotientGroup.mk 1), (Finset.sum_eq_zero_iff_of_nonneg fun q _ ↦ hr_nonneg q).mp
    (Complex.ofReal_eq_zero.mp hsum) (QuotientGroup.mk 1) (Finset.mem_univ _), Complex.ofReal_zero]

/-- Negation in the second argument. -/
@[simp]
theorem peterssonInnerCosets_neg_right (f g : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets f (-g) = -peterssonInnerCosets f g := by
  simp only [peterssonInnerCosets, FunLike.coe_neg, SlashAction.neg_slash,
    peterssonInner_neg_right, Finset.sum_neg_distrib]

/-- Negation in the first argument. -/
@[simp]
theorem peterssonInnerCosets_neg_left (f g : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets (-f) g = -peterssonInnerCosets f g := by
  simp only [peterssonInnerCosets, FunLike.coe_neg, SlashAction.neg_slash,
    peterssonInner_neg_left, Finset.sum_neg_distrib]

/-- Additivity in the second argument. -/
@[simp]
theorem peterssonInnerCosets_add_right (f g₁ g₂ : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets f (g₁ + g₂) =
      peterssonInnerCosets f g₁ + peterssonInnerCosets f g₂ := by
  simp only [peterssonInnerCosets, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [FunLike.coe_add, SlashAction.add_slash]
  exact peterssonInner_add_right k fd _ _ _
    (integrableOn_petersson_slash k _ f g₁ (q.out)⁻¹)
    (integrableOn_petersson_slash k _ f g₂ (q.out)⁻¹)

/-- Complex-linearity in the second argument. -/
@[simp]
theorem peterssonInnerCosets_smul_right (c : ℂ)
    (f g : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets f (c • g) = c * peterssonInnerCosets f g := by
  simp only [peterssonInnerCosets, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [FunLike.coe_smul, ModularForm.SL_smul_slash]
  exact peterssonInner_smul_right k _ c _ _

/-- Conjugate-linearity in the first argument. -/
@[simp]
theorem peterssonInnerCosets_smul_left (c : ℂ)
    (f g : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets (c • f) g = conj c * peterssonInnerCosets f g :=
  calc peterssonInnerCosets (c • f) g
      = conj (peterssonInnerCosets g (c • f)) := (peterssonInnerCosets_conj_symm _ _).symm
    _ = conj (c * peterssonInnerCosets g f) := by rw [peterssonInnerCosets_smul_right]
    _ = conj c * conj (peterssonInnerCosets g f) := map_mul _ _ _
    _ = conj c * peterssonInnerCosets f g := by rw [peterssonInnerCosets_conj_symm]

/-- Additivity in the first argument. -/
@[simp]
theorem peterssonInnerCosets_add_left (f₁ f₂ g : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets (f₁ + f₂) g =
      peterssonInnerCosets f₁ g + peterssonInnerCosets f₂ g :=
  calc peterssonInnerCosets (f₁ + f₂) g
      = conj (peterssonInnerCosets g (f₁ + f₂)) := (peterssonInnerCosets_conj_symm _ _).symm
    _ = conj (peterssonInnerCosets g f₁ + peterssonInnerCosets g f₂) := by
        rw [peterssonInnerCosets_add_right]
    _ = conj (peterssonInnerCosets g f₁) + conj (peterssonInnerCosets g f₂) := map_add _ _ _
    _ = peterssonInnerCosets f₁ g + peterssonInnerCosets f₂ g := by
        rw [peterssonInnerCosets_conj_symm, peterssonInnerCosets_conj_symm]

/-- The self-pairing is nonnegative: each coset summand is a nonnegative real. -/
theorem peterssonInnerCosets_self_re_nonneg (f : CuspForm (Γ.map (mapGL ℝ)) k) :
    0 ≤ (peterssonInnerCosets f f).re := by
  rw [peterssonInnerCosets_def, Complex.re_sum]
  refine Finset.sum_nonneg fun q _ ↦ ?_
  obtain ⟨r, hr, heq⟩ := peterssonInnerCosets_summand_nonneg f q
  rw [heq, Complex.ofReal_re]
  exact hr

/-- The self-pairing is real: its imaginary part vanishes, by Hermitian symmetry. -/
@[simp]
theorem peterssonInnerCosets_self_im (f : CuspForm (Γ.map (mapGL ℝ)) k) :
    (peterssonInnerCosets f f).im = 0 :=
  Complex.conj_eq_iff_im.mp (peterssonInnerCosets_conj_symm f f)

/-- The self-pairing vanishes exactly on the zero form. -/
@[simp]
theorem peterssonInnerCosets_self_eq_zero (f : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets f f = 0 ↔ f = 0 :=
  ⟨peterssonInnerCosets_definite f, fun h ↦ by rw [h]; exact peterssonInnerCosets_zero_left 0⟩

/-- The Petersson pairing bundled as an `InnerProductSpace.Core` on `S_k(Γ)`: the Hermitian
interface behind Mathlib's inner-product, norm, orthogonality and adjoint APIs, which the
adjoint theory consumes. Evaluation is `peterssonInnerCosetsCore_inner`.

Unlike the level-one `peterssonInnerCore`, this one does integrate over a fundamental domain
for the group in question, so it is the genuine Petersson product of `Γ`. It is still a
plain `def` rather than an instance, following the same convention: consumers name it
explicitly, and no `InnerProductSpace` instance is derived from it. The
`@[instance_reducible]` attribute is required by Lean's class-definition reducibility linter
for any `def` of class type. -/
@[instance_reducible]
noncomputable def peterssonInnerCosetsCore :
    InnerProductSpace.Core ℂ (CuspForm (Γ.map (mapGL ℝ)) k) where
  inner := peterssonInnerCosets
  conj_inner_symm := peterssonInnerCosets_conj_symm
  re_inner_nonneg := peterssonInnerCosets_self_re_nonneg
  add_left := peterssonInnerCosets_add_left
  smul_left f g c := peterssonInnerCosets_smul_left c f g
  definite := peterssonInnerCosets_definite

/-- Evaluation of the bundled core: its inner product is `peterssonInnerCosets`. -/
@[simp]
theorem peterssonInnerCosetsCore_inner
    (f g : CuspForm (Γ.map (mapGL ℝ)) k) :
    (peterssonInnerCosetsCore :
        InnerProductSpace.Core ℂ (CuspForm (Γ.map (mapGL ℝ)) k)).inner f g =
      peterssonInnerCosets f g := (rfl)

end CuspForm
