/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex

/-!
# The Petersson product under a slash, and the fundamental-domain form of the product

Slashing by `α ∈ GL(2, ℝ)` of positive determinant moves the Petersson integrand along the
Möbius action, and the invariant measure of `ℍ` does not see that motion. Writing
`D = det α > 0`, Mathlib's `UpperHalfPlane.petersson_slash` reads

```text
petersson k (f ∣[k] α) (h ∣[k] α) τ = D ^ (k - 2) * petersson k f h (α • τ),
```

so integrating over a domain `S` and changing variables gives

```text
⟪f ∣[k] α, h ∣[k] α⟫_S = D ^ (k - 2) * ⟪f, h⟫_{α • S}.
```

Feeding `h ∣[k] α⁻¹` into that identity moves a slash across the pairing, one argument at a
time — the **adjoint formula for a single slash**:

```text
⟪f ∣[k] α, h⟫_S = D ^ (k - 2) * ⟪f, h ∣[k] α⁻¹⟫_{α • S}.
```

This is the change-of-variables step behind the adjoint theory of the Hecke operators
(Diamond–Shurman §5.5, Miyake §4.5), in the shape the change of variables produces. The
classical form uses the main involution `α^ι = (det α) · α⁻¹` in place of `α⁻¹`; the two differ
by the scalar matrix `D · I`, which slashes as multiplication by `D ^ (k - 2)`, so the two
statements carry the same content and the determinant factor above is exactly the scalar the
involution absorbs. Either way it is the analytic input to the Petersson adjoint
`Tₙ* = ⟨n⟩⁻¹Tₙ` of the Hecke operators at indices prime to the level.

The same change of variables identifies the coset sum defining the Petersson product on
`S_k(Γ)` with a *single* integral. Each summand
`⟪f ∣[k] q⁻¹, g ∣[k] q⁻¹⟫_𝒟` is the integral of the unslashed Petersson integrand over the
translate `q⁻¹ • 𝒟`; passing to the open domain `𝒟ᵒ`, which differs from `𝒟` by a null set,
those translates — one for each coset of `Γ·{±I}` — become pairwise *disjoint*. So `⟪f, g⟫` is
the integral of `petersson k f g` over `⋃_q q⁻¹ • 𝒟ᵒ`: the definition by cosets and the
classical definition as an integral over a fundamental domain agree.

## Main results

* `UpperHalfPlane.peterssonInner_smul_set`: the change of variables, `⟪f, h⟫_{α • S}` is the
  integral over `S` of the integrand composed with `α`.
* `UpperHalfPlane.integrableOn_smul_set_iff`: integrability transports along the same
  translation.
* `UpperHalfPlane.peterssonInner_slash_slash_of_det_pos`: a simultaneous slash by a
  positive-determinant `α` rescales the pairing by `(det α) ^ (k - 2)` and translates the
  domain.
* `UpperHalfPlane.peterssonInner_slash_left_of_det_pos` and
  `UpperHalfPlane.peterssonInner_slash_right_of_det_pos`: the adjoint formula, moving a slash
  from one argument of the pairing to the other.
* `UpperHalfPlane.peterssonInner_slash_slash_SL`: the determinant-one case, where the scalar
  disappears and only the domain moves.
* `Subgroup.pairwise_disjoint_smul_fdo_out`: the translates of `𝒟ᵒ` indexed by the cosets of
  `Γ·{±I}` are pairwise disjoint.
* `CuspForm.peterssonInnerCosets_eq_peterssonInner`: the Petersson product of `S_k(Γ)` is the
  integral of `petersson k f g` over the union of those translates.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Sections 5.4 and 5.5.
* Miyake, *Modular forms*, Section 4.5.
-/

public section

noncomputable section

open MeasureTheory UpperHalfPlane ModularGroup

open scoped MatrixGroups ModularForm Pointwise

namespace UpperHalfPlane

variable {k : ℤ} {g : GL (Fin 2) ℝ}

/-! ### Change of variables -/

/-- **The Petersson pairing over a translated domain.** The invariant measure of `ℍ` is
`GL(2, ℝ)`-invariant, so integrating over `α • S` is integrating the composite over `S`. -/
theorem peterssonInner_smul_set (k : ℤ) (g : GL (Fin 2) ℝ) (S : Set ℍ) (f h : ℍ → ℂ) :
    peterssonInner k (g • S) f h = ∫ τ in S, petersson k f h (g • τ) := by
  rw [peterssonInner_def, ← Set.image_smul]
  exact (measurePreserving_smul g volume).setIntegral_image_emb
    (measurableEmbedding_const_smul g) _ S

/-- **Integrability transports along a translation of the domain**, again because the invariant
measure of `ℍ` is `GL(2, ℝ)`-invariant. -/
theorem integrableOn_smul_set_iff (g : GL (Fin 2) ℝ) (S : Set ℍ) (F : ℍ → ℂ) :
    IntegrableOn F (g • S) volume ↔ IntegrableOn (fun τ ↦ F (g • τ)) S volume := by
  rw [← Set.image_smul]
  exact (measurePreserving_smul g volume).integrableOn_image (measurableEmbedding_const_smul g)

/-! ### Slashing by an element of positive determinant -/

/-- **The Petersson integrand of a simultaneously slashed pair**, for a slash of positive
determinant: it is the integrand of the original pair, evaluated at the moved point and scaled
by `(det α) ^ (k - 2)`. This is `UpperHalfPlane.petersson_slash` with the absolute value and the
twist `σ` resolved. -/
theorem petersson_slash_of_det_pos (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (f h : ℍ → ℂ) (τ : ℍ) :
    petersson k (f ∣[k] g) (h ∣[k] g) τ =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2) * petersson k f h (g • τ) := by
  simp [petersson_slash, σ_eq_refl_of_det_pos hg, abs_of_pos hg]

/-- **A simultaneous slash rescales the Petersson pairing and translates its domain**:
`⟪f ∣[k] α, h ∣[k] α⟫_S = (det α) ^ (k - 2) · ⟪f, h⟫_{α • S}`.

No integrability hypothesis is needed: both sides are the same set integral after the change of
variables, and `MeasureTheory.integral` is defined (as `0`) even where it fails to converge. -/
theorem peterssonInner_slash_slash_of_det_pos (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (S : Set ℍ) (f h : ℍ → ℂ) :
    peterssonInner k S (f ∣[k] g) (h ∣[k] g) =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2) * peterssonInner k (g • S) f h := by
  rw [peterssonInner_smul_set, peterssonInner_def]
  simp_rw [petersson_slash_of_det_pos hg]
  exact MeasureTheory.integral_const_mul _ _

/-- **The adjoint of a slash, on the left argument**:
`⟪f ∣[k] α, h⟫_S = (det α) ^ (k - 2) · ⟪f, h ∣[k] α⁻¹⟫_{α • S}` for `α` of positive determinant.

The classical statement uses the main involution `α^ι = (det α) · α⁻¹` in place of `α⁻¹`;
slashing by the scalar matrix `(det α) · I` is multiplication by `(det α) ^ (k - 2)`, which is
precisely the factor carried here. -/
theorem peterssonInner_slash_left_of_det_pos (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (S : Set ℍ) (f h : ℍ → ℂ) :
    peterssonInner k S (f ∣[k] g) h =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2) *
        peterssonInner k (g • S) f (h ∣[k] g⁻¹) := by
  have hslash := peterssonInner_slash_slash_of_det_pos (k := k) hg S f (h ∣[k] g⁻¹)
  rwa [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one] at hslash

/-- **The adjoint of a slash, on the right argument**:
`⟪f, h ∣[k] α⟫_S = (det α) ^ (k - 2) · ⟪f ∣[k] α⁻¹, h⟫_{α • S}`. The mirror of
`peterssonInner_slash_left_of_det_pos`, with the same proof. -/
theorem peterssonInner_slash_right_of_det_pos (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (S : Set ℍ) (f h : ℍ → ℂ) :
    peterssonInner k S f (h ∣[k] g) =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2) *
        peterssonInner k (g • S) (f ∣[k] g⁻¹) h := by
  have hslash := peterssonInner_slash_slash_of_det_pos (k := k) hg S (f ∣[k] g⁻¹) h
  rwa [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one] at hslash

/-! ### Slashing by an element of `SL(2, ℤ)` -/

/-- **A simultaneous slash by `SL(2, ℤ)` only translates the domain of the Petersson pairing**:
the determinant is `1`, so the scalar of `peterssonInner_slash_slash_of_det_pos` disappears.
Mathlib's `UpperHalfPlane.petersson_slash_SL` already records the determinant-free pointwise
identity, so the proof is the change of variables alone. -/
theorem peterssonInner_slash_slash_SL (k : ℤ) (γ : SL(2, ℤ)) (S : Set ℍ) (f h : ℍ → ℂ) :
    peterssonInner k S (f ∣[k] γ) (h ∣[k] γ) = peterssonInner k (γ • S) f h := by
  rw [sl_smul_set, peterssonInner_smul_set, peterssonInner_def]
  simp_rw [petersson_slash_SL, sl_moeb]

end UpperHalfPlane

/-! ### The Petersson product as an integral over a fundamental domain -/

namespace Subgroup

/-- **The translates of `𝒟ᵒ` indexed by the cosets of `Γ·{±I}` are pairwise disjoint.** By
`ModularGroup.disjoint_smul_fdo` it suffices that the chosen representatives of two distinct
cosets differ neither by `1` nor by `−1`; and both `1` and `−1` lie in `Γ·{±I}`, so either
coincidence would identify the two cosets. -/
theorem pairwise_disjoint_smul_fdo_out (Γ : Subgroup SL(2, ℤ)) :
    Pairwise (Function.onFun Disjoint
      fun q : SL(2, ℤ) ⧸ Γ.withCenter ↦ ((q.out)⁻¹ • fdo)) := by
  intro q₁ q₂ hq
  refine disjoint_smul_fdo ?_ ?_ <;> rw [inv_inv] <;> intro h <;> apply hq
  · rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂, mul_inv_eq_one.mp h]
  · have hneg : q₁.out = -q₂.out := by
      rw [mul_inv_eq_iff_eq_mul] at h
      simpa using h
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂, hneg]
    refine QuotientGroup.eq.mpr ?_
    have hcalc : (-q₂.out)⁻¹ * q₂.out = -1 := by rw [← neg_inv, neg_mul, inv_mul_cancel]
    rw [hcalc]
    exact Γ.center_le_withCenter
      (Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl))

end Subgroup

namespace CuspForm

open Matrix.SpecialLinearGroup

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}

/-- **The Petersson integrand of two cusp forms is integrable over every translate of
`𝒟ᵒ`.** Transporting the integral back to `𝒟` turns the integrand into that of the slashed
pair, where the cusp-form bound applies (`UpperHalfPlane.integrableOn_petersson_slash`). -/
theorem integrableOn_petersson_smul_fdo (f g : CuspForm (Γ.map (mapGL ℝ)) k) (γ : SL(2, ℤ)) :
    IntegrableOn (petersson k ⇑f ⇑g) (γ • fdo) volume := by
  refine IntegrableOn.mono_set ?_ (Set.smul_set_mono fdo_subset_fd)
  rw [sl_smul_set, UpperHalfPlane.integrableOn_smul_set_iff]
  refine (UpperHalfPlane.integrableOn_petersson_slash k (Γ.map (mapGL ℝ)) f g γ).congr_fun
    (fun τ _ ↦ ?_) isClosed_fd.measurableSet
  simp only [petersson_slash_SL, sl_moeb]

/-- **The Petersson product of `S_k(Γ)` is a sum of integrals over translates of `𝒟`.** Each
coset summand of `CuspForm.peterssonInnerCosets` slashes both arguments by the same element of
`SL(2, ℤ)`, so `UpperHalfPlane.peterssonInner_slash_slash_SL` strips the slashes at the cost of
moving the domain. -/
theorem peterssonInnerCosets_eq_sum_smul_fd (f g : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets f g =
      ∑ q : SL(2, ℤ) ⧸ Γ.withCenter,
        UpperHalfPlane.peterssonInner k ((q.out)⁻¹ • fd) ⇑f ⇑g := by
  rw [peterssonInnerCosets_def]
  exact Finset.sum_congr rfl fun q _ ↦ UpperHalfPlane.peterssonInner_slash_slash_SL _ _ _ _ _

/-- **The Petersson product of `S_k(Γ)` is the integral over a fundamental domain.** The
translates `q⁻¹ • 𝒟ᵒ`, one for each coset of `Γ·{±I}` in `SL(2, ℤ)`, are open, pairwise
disjoint, and carry an integrable Petersson integrand, so the sum of integrals over them is the
integral over their union. Together with `peterssonInnerCosets_eq_sum_smul_fd` — and the fact
that `𝒟` and `𝒟ᵒ` differ by a null set — this identifies the coset-sum definition of the
Petersson product with the classical definition as an integral over a fundamental domain. -/
theorem peterssonInnerCosets_eq_peterssonInner (f g : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets f g =
      UpperHalfPlane.peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Γ.withCenter, ((q.out)⁻¹ • fdo)) ⇑f ⇑g := by
  rw [UpperHalfPlane.peterssonInner_def, integral_iUnion_fintype
      (fun q ↦ (isOpen_smul_fdo _).measurableSet)
      Γ.pairwise_disjoint_smul_fdo_out
      (fun q ↦ integrableOn_petersson_smul_fdo f g _),
    peterssonInnerCosets_eq_sum_smul_fd]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hae : ((((q.out)⁻¹ : SL(2, ℤ)) • fd : Set ℍ)) =ᵐ[volume]
      (((q.out)⁻¹ : SL(2, ℤ)) • fdo) := by
    rw [sl_smul_set, sl_smul_set]
    exact (MeasureTheory.smul_set_ae_eq _).mpr fd_ae_eq_fdo
  rw [UpperHalfPlane.peterssonInner_congr_set hae, UpperHalfPlane.peterssonInner_def]

end CuspForm
