/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex

/-!
# The Petersson product under a slash and as an integral over translated domains

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
the integral of `petersson k f g` over `⋃_q q⁻¹ • 𝒟ᵒ`. This file does not formalize that this
union is itself a fundamental domain for `Γ`.

## Main results

* `UpperHalfPlane.peterssonInner_slash_slash_of_det_pos`: a simultaneous slash by a
  positive-determinant `α` rescales the pairing by `(det α) ^ (k - 2)` and translates the
  domain.
* `UpperHalfPlane.peterssonInner_slash_left_of_det_pos` and
  `UpperHalfPlane.peterssonInner_slash_right_of_det_pos`: the adjoint formula, moving a slash
  from one argument of the pairing to the other.
* `UpperHalfPlane.peterssonInner_slash_slash_SL`: the determinant-one case, where the scalar
  disappears and only the domain moves.
* `CuspForm.peterssonInnerCosets_eq_sum_smul_fd`: the coset pairing is a sum of integrals over
  translates of `𝒟`.
* `CuspForm.peterssonInnerCosets_eq_peterssonInner`: that sum is the single integral of
  `petersson k f g` over the union of the corresponding translates of `𝒟ᵒ`.

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

/-! ### Slashing by an element of positive determinant -/

/-- **A simultaneous slash rescales the Petersson pairing and translates its domain**:
`⟪f ∣[k] α, h ∣[k] α⟫_S = (det α) ^ (k - 2) · ⟪f, h⟫_{α • S}`.

No integrability hypothesis is needed: both sides are the same set integral after the change of
variables, and `MeasureTheory.integral` is defined (as `0`) even where it fails to converge. -/
theorem peterssonInner_slash_slash_of_det_pos (k : ℤ)
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (S : Set ℍ) (f h : ℍ → ℂ) :
    peterssonInner k S (f ∣[k] g) (h ∣[k] g) =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2) * peterssonInner k (g • S) f h := by
  rw [peterssonInner_def, peterssonInner_def, ← Set.image_smul,
    (measurePreserving_smul g volume).setIntegral_image_emb
      (measurableEmbedding_const_smul g)]
  simp_rw [petersson_slash]
  simp only [σ_eq_refl_of_det_pos hg, ContinuousAlgEquiv.refl_apply,
    Matrix.GeneralLinearGroup.val_det_apply, abs_of_pos hg]
  exact MeasureTheory.integral_const_mul _ _

/-- **The adjoint of a slash, on the left argument**:
`⟪f ∣[k] α, h⟫_S = (det α) ^ (k - 2) · ⟪f, h ∣[k] α⁻¹⟫_{α • S}` for `α` of positive determinant.

The classical statement uses the main involution `α^ι = (det α) · α⁻¹` in place of `α⁻¹`;
slashing by the scalar matrix `(det α) · I` is multiplication by `(det α) ^ (k - 2)`, which is
precisely the factor carried here. -/
theorem peterssonInner_slash_left_of_det_pos (k : ℤ)
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (S : Set ℍ) (f h : ℍ → ℂ) :
    peterssonInner k S (f ∣[k] g) h =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2) *
        peterssonInner k (g • S) f (h ∣[k] g⁻¹) := by
  have hslash := peterssonInner_slash_slash_of_det_pos k hg S f (h ∣[k] g⁻¹)
  rwa [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one] at hslash

/-- **The adjoint of a slash, on the right argument**:
`⟪f, h ∣[k] α⟫_S = (det α) ^ (k - 2) · ⟪f ∣[k] α⁻¹, h⟫_{α • S}`. The mirror of
`peterssonInner_slash_left_of_det_pos`, with the same proof. -/
theorem peterssonInner_slash_right_of_det_pos (k : ℤ)
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (S : Set ℍ) (f h : ℍ → ℂ) :
    peterssonInner k S f (h ∣[k] g) =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 2) *
        peterssonInner k (g • S) (f ∣[k] g⁻¹) h := by
  have hslash := peterssonInner_slash_slash_of_det_pos k hg S (f ∣[k] g⁻¹) h
  rwa [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one] at hslash

/-! ### Slashing by an element of `SL(2, ℤ)` -/

/-- **A simultaneous slash by `SL(2, ℤ)` only translates the domain of the Petersson pairing**:
the determinant is `1`, so the scalar of `peterssonInner_slash_slash_of_det_pos` disappears. -/
theorem peterssonInner_slash_slash_SL (k : ℤ) (γ : SL(2, ℤ)) (S : Set ℍ) (f h : ℍ → ℂ) :
    peterssonInner k S (f ∣[k] γ) (h ∣[k] γ) = peterssonInner k (γ • S) f h := by
  have hdet_eq : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det) = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact congrArg Units.val (Matrix.SpecialLinearGroup.det_mapGL γ)
  have hdet : 0 < (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det) :=
    det_pos_of_mem_slGL (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)
  simpa only [ModularForm.SL_slash, hdet_eq, Complex.ofReal_one, one_zpow, one_mul,
    sl_smul_set] using peterssonInner_slash_slash_of_det_pos
      (g := (γ : GL (Fin 2) ℝ)) k hdet S f h

end UpperHalfPlane

/-! ### The Petersson product as an integral over a union of translated domains -/

namespace CuspForm

open Matrix.SpecialLinearGroup

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}

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

/-- **The Petersson product of `S_k(Γ)` is a single integral over a union of translates.** The
sets `q⁻¹ • 𝒟ᵒ`, one for each coset of `Γ·{±I}` in `SL(2, ℤ)`, are open and pairwise disjoint,
and carry an integrable Petersson integrand, so the sum of integrals over them is the integral
over their union. This theorem does not assert that the union is a fundamental domain for
`Γ`. -/
theorem peterssonInnerCosets_eq_peterssonInner (f g : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets f g =
      UpperHalfPlane.peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Γ.withCenter, ((q.out)⁻¹ • fdo)) ⇑f ⇑g := by
  rw [UpperHalfPlane.peterssonInner_def, integral_iUnion_fintype
      (fun q ↦ (isOpen_smul_fdo _).measurableSet)
      (ModularGroup.pairwise_disjoint_smul_fdo_out_withCenter Γ)
      (fun q ↦ (UpperHalfPlane.integrableOn_petersson_sl_smul_fd_left
        k (Γ.map (mapGL ℝ)) f g _).mono_set (Set.smul_set_mono fdo_subset_fd)),
    peterssonInnerCosets_eq_sum_smul_fd]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hae : ((((q.out)⁻¹ : SL(2, ℤ)) • fd : Set ℍ)) =ᵐ[volume]
      (((q.out)⁻¹ : SL(2, ℤ)) • fdo) := by
    rw [ModularGroup.sl_smul_set, ModularGroup.sl_smul_set]
    exact (MeasureTheory.smul_set_ae_eq _).mpr fd_ae_eq_fdo
  rw [UpperHalfPlane.peterssonInner_congr_set hae, UpperHalfPlane.peterssonInner_def]

end CuspForm
