/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.Fricke.Operator

/-!
# The Fricke operator is an involution up to a scalar

The Fricke matrix squares to the scalar matrix `(-N) • 1`
(`coe_frickeGL_sq` of `TauCeti/NumberTheory/ModularForms/Fricke/Matrix.lean`), and a scalar
matrix acts trivially on `ℍ`. Slashing by `W²` is therefore multiplication by a constant, and
the Fricke operator `W_N` of `TauCeti/NumberTheory/ModularForms/Fricke/Operator.lean` satisfies
`W_N ∘ W_N = c • id` for that constant

`c = N ^ (2 * (k - 1)) * (-N) ^ (-k)`.

The constant is nonzero, so `W_N` is invertible with `W_N⁻¹ = c⁻¹ • W_N`.

## Main definitions

* `TauCeti.frickeScalar`: the constant `c` above.
* `TauCeti.frickeOperatorEquiv`, `TauCeti.frickeOperatorCuspEquiv`: `W_N` bundled as a linear
  automorphism of `M_k(Γ₁(N))` and of `S_k(Γ₁(N))`, with inverse `c⁻¹ • W_N`.

## Main results

* `TauCeti.frickeGL_sq_slash`: slashing by `W²` is multiplication by `frickeScalar N k`.
* `TauCeti.frickeOperator_frickeOperator`: `W_N ∘ W_N = frickeScalar N k • id` on `M_k(Γ₁(N))`.
* `TauCeti.frickeOperatorCusp_frickeOperatorCusp`: the same on `S_k(Γ₁(N))`.
* `TauCeti.frickeOperator_frickeOperator_apply`,
  `TauCeti.frickeOperatorCusp_frickeOperatorCusp_apply`: the pointwise forms of those two, which
  are the `simp`-normal ones.
* `TauCeti.frickeScalar_def`: the defining equation of the constant, for clients that
  cannot unfold it.
* `TauCeti.frickeScalar_eq`: its evaluated form `(-1) ^ k * N ^ (k - 2)`.
* `TauCeti.frickeScalar_ne_zero`: the constant is nonzero, which is what makes `W_N`
  invertible.
* The two-sided inverse laws `W_N ∘ (c⁻¹ • W_N) = id = (c⁻¹ • W_N) ∘ W_N`, on modular and on
  cusp forms, are `private`: they exist only as the `LinearEquiv.ofLinearMap` arguments of the two
  equivalences above, which together with `frickeOperator_frickeOperator` are the public surface.
* `TauCeti.slash_mul_frickeGL`: slashing by `A * W` is `frickeScalar N k •` slashing by
  `A * W⁻¹`. This is the form the character-space transport will consume, where the two Fricke
  factors of a conjugated operator have to be collapsed onto one representative.

## Where the scalar comes from

Weight-`k` slashing by `g` carries the factor `|det g| ^ (k - 1) * denom g z ^ (-k)`. For
`g = W²` the two factors are the two halves of `frickeScalar`: `det W = N` gives
`|det W²| = N ^ 2`, and `W²` being the scalar matrix `(-N) • 1` gives `denom W² z = -N`,
independently of `z`. The remaining ingredient is that `W²` acts trivially on `ℍ`, so the
`f (W² • z)` in the slash is just `f z` — mathlib's `glScalar_smul`.

## Provenance

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/Fricke.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `340875adfb2`, Apache-2.0, Chris Birkbeck), realizing part of Layer 6 of the ModularForms
roadmap.

AINTLIB states these over `ℚ` and pushes to `ℝ` through a `glMap` transport at every step; here,
as already in `Fricke/Operator.lean`, `frickeGL` is read at `ℝ` directly and no transport
appears. That also replaces AINTLIB's hand computation of `W² • z` and `denom (W²) z` from the
matrix entries: over `ℝ` the square is literally a `Matrix.GeneralLinearGroup.scalar`, so
mathlib's `glScalar_smul` and `denom_scalar` apply, and `UpperHalfPlane.σ` is discharged from
positivity of `det W²` rather than from a rational-determinant side condition.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §5.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-- The scalar `c` with `W_N ∘ W_N = c • id`, namely `c = N ^ (2 * (k - 1)) * (-N) ^ (-k)`: the
`|det|` and `denom` factors of the weight-`k` slash by `W² = (-N) • 1`. -/
public noncomputable def frickeScalar (N : ℕ) (k : ℤ) : ℂ :=
  (N : ℂ) ^ (2 * (k - 1)) * (-(N : ℂ)) ^ (-k)

/-- Defining equation for `frickeScalar`. The definition is `public` but is not marked
`@[expose]`, so a downstream module rewrites with this rather than unfolding the body.

Deliberately not `@[simp]`: `frickeScalar N k` is the normal form here, not the expanded product.
Every statement below is phrased in terms of the named constant, and the two factors only need to
be visible inside `frickeGL_sq_slash`, which rewrites with this lemma explicitly. -/
public theorem frickeScalar_def (N : ℕ) (k : ℤ) :
    frickeScalar N k = (N : ℂ) ^ (2 * (k - 1)) * (-(N : ℂ)) ^ (-k) := (rfl)

/-- **The evaluated form of the scalar**, `(-1) ^ k * N ^ (k - 2)`, which is how
`Fricke/Operator.lean` describes it and the form the normalized operator
`𝒲_N = (√N) ^ (2 - k) • (· ∣[k] W)` needs in order to be an involution in even weight.

`[NeZero N]` is load-bearing rather than ambient: at `N = 0`, `k = 2` the two sides differ. -/
public theorem frickeScalar_eq (k : ℤ) :
    frickeScalar N k = (-1) ^ k * (N : ℂ) ^ (k - 2) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hneg : ((-1 : ℂ)) ^ (-k) = (-1 : ℂ) ^ k := by
    rw [zpow_neg]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← two_mul, zpow_mul]
    norm_num
  -- `frickeScalar_def` leaves the sign trapped inside the base of `(-N) ^ (-k)`. Splitting it off
  -- as `-1 * N` is what lets `mul_zpow` separate the two factors, so that `hneg` can turn
  -- `(-1) ^ (-k)` into `(-1) ^ k` and `zpow_add₀` can merge `N ^ (-k)` with `N ^ (2 * (k - 1))`.
  have hsplit : (-(N : ℂ)) = (-1) * (N : ℂ) := by ring
  rw [frickeScalar_def, hsplit, mul_zpow, hneg,
    ← mul_assoc, mul_comm ((N : ℂ) ^ (2 * (k - 1))) ((-1 : ℂ) ^ k), mul_assoc,
    ← zpow_add₀ hN]
  ring_nf

/-- `frickeScalar N k` is nonzero. This is what makes the Fricke operator invertible, with
inverse `(frickeScalar N k)⁻¹ • W_N`; see `frickeOperatorEquiv`. -/
public theorem frickeScalar_ne_zero (k : ℤ) : frickeScalar N k ≠ 0 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  exact mul_ne_zero (zpow_ne_zero _ hN) (zpow_ne_zero _ (neg_ne_zero.mpr hN))

/-- `W² = (-N) • 1` as an element of `GL (Fin 2) ℝ`, in the `Matrix.GeneralLinearGroup.scalar`
form that mathlib's `glScalar_smul` and `denom_scalar` consume. -/
private theorem frickeGL_sq_eq_scalar (hN : (N : ℝ) ≠ 0) : frickeGL ℝ N * frickeGL ℝ N =
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (-(N : ℝ)) (neg_ne_zero.mpr hN)) := by
  ext i j
  rw [← sq, coe_frickeGL_sq]
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.diagonal_apply]

/-- **Slashing by `W²` is multiplication by `frickeScalar N k`.** `W² = (-N) • 1` is a scalar
matrix, so it acts trivially on `ℍ` and has constant `denom`; what is left of the weight-`k`
slash is the constant `|det W²| ^ (k - 1) * (-N) ^ (-k)`. -/
public theorem frickeGL_sq_slash (k : ℤ) (f : ℍ → ℂ) :
    f ∣[k] (frickeGL ℝ N * frickeGL ℝ N) = frickeScalar N k • f := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  set u : ℝˣ := Units.mk0 (-(N : ℝ)) (neg_ne_zero.mpr hN) with hu
  have hdet : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u).det : ℝ) = (N : ℝ) ^ 2 := by
    rw [Matrix.GeneralLinearGroup.det_scalar]
    simp [hu, sq]
  have hpos : 0 < ((Matrix.GeneralLinearGroup.scalar (Fin 2) u).det : ℝ) := by
    rw [hdet]
    exact pow_pos ((Nat.cast_pos (α := ℝ)).mpr (NeZero.pos N)) 2
  have hσ := UpperHalfPlane.σ_eq_refl_of_det_pos hpos
  ext z
  rw [ModularForm.slash_apply, frickeGL_sq_eq_scalar hN, ← hu, hσ, glScalar_smul, denom_scalar,
    hdet, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)]
  push_cast [hu, frickeScalar_def]
  rw [← zpow_natCast (N : ℂ) 2, ← zpow_mul]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.cast_ofNat, Units.val_mk0, Complex.ofReal_neg,
    Complex.ofReal_natCast, zpow_neg, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Collapsing a Fricke factor**: slashing by `A * W` is `frickeScalar N k •` slashing by
`A * W⁻¹`, because `A * W = (A * W⁻¹) * W²`. This is the step that lets the two Fricke factors
of a `W`-conjugated operator be replaced by a single one. -/
public theorem slash_mul_frickeGL (k : ℤ) (f : ℍ → ℂ) (A : GL (Fin 2) ℝ) :
    f ∣[k] (A * frickeGL ℝ N) = frickeScalar N k • (f ∣[k] (A * (frickeGL ℝ N)⁻¹)) := by
  have hsplit : A * frickeGL ℝ N = A * (frickeGL ℝ N)⁻¹ * (frickeGL ℝ N * frickeGL ℝ N) := by
    group
  rw [hsplit, SlashAction.slash_mul, frickeGL_sq_slash]

/-- **`W_N ∘ W_N = frickeScalar N k • id` on `M_k(Γ₁(N))`.** Composing the operator with itself
slashes by `W²`, which `frickeGL_sq_slash` identifies with the scalar. -/
public theorem frickeOperator_frickeOperator (k : ℤ) :
    (frickeOperator (N := N) k).comp (frickeOperator (N := N) k) =
      frickeScalar N k • LinearMap.id := by
  ext f z
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, LinearMap.id_coe,
    id_eq, FunLike.coe_smul, Pi.smul_apply]
  rw [coe_frickeOperator, coe_frickeOperator, ← SlashAction.slash_mul, frickeGL_sq_slash,
    Pi.smul_apply]

/-- **`W_N (W_N f) = frickeScalar N k • f`** for a modular form `f`, the pointwise form of
`frickeOperator_frickeOperator`. This, not the composition equality, is the simp-normal form: a
goal mentioning `W_N` at all mentions it applied to a form. -/
@[simp]
public theorem frickeOperator_frickeOperator_apply (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    frickeOperator k (frickeOperator k f) = frickeScalar N k • f :=
  LinearMap.congr_fun (frickeOperator_frickeOperator (N := N) k) f

/-- **`c⁻¹ • W_N` inverts `W_N` on the right** on `M_k(Γ₁(N))`, for `c = frickeScalar N k`. -/
private theorem frickeOperator_comp_smul_frickeOperator (k : ℤ) :
    (frickeOperator (N := N) k).comp ((frickeScalar N k)⁻¹ • frickeOperator (N := N) k) =
      LinearMap.id := by
  rw [LinearMap.comp_smul, frickeOperator_frickeOperator, smul_smul,
    inv_mul_cancel₀ (frickeScalar_ne_zero (N := N) k), one_smul]

/-- **`c⁻¹ • W_N` inverts `W_N` on the left** on `M_k(Γ₁(N))`, for `c = frickeScalar N k`. -/
private theorem smul_frickeOperator_comp_frickeOperator (k : ℤ) :
    ((frickeScalar N k)⁻¹ • frickeOperator (N := N) k).comp (frickeOperator (N := N) k) =
      LinearMap.id := by
  rw [LinearMap.smul_comp, frickeOperator_frickeOperator, smul_smul,
    inv_mul_cancel₀ (frickeScalar_ne_zero (N := N) k), one_smul]

/-- **The Fricke operator as a linear automorphism of `M_k(Γ₁(N))`**, with inverse
`(frickeScalar N k)⁻¹ • W_N`. -/
public noncomputable def frickeOperatorEquiv (k : ℤ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k ≃ₗ[ℂ] ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
  LinearEquiv.ofLinearMap (frickeOperator k) ((frickeScalar N k)⁻¹ • frickeOperator k)
    (frickeOperator_comp_smul_frickeOperator k) (smul_frickeOperator_comp_frickeOperator k)

/-- The bundled Fricke operator acts as the Fricke operator. -/
@[simp]
public theorem frickeOperatorEquiv_apply (k : ℤ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    frickeOperatorEquiv (N := N) k f = frickeOperator k f := by
  simp [frickeOperatorEquiv]

/-- The inverse of the bundled Fricke operator is `(frickeScalar N k)⁻¹ • W_N`. -/
@[simp]
public theorem frickeOperatorEquiv_symm_apply (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (frickeOperatorEquiv (N := N) k).symm f = (frickeScalar N k)⁻¹ • frickeOperator k f := by
  simp [frickeOperatorEquiv]

/-- **`W_N ∘ W_N = frickeScalar N k • id` on `S_k(Γ₁(N))`**, the cusp-form form of
`frickeOperator_frickeOperator`. With `frickeScalar_ne_zero` this makes `W_N` invertible on
cusp forms. -/
public theorem frickeOperatorCusp_frickeOperatorCusp (k : ℤ) :
    (frickeOperatorCusp (N := N) k).comp (frickeOperatorCusp (N := N) k) =
      frickeScalar N k • LinearMap.id := by
  -- Descended from the modular-form statement rather than recomputed: cusp forms embed in
  -- modular forms, and `frickeOperator_coe_cuspForm` says the two operators agree under that
  -- embedding, so the slash-by-`W²` computation lives only in `frickeOperator_frickeOperator`.
  ext f z
  have h := DFunLike.congr_fun (LinearMap.congr_fun
    (frickeOperator_frickeOperator (N := N) k)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) z
  simpa [frickeOperator_coe_cuspForm] using h

/-- **`W_N (W_N f) = frickeScalar N k • f`** for a cusp form `f`, the pointwise and simp-normal
form of `frickeOperatorCusp_frickeOperatorCusp`. -/
@[simp]
public theorem frickeOperatorCusp_frickeOperatorCusp_apply (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    frickeOperatorCusp k (frickeOperatorCusp k f) = frickeScalar N k • f :=
  LinearMap.congr_fun (frickeOperatorCusp_frickeOperatorCusp (N := N) k) f

/-- **`c⁻¹ • W_N` inverts `W_N` on the right** on `S_k(Γ₁(N))`, for `c = frickeScalar N k`. -/
private theorem frickeOperatorCusp_comp_smul_frickeOperatorCusp (k : ℤ) :
    (frickeOperatorCusp (N := N) k).comp
        ((frickeScalar N k)⁻¹ • frickeOperatorCusp (N := N) k) = LinearMap.id := by
  rw [LinearMap.comp_smul, frickeOperatorCusp_frickeOperatorCusp, smul_smul,
    inv_mul_cancel₀ (frickeScalar_ne_zero (N := N) k), one_smul]

/-- **`c⁻¹ • W_N` inverts `W_N` on the left** on `S_k(Γ₁(N))`, for `c = frickeScalar N k`. -/
private theorem smul_frickeOperatorCusp_comp_frickeOperatorCusp (k : ℤ) :
    ((frickeScalar N k)⁻¹ • frickeOperatorCusp (N := N) k).comp
        (frickeOperatorCusp (N := N) k) = LinearMap.id := by
  rw [LinearMap.smul_comp, frickeOperatorCusp_frickeOperatorCusp, smul_smul,
    inv_mul_cancel₀ (frickeScalar_ne_zero (N := N) k), one_smul]

/-- **The Fricke operator as a linear automorphism of `S_k(Γ₁(N))`**, with inverse
`(frickeScalar N k)⁻¹ • W_N`. -/
public noncomputable def frickeOperatorCuspEquiv (k : ℤ) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k ≃ₗ[ℂ] CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  LinearEquiv.ofLinearMap (frickeOperatorCusp k) ((frickeScalar N k)⁻¹ • frickeOperatorCusp k)
    (frickeOperatorCusp_comp_smul_frickeOperatorCusp k)
    (smul_frickeOperatorCusp_comp_frickeOperatorCusp k)

/-- The bundled Fricke operator on cusp forms acts as `frickeOperatorCusp`. -/
@[simp]
public theorem frickeOperatorCuspEquiv_apply (k : ℤ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    frickeOperatorCuspEquiv (N := N) k f = frickeOperatorCusp k f := by
  simp [frickeOperatorCuspEquiv]

/-- The inverse of the bundled Fricke operator on cusp forms is
`(frickeScalar N k)⁻¹ • W_N`. -/
@[simp]
public theorem frickeOperatorCuspEquiv_symm_apply (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (frickeOperatorCuspEquiv (N := N) k).symm f =
      (frickeScalar N k)⁻¹ • frickeOperatorCusp k f := by
  simp [frickeOperatorCuspEquiv]

end TauCeti
