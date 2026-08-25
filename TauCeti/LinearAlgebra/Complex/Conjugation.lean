/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The real points of a conjugate-linear involution

A **conjugation** of a complex vector space `V` is a conjugate-linear map `K : V → V` with
`K ∘ K = id`, that is, a `starRingEnd ℂ`-semilinear self-map that is involutive.  Its **real
points** are the vectors it fixes.  They form a real subspace `TauCeti.realPoints K`, and the main
theorem of this file is that `V` is the complexification of that subspace: the canonical map

`ℂ ⊗[ℝ] realPoints K → V`, `c ⊗ₜ w ↦ c • w`

is a `ℂ`-linear isomorphism.  Conversely a complexification `ℂ ⊗[ℝ] W` carries the conjugation
`c ⊗ₜ w ↦ conj c ⊗ₜ w`.  So a conjugation on `V` is the same data as a presentation of `V` as the
complexification of a real vector space, which is what makes conjugations the tool for realizing
an object over `ℝ`.

Everything is stated for an arbitrary `V`; no finite-dimensionality is used anywhere.

## Main definitions

* `TauCeti.realPoints`: the real points of a conjugate-linear map, as a `Submodule ℝ V`.
* `TauCeti.conjRealPart` and `TauCeti.conjImagPart`: the two real points a vector decomposes into;
  `TauCeti.conjRealPart_def` and `TauCeti.conjImagPart_def` are their defining formulas.
* `TauCeti.realPointsLift`: the canonical `ℂ`-linear map `ℂ ⊗[ℝ] realPoints K →ₗ[ℂ] V`.
* `TauCeti.realPointsEquiv`: that map as a `ℂ`-linear isomorphism, for involutive `K`.
* `TauCeti.tmulConj`: the conjugation `c ⊗ₜ w ↦ conj c ⊗ₜ w` of a complexification `ℂ ⊗[ℝ] W`.

## Main statements

* `TauCeti.conjRealPart_add_I_smul_conjImagPart`: the decomposition
  `v = conjRealPart K v + I • conjImagPart K v`, which makes `TauCeti.realPointsLift` surjective.
* `TauCeti.realPointsLift_injective`, `TauCeti.realPointsLift_surjective` and
  `TauCeti.realPointsEquiv`: **a complex vector space is the complexification of the real points of
  any conjugation on it.**
* `TauCeti.exists_one_tmul_add_I_tmul`: every element of `ℂ ⊗[ℝ] W` is `1 ⊗ₜ w₁ + I ⊗ₜ w₂`; this
  is what makes the lift injective.
* `TauCeti.tmulConj_involutive`, `TauCeti.tmulConj_tmul` and
  `TauCeti.mem_realPoints_tmulConj_iff`: the conjugation of a complexification and its real
  points.

## Implementation notes

A conjugation is carried here as the two unbundled hypotheses `K : V →ₛₗ[starRingEnd ℂ] V` and
`Function.Involutive K`, rather than as a bundled structure.  `TauCeti.Hodge.Conjugation` already
bundles exactly this data, but it lives downstream in `TauCeti/Geometry/Hodge/`, so bundling here
would either duplicate it or invert the dependency between `TauCeti.LinearAlgebra` and
`TauCeti.Geometry`; a `TauCeti.Hodge.Conjugation` supplies the hypotheses below from its two
fields.  For the same reason `TauCeti.realPoints` asks only for the semilinear map: the subspace
makes sense without involutivity, and only the complexification theorem needs it.

No definition here exposes its body: `TauCeti.mem_realPoints`, `TauCeti.conjRealPart_def`,
`TauCeti.conjImagPart_def`, `TauCeti.realPointsLift_tmul`, `TauCeti.realPointsEquiv_tmul` and
`TauCeti.tmulConj_tmul` are the characterizations a consumer works from.

The real scalar structure on `V` is Mathlib's `Module.complexToReal`, the one `Module ℂ V` induces,
so `r • v` and `(r : ℂ) • v` are definitionally equal and no scalar tower hypothesis is carried.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2, where the
  conjugation attached to an invariant form realizes a representation over `ℝ`.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-! ### The real points of a conjugate-linear map -/

/-- The **real points** of a conjugate-linear map `K : V → V`: the vectors `K` fixes.  They form a
subspace over `ℝ` but not over `ℂ`, since `K (c • v) = conj c • K v`. -/
def realPoints (K : V →ₛₗ[starRingEnd ℂ] V) : Submodule ℝ V where
  carrier := {v | K v = v}
  add_mem' {v w} (hv : K v = v) (hw : K w = w) := by
    rw [Set.mem_ofPred_eq, map_add, hv, hw]
  zero_mem' := map_zero K
  smul_mem' r v (hv : K v = v) := by
    -- `Complex.coe_smul` turns the `ℝ`-action of `Module.complexToReal` into the `ℂ`-action, the
    -- one the semilinearity of `K` speaks about.
    rw [Set.mem_ofPred_eq, ← Complex.coe_smul r, map_smulₛₗ, Complex.conj_ofReal, hv]

@[simp]
theorem mem_realPoints {K : V →ₛₗ[starRingEnd ℂ] V} {v : V} :
    v ∈ realPoints K ↔ K v = v :=
  (Iff.rfl)

variable {K : V →ₛₗ[starRingEnd ℂ] V}

theorem add_conj_mem_realPoints (hK : Function.Involutive K) (v : V) :
    v + K v ∈ realPoints K := by
  rw [mem_realPoints, map_add, hK v, add_comm]

theorem I_smul_sub_conj_mem_realPoints (hK : Function.Involutive K) (v : V) :
    Complex.I • (K v - v) ∈ realPoints K := by
  rw [mem_realPoints, map_smulₛₗ, map_sub, hK v, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]

variable (K) in
/-- The **real part** of `v` relative to a conjugate-linear map: the vector `½ (v + K v)`, a real
point once `K` is involutive (`TauCeti.conjRealPart_mem`). -/
noncomputable def conjRealPart (v : V) : V := (2⁻¹ : ℝ) • (v + K v)

variable (K) in
/-- The **imaginary part** of `v` relative to a conjugate-linear map: the vector
`½ I • (K v - v)`, the coefficient of `I` in `TauCeti.conjRealPart_add_I_smul_conjImagPart`. -/
noncomputable def conjImagPart (v : V) : V := (2⁻¹ : ℝ) • (Complex.I • (K v - v))

/-- The defining formula for the real part, the body of `TauCeti.conjRealPart` not being exposed. -/
theorem conjRealPart_def (v : V) : conjRealPart K v = (2⁻¹ : ℝ) • (v + K v) := (rfl)

/-- The defining formula for the imaginary part, the body of `TauCeti.conjImagPart` not being
exposed. -/
theorem conjImagPart_def (v : V) :
    conjImagPart K v = (2⁻¹ : ℝ) • (Complex.I • (K v - v)) := (rfl)

theorem conjRealPart_mem (hK : Function.Involutive K) (v : V) : conjRealPart K v ∈ realPoints K :=
  Submodule.smul_mem _ _ (add_conj_mem_realPoints hK v)

theorem conjImagPart_mem (hK : Function.Involutive K) (v : V) : conjImagPart K v ∈ realPoints K :=
  Submodule.smul_mem _ _ (I_smul_sub_conj_mem_realPoints hK v)

/-- **The decomposition into real points**: every vector is its real part plus `I` times its
imaginary part.  Once `K` is involutive both summands lie in `TauCeti.realPoints K`, so this is
what exhibits `V` as the complexification of that subspace. -/
theorem conjRealPart_add_I_smul_conjImagPart (v : V) :
    conjRealPart K v + Complex.I • conjImagPart K v = v := by
  have hI : Complex.I • (Complex.I • (K v - v)) = v - K v := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, neg_sub]
  have hsum : (v + K v) + (v - K v) = (2 : ℝ) • v := by
    rw [two_smul]
    abel
  rw [conjRealPart_def, conjImagPart_def, smul_comm Complex.I ((2⁻¹ : ℝ)), hI, ← smul_add, hsum,
    smul_smul]
  norm_num

/-! ### A complexification splits along `1` and `I` -/

/-- **Every element of `ℂ ⊗[ℝ] W` is `1 ⊗ₜ w₁ + I ⊗ₜ w₂`**: writing a complex scalar as
`x + y * I` with `x, y : ℝ` moves its two real coordinates into the second factor.  This is the
splitting `ℂ ⊗[ℝ] W ≅ W ⊕ I · W` in the form the injectivity argument below uses it. -/
theorem exists_one_tmul_add_I_tmul {W : Type*} [AddCommGroup W] [Module ℝ W] (u : ℂ ⊗[ℝ] W) :
    ∃ w₁ w₂ : W, u = 1 ⊗ₜ[ℝ] w₁ + Complex.I ⊗ₜ[ℝ] w₂ := by
  induction u with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul c w =>
    refine ⟨c.re • w, c.im • w, ?_⟩
    rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
    congr 1
    simp only [Complex.real_smul, mul_one]
    exact (Complex.re_add_im c).symm
  | add u₁ u₂ h₁ h₂ =>
    obtain ⟨a₁, b₁, rfl⟩ := h₁
    obtain ⟨a₂, b₂, rfl⟩ := h₂
    exact ⟨a₁ + a₂, b₁ + b₂, by rw [TensorProduct.tmul_add, TensorProduct.tmul_add]; abel⟩

/-! ### The complexification of the real points -/

variable (K) in
/-- The canonical `ℂ`-linear map from the complexification of the real points, `c ⊗ₜ w ↦ c • w`.
`TauCeti.realPointsEquiv` upgrades it to an isomorphism when `K` is involutive. -/
noncomputable def realPointsLift : ℂ ⊗[ℝ] realPoints K →ₗ[ℂ] V :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ (realPoints K →ₗ[ℝ] V) (realPoints K).subtype)

@[simp]
theorem realPointsLift_tmul (c : ℂ) (w : realPoints K) :
    realPointsLift K (c ⊗ₜ[ℝ] w) = c • (w : V) := by
  simp [realPointsLift]

theorem realPointsLift_surjective (hK : Function.Involutive K) :
    Function.Surjective (realPointsLift K) := fun v =>
  ⟨1 ⊗ₜ[ℝ] ⟨conjRealPart K v, conjRealPart_mem hK v⟩ +
      Complex.I ⊗ₜ[ℝ] ⟨conjImagPart K v, conjImagPart_mem hK v⟩, by
    rw [map_add, realPointsLift_tmul, realPointsLift_tmul, one_smul]
    exact conjRealPart_add_I_smul_conjImagPart v⟩

/-- The lift is injective for **any** conjugate-linear `K`: only its surjectivity uses that `K` is
involutive. -/
theorem realPointsLift_injective : Function.Injective (realPointsLift K) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨w₁, w₂, rfl⟩ := exists_one_tmul_add_I_tmul u
  rw [map_add, realPointsLift_tmul, realPointsLift_tmul, one_smul] at hu
  -- Applying `K` flips the sign of the `I`-component, so both components vanish.
  have hconj : (w₁ : V) - Complex.I • (w₂ : V) = 0 := by
    have h := congrArg K hu
    rwa [map_add, map_smulₛₗ, Complex.conj_I, neg_smul, ← sub_eq_add_neg, w₁.2, w₂.2,
      map_zero] at h
  have h₁ : (w₁ : V) = 0 := by
    have h2 : ((w₁ : V) + Complex.I • (w₂ : V)) + ((w₁ : V) - Complex.I • (w₂ : V))
        = (2 : ℂ) • (w₁ : V) := by
      rw [two_smul]
      abel
    rw [hu, hconj, add_zero] at h2
    have := congrArg (fun x : V => (2 : ℂ)⁻¹ • x) h2
    simpa [smul_smul] using this.symm
  have h₂ : (w₂ : V) = 0 := by
    have hI : Complex.I • (w₂ : V) = 0 := by rw [← hu, h₁, zero_add]
    have := congrArg (fun x : V => Complex.I⁻¹ • x) hI
    simpa [smul_smul, inv_mul_cancel₀ Complex.I_ne_zero] using this
  rw [Submodule.coe_eq_zero] at h₁ h₂
  rw [h₁, h₂]
  simp

/-- **A complex vector space is the complexification of the real points of any conjugation on
it.**  The isomorphism is `c ⊗ₜ w ↦ c • w`; surjectivity is the decomposition
`TauCeti.conjRealPart_add_I_smul_conjImagPart`, and injectivity is that a relation `w₁ + I • w₂ = 0`
between real points is killed by adding and subtracting its conjugate. -/
noncomputable def realPointsEquiv (hK : Function.Involutive K) :
    ℂ ⊗[ℝ] realPoints K ≃ₗ[ℂ] V :=
  LinearEquiv.ofBijective (realPointsLift K)
    ⟨realPointsLift_injective, realPointsLift_surjective hK⟩

@[simp]
theorem realPointsEquiv_tmul (hK : Function.Involutive K) (c : ℂ) (w : realPoints K) :
    realPointsEquiv hK (c ⊗ₜ[ℝ] w) = c • (w : V) :=
  realPointsLift_tmul c w

/-! ### The conjugation of a complexification -/

section Complexification

variable (W : Type*) [AddCommGroup W] [Module ℝ W]

/-- The **conjugation of a complexification**: `c ⊗ₜ w ↦ conj c ⊗ₜ w`, conjugate-linear because
conjugation is `ℝ`-linear and multiplicative on `ℂ`.  Together with `TauCeti.realPointsEquiv` it
makes conjugations on `V` and presentations of `V` as a complexification the same data. -/
noncomputable def tmulConj : (ℂ ⊗[ℝ] W) →ₛₗ[starRingEnd ℂ] (ℂ ⊗[ℝ] W) where
  toFun := TensorProduct.lift ((TensorProduct.mk ℝ ℂ W).comp Complex.conjAe.toLinearMap)
  map_add' := map_add _
  map_smul' c u := by
    induction u with
    | zero => simp
    | tmul c' w =>
      simp only [TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.lift.tmul,
        LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
        Complex.conjAe_coe, TensorProduct.mk_apply, map_mul]
    | add u₁ u₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, smul_add]

@[simp]
theorem tmulConj_tmul (c : ℂ) (w : W) :
    tmulConj W (c ⊗ₜ[ℝ] w) = (starRingEnd ℂ) c ⊗ₜ[ℝ] w :=
  (rfl)

theorem tmulConj_involutive : Function.Involutive (tmulConj W) := by
  intro u
  induction u with
  | zero => simp
  | tmul c w => simp
  | add u₁ u₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]

/-- The real points of the conjugation of a complexification are exactly the image of `W`, that
is, the elements `1 ⊗ₜ w`. -/
theorem mem_realPoints_tmulConj_iff (u : ℂ ⊗[ℝ] W) :
    u ∈ realPoints (tmulConj W) ↔ ∃ w : W, u = 1 ⊗ₜ[ℝ] w := by
  refine ⟨fun hu => ?_, ?_⟩
  · obtain ⟨w₁, w₂, rfl⟩ := exists_one_tmul_add_I_tmul u
    rw [mem_realPoints, map_add, tmulConj_tmul, tmulConj_tmul, map_one, Complex.conj_I] at hu
    refine ⟨w₁, ?_⟩
    have hc : -(Complex.I ⊗ₜ[ℝ] w₂) = Complex.I ⊗ₜ[ℝ] w₂ := by
      rw [← TensorProduct.neg_tmul]
      exact add_left_cancel hu
    have h : (2 : ℝ) • (Complex.I ⊗ₜ[ℝ] w₂) = (0 : ℂ ⊗[ℝ] W) := by
      rw [two_smul]
      nth_rewrite 1 [← hc]
      abel
    have h₂ : Complex.I ⊗ₜ[ℝ] w₂ = (0 : ℂ ⊗[ℝ] W) := by
      have := congrArg (fun x : ℂ ⊗[ℝ] W => (2⁻¹ : ℝ) • x) h
      simpa [smul_smul] using this
    rw [h₂, add_zero]
  · rintro ⟨w, rfl⟩
    rw [mem_realPoints, tmulConj_tmul, map_one]

end Complexification

/-- **The conjugation of a complexification commutes with every base-changed map**, because
`LinearMap.baseChange` leaves the conjugated factor alone. -/
theorem tmulConj_baseChange {W W' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W']
    [Module ℝ W'] (f : W →ₗ[ℝ] W') (u : ℂ ⊗[ℝ] W) :
    tmulConj W' (f.baseChange ℂ u) = f.baseChange ℂ (tmulConj W u) := by
  induction u with
  | zero => simp
  | tmul c w => simp
  | add u₁ u₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]

end TauCeti
