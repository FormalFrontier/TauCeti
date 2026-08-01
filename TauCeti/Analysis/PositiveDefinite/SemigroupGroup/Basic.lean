/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.Function.Kernel
public import TauCeti.Analysis.PositiveDefinite.Kernel.Basic
public import TauCeti.Analysis.PositiveDefinite.Kernel.Closure
public import Mathlib.Data.NNReal.Basic

/-!
# Positive-definite functions on `[0, ∞) × V`

This file records the Berg--Christensen--Ressel semigroup-group positive-definiteness predicate
for functions on `ℝ≥0 × V`. For an additive group `V`, the intended involution is
`(t, v) ↦ (t, -v)`, so the finite quadratic forms use the entries
`F (tᵢ + tⱼ, vᵢ - vⱼ)`.

The generic positive-definite-function predicate already captures the finite quadratic-form
condition. Here we name its BCR specialization by using the local wrapper `BCRPoint V`, whose
involution is `(t, v) ↦ (t, -v)`, rather than installing a global negation `StarAddMonoid`
instance on every additive group `V`, which would conflict with Mathlib's ordinary star
conventions. The result is the named hypothesis needed for the BCR Laplace--Fourier
representation target in the `OneParameterSemigroups` roadmap.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Objects: the roadmap asks
for `IsSemigroupGroupPD` as the positive-definite predicate on `ℝ≥0 × V` with involution
`(t, a)⋆ = (t, -a)`.

## Main declarations

* `TauCeti.IsSemigroupGroupPD`: the BCR positive-definiteness predicate on `ℝ≥0 × V`.
* `TauCeti.isSemigroupGroupPD_iff_isPositiveDefiniteKernel`: the bridge to the associated
  positive-definite kernel.
* `TauCeti.isSemigroupGroupPD_iff`: the finite quadratic-form characterization.
* `TauCeti.IsSemigroupGroupPD.conj_symm`, diagonal, and origin lemmas: basic consequences of the
  semigroup-group positive-definiteness condition.
* `TauCeti.isSemigroupGroupPD_const_of_nonneg`, `TauCeti.isSemigroupGroupPD_zero`, and
  `TauCeti.isSemigroupGroupPD_one`: basic constant examples.
* `TauCeti.IsSemigroupGroupPD.add`, `TauCeti.IsSemigroupGroupPD.mul`, and finite
  `sum`/`prod`: closure properties inherited from positive-definite kernels.
* `TauCeti.IsSemigroupGroupPD.quadForm_two_nonneg`: the `2 × 2` BCR Hermitian sub-form is
  nonnegative.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open ComplexConjugate
open scoped ComplexOrder
open scoped NNReal

namespace TauCeti

variable {V : Type*} [AddCommGroup V] {F G : ℝ≥0 × V → ℂ}

/-- The additive monoid `ℝ≥0 × V` equipped with the BCR involution `(t, v) ↦ (t, -v)`.

This wrapper avoids installing a global negation `StarAddMonoid` instance on an arbitrary
additive group `V`. -/
private structure BCRPoint (V : Type*) where
  /-- The nonnegative time coordinate. -/
  time : ℝ≥0
  /-- The group coordinate. -/
  point : V

namespace BCRPoint

variable {V : Type*}

/-- Convert a product point to the local BCR wrapper. Internal helper, not part of the public
API. -/
private def ofProd (p : ℝ≥0 × V) : BCRPoint V :=
  ⟨p.1, p.2⟩

/-- Convert a local BCR wrapper back to the product type. Internal helper, not part of the public
API. -/
private def toProd (p : BCRPoint V) : ℝ≥0 × V :=
  (p.time, p.point)

@[ext]
private theorem ext {p q : BCRPoint V} (ht : p.time = q.time) (hv : p.point = q.point) :
    p = q := by
  cases p
  cases q
  simp_all

private instance [AddCommGroup V] : Zero (BCRPoint V) where
  zero := ⟨0, 0⟩

private instance [AddCommGroup V] : Add (BCRPoint V) where
  add p q := ⟨p.time + q.time, p.point + q.point⟩

private instance [AddCommGroup V] : Star (BCRPoint V) where
  star p := ⟨p.time, -p.point⟩

@[simp]
private theorem zero_time [AddCommGroup V] : (0 : BCRPoint V).time = 0 :=
  rfl

@[simp]
private theorem zero_point [AddCommGroup V] : (0 : BCRPoint V).point = 0 :=
  rfl

@[simp]
private theorem add_time [AddCommGroup V] (p q : BCRPoint V) : (p + q).time = p.time + q.time :=
  rfl

@[simp]
private theorem add_point [AddCommGroup V] (p q : BCRPoint V) : (p + q).point = p.point + q.point :=
  rfl

@[simp]
private theorem star_time [AddCommGroup V] (p : BCRPoint V) : (star p).time = p.time :=
  rfl

@[simp]
private theorem star_point [AddCommGroup V] (p : BCRPoint V) : (star p).point = -p.point :=
  rfl

private instance [AddCommGroup V] : AddCommMonoid (BCRPoint V) where
  add := (· + ·)
  zero := 0
  add_assoc := by
    intro a b c
    ext <;> simp [add_assoc]
  zero_add := by
    intro a
    ext <;> simp
  add_zero := by
    intro a
    ext <;> simp
  add_comm := by
    intro a b
    ext <;> simp [add_comm]
  nsmul := nsmulRec

private instance [AddCommGroup V] : StarAddMonoid (BCRPoint V) where
  star_add := by
    intro p q
    ext <;> simp [add_comm]
  star_involutive := by
    intro p
    ext <;> simp

end BCRPoint

/-- A function on `ℝ≥0 × V` is semigroup-group positive definite, in the
Berg--Christensen--Ressel sense, if all finite quadratic forms formed using the involution
`(t, v) ↦ (t, -v)` are nonnegative:
`∑ᵢⱼ cᵢ conj(cⱼ) F(tᵢ + tⱼ, vᵢ - vⱼ) ≥ 0`. -/
def IsSemigroupGroupPD (F : ℝ≥0 × V → ℂ) : Prop :=
  IsPositiveDefinite fun p : BCRPoint V => F (p.time, p.point)

/-- The bridge from semigroup-group positive definiteness to the associated positive-definite
kernel. -/
theorem isSemigroupGroupPD_iff_isPositiveDefiniteKernel :
    IsSemigroupGroupPD F ↔
      IsPositiveDefiniteKernel fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2) := by
  constructor
  · intro hF
    have hK := IsPositiveDefinite.isPositiveDefiniteKernel hF
    have hK' := isPositiveDefiniteKernel_comp hK (fun p : ℝ≥0 × V => BCRPoint.ofProd p)
    simpa [BCRPoint.ofProd, sub_eq_add_neg] using hK'
  · intro hK
    refine IsPositiveDefinite.of_isPositiveDefiniteKernel ?_
    have hK' := isPositiveDefiniteKernel_comp hK (fun p : BCRPoint V => BCRPoint.toProd p)
    simpa [BCRPoint.toProd, sub_eq_add_neg] using hK'

/-- The kernel associated to a semigroup-group positive-definite function is positive definite. -/
theorem IsSemigroupGroupPD.isPositiveDefiniteKernel (hF : IsSemigroupGroupPD F) :
    IsPositiveDefiniteKernel fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2) :=
  isSemigroupGroupPD_iff_isPositiveDefiniteKernel.mp hF

/-- Build a semigroup-group positive-definite function from the associated positive-definite
kernel. -/
theorem IsSemigroupGroupPD.of_isPositiveDefiniteKernel
    (hF : IsPositiveDefiniteKernel fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2)) :
    IsSemigroupGroupPD F :=
  isSemigroupGroupPD_iff_isPositiveDefiniteKernel.mpr hF

/-- A nonnegative complex constant is semigroup-group positive definite. -/
theorem isSemigroupGroupPD_const_of_nonneg {k : ℂ} (hk : 0 ≤ k) :
    IsSemigroupGroupPD (fun _ : ℝ≥0 × V => k) :=
  IsSemigroupGroupPD.of_isPositiveDefiniteKernel <| by
    simpa using isPositiveDefiniteKernel_const_of_nonneg (α := ℝ≥0 × V) hk

/-- The zero function is semigroup-group positive definite. -/
theorem isSemigroupGroupPD_zero :
    IsSemigroupGroupPD (fun _ : ℝ≥0 × V => (0 : ℂ)) :=
  isSemigroupGroupPD_const_of_nonneg le_rfl

/-- The constant-one function is semigroup-group positive definite. -/
theorem isSemigroupGroupPD_one :
    IsSemigroupGroupPD (fun _ : ℝ≥0 × V => (1 : ℂ)) :=
  isSemigroupGroupPD_const_of_nonneg zero_le_one

/-- The finite quadratic-form characterization of semigroup-group positive definiteness. -/
theorem isSemigroupGroupPD_iff :
    IsSemigroupGroupPD F ↔
      (∀ p q : ℝ≥0 × V, conj (F (p.1 + q.1, p.2 - q.2))
        = F (q.1 + p.1, q.2 - p.2)) ∧
        ∀ {ι : Type*} [Fintype ι] (c : ι → ℂ) (p : ι → ℝ≥0 × V),
          0 ≤ ∑ i, ∑ j, c i * conj (c j) *
            F ((p i).1 + (p j).1, (p i).2 - (p j).2) := by
  classical
  constructor
  · intro hF
    refine ⟨fun p q => isPositiveDefiniteKernel_conj_symm hF.isPositiveDefiniteKernel p q, ?_⟩
    intro ι _ c p
    have hpos := (isPositiveDefiniteKernel_iff.mp hF.isPositiveDefiniteKernel).2 p
      (fun i => conj (c i))
    simpa only [Complex.conj_conj] using hpos
  · rintro ⟨hsymm, hpos⟩
    exact IsSemigroupGroupPD.of_isPositiveDefiniteKernel <| isPositiveDefiniteKernel_iff.mpr
      ⟨hsymm, fun p x => by
        have h := hpos (fun i => conj (x i)) p
        simpa only [Complex.conj_conj] using h⟩

namespace IsSemigroupGroupPD

/-- Positive-definiteness holds for arbitrary finite BCR families: for every finite family of
scalars `c` and points `p`, the quadratic form
`∑ i, ∑ j, c i * conj (c j) * F ((p i).1 + (p j).1, (p i).2 - (p j).2)` is nonnegative. -/
theorem sum_nonneg (hF : IsSemigroupGroupPD F) {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (p : ι → ℝ≥0 × V) :
    0 ≤ ∑ i, ∑ j, c i * conj (c j) *
      F ((p i).1 + (p j).1, (p i).2 - (p j).2) :=
  (isSemigroupGroupPD_iff.mp hF).2 c p

/-- The `2 × 2` BCR Hermitian sub-form at two points. -/
theorem quadForm_two_nonneg (hF : IsSemigroupGroupPD F) (p q : ℝ≥0 × V) (c₀ c₁ : ℂ) :
    0 ≤ c₀ * conj c₀ * F (p.1 + p.1, p.2 - p.2)
      + c₀ * conj c₁ * F (p.1 + q.1, p.2 - q.2)
      + c₁ * conj c₀ * F (q.1 + p.1, q.2 - p.2)
      + c₁ * conj c₁ * F (q.1 + q.1, q.2 - q.2) := by
  simpa [BCRPoint.ofProd, sub_eq_add_neg] using
    IsPositiveDefinite.quadForm_two_nonneg hF (BCRPoint.ofProd p) (BCRPoint.ofProd q) c₀ c₁

/-- A semigroup-group positive-definite function is conjugate symmetric for the BCR kernel:
`conj (F (t + u, v - w)) = F (u + t, w - v)`. -/
@[simp]
theorem conj_symm (hF : IsSemigroupGroupPD F) (p q : ℝ≥0 × V) :
    conj (F (p.1 + q.1, p.2 - q.2)) = F (q.1 + p.1, q.2 - p.2) :=
  isPositiveDefiniteKernel_conj_symm hF.isPositiveDefiniteKernel p q

/-- Values of a semigroup-group positive-definite function on the time diagonal `(t + t, 0)` are
real and nonnegative. -/
theorem diagonal_nonneg (hF : IsSemigroupGroupPD F) (t : ℝ≥0) : 0 ≤ F (t + t, 0) := by
  simpa using isPositiveDefiniteKernel_apply_self_nonneg hF.isPositiveDefiniteKernel (t, 0)

/-- Values of a semigroup-group positive-definite function on the time diagonal `(t + t, 0)` have
zero imaginary part. -/
@[simp]
theorem diagonal_im (hF : IsSemigroupGroupPD F) (t : ℝ≥0) : (F (t + t, 0)).im = 0 :=
  ((Complex.nonneg_iff.mp (hF.diagonal_nonneg t)).2).symm

/-- The real part of a semigroup-group positive-definite function on the time diagonal
`(t + t, 0)` is nonnegative. -/
theorem diagonal_re_nonneg (hF : IsSemigroupGroupPD F) (t : ℝ≥0) :
    0 ≤ (F (t + t, 0)).re :=
  (Complex.nonneg_iff.mp (hF.diagonal_nonneg t)).1

/-- A semigroup-group positive-definite function on the time diagonal `(t + t, 0)` is equal to
its real part, viewed as a complex number. -/
theorem diagonal_eq_ofReal_re (hF : IsSemigroupGroupPD F) (t : ℝ≥0) :
    F (t + t, 0) = ((F (t + t, 0)).re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using hF.diagonal_im t

/-- The value of a semigroup-group positive-definite function at `(0, 0)` is real and
nonnegative. -/
theorem map_zero_nonneg (hF : IsSemigroupGroupPD F) : 0 ≤ F (0, 0) := by
  simpa using hF.diagonal_nonneg 0

/-- The value of a semigroup-group positive-definite function at `(0, 0)` has zero imaginary
part. -/
@[simp]
theorem map_zero_im (hF : IsSemigroupGroupPD F) : (F (0, 0)).im = 0 :=
  by simpa using hF.diagonal_im 0

/-- The real part of the value of a semigroup-group positive-definite function at `(0, 0)` is
nonnegative. -/
theorem map_zero_re_nonneg (hF : IsSemigroupGroupPD F) : 0 ≤ (F (0, 0)).re :=
  by simpa using hF.diagonal_re_nonneg 0

/-- The value at `(0, 0)` of a semigroup-group positive-definite function is equal to its real
part, viewed as a complex number. -/
theorem map_zero_eq_ofReal_re (hF : IsSemigroupGroupPD F) : F (0, 0) = ((F (0, 0)).re : ℂ) := by
  simpa using hF.diagonal_eq_ofReal_re 0

/-- If a semigroup-group positive-definite function is nonzero at the origin, then the real
part of its value at the origin is strictly positive. -/
theorem map_zero_re_pos_of_ne_zero (hF : IsSemigroupGroupPD F) (h0 : F (0, 0) ≠ 0) :
    0 < (F (0, 0)).re := by
  refine lt_of_le_of_ne hF.map_zero_re_nonneg ?_
  intro hre
  apply h0
  apply Complex.ext
  · exact hre.symm
  · simpa using hF.map_zero_im

/-- Semigroup-group positive-definite functions are closed under addition. -/
theorem add (hF : IsSemigroupGroupPD F) (hG : IsSemigroupGroupPD G) :
    IsSemigroupGroupPD fun x => F x + G x :=
  IsSemigroupGroupPD.of_isPositiveDefiniteKernel <| by
    simpa only [Pi.add_apply] using
      isPositiveDefiniteKernel_add hF.isPositiveDefiniteKernel hG.isPositiveDefiniteKernel

/-- Semigroup-group positive-definite functions are closed under multiplication by a
nonnegative complex scalar. -/
theorem const_mul {k : ℂ} (hk : 0 ≤ k) (hF : IsSemigroupGroupPD F) :
    IsSemigroupGroupPD fun x => k * F x :=
  IsSemigroupGroupPD.of_isPositiveDefiniteKernel <| by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      isPositiveDefiniteKernel_smul_of_nonneg hk hF.isPositiveDefiniteKernel

/-- Semigroup-group positive-definite functions are closed under multiplication by a
nonnegative real scalar. -/
theorem smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) (hF : IsSemigroupGroupPD F) :
    IsSemigroupGroupPD fun x => r • F x :=
  IsSemigroupGroupPD.of_isPositiveDefiniteKernel <|
    isPositiveDefiniteKernel_smul hr hF.isPositiveDefiniteKernel

/-- Semigroup-group positive-definite functions are closed under pointwise multiplication
(Schur product). -/
theorem mul (hF : IsSemigroupGroupPD F) (hG : IsSemigroupGroupPD G) :
    IsSemigroupGroupPD fun x => F x * G x :=
  IsSemigroupGroupPD.of_isPositiveDefiniteKernel <|
    isPositiveDefiniteKernel_mul hF.isPositiveDefiniteKernel hG.isPositiveDefiniteKernel

/-- Semigroup-group positive-definite functions are closed under finite sums. -/
theorem sum {ι : Type*} {s : Finset ι} {F : ι → ℝ≥0 × V → ℂ}
    (hF : ∀ i ∈ s, IsSemigroupGroupPD (F i)) :
    IsSemigroupGroupPD fun x => ∑ i ∈ s, F i x :=
  IsSemigroupGroupPD.of_isPositiveDefiniteKernel <|
    isPositiveDefiniteKernel_sum fun i hi => (hF i hi).isPositiveDefiniteKernel

/-- Semigroup-group positive-definite functions are closed under finite products
(Schur products). -/
theorem prod {ι : Type*} {s : Finset ι} {F : ι → ℝ≥0 × V → ℂ}
    (hF : ∀ i ∈ s, IsSemigroupGroupPD (F i)) :
    IsSemigroupGroupPD fun x => ∏ i ∈ s, F i x :=
  IsSemigroupGroupPD.of_isPositiveDefiniteKernel <|
    isPositiveDefiniteKernel_prod fun i hi => (hF i hi).isPositiveDefiniteKernel

end IsSemigroupGroupPD

end TauCeti
