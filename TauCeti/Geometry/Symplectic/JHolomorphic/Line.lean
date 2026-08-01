/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Basic

/-!
# The standard complex line as a source for constant-structure `J`-holomorphic maps

This file records the elementary Cauchy--Riemann bookkeeping for maps whose source is the
standard complex line, represented as `ℝ × ℝ` with the almost complex structure
`AlmostComplexStructure.product ℝ`, `(s, t) ↦ (-t, s)`.

For a real-linear map out of this source, complex-linearity says exactly that the image of the
imaginary coordinate vector is `J` applied to the image of the real coordinate vector. Thus the
linear map, and in particular the Frechet derivative of a constant-structure `J`-holomorphic map
from the standard
line, is determined by its `s`-direction.

The final lemmas translate this into the first pointwise area estimate used by the analytic
Heegaard Floer roadmap: under a taming form, the symplectic area of the ordered pair
`(∂s u, ∂t u)` is nonnegative, and it is positive when `∂s u` is nonzero.

This is still pointwise linear algebra, not an integrated energy theory. It is the local
calculus API needed before the holomorphic-curve energy and elliptic estimates in
`TauCetiRoadmap/HeegaardFloer/README.md`, Lane F2.1.

## Main declarations

* `TauCeti.stdComplexLineReal` and `TauCeti.stdComplexLineImag`: the coordinate vectors
  `(1, 0)` and `(0, 1)` in the standard complex line.
* `TauCeti.isComplexLinearMap_stdComplexLine_iff`: complex-linearity out of the standard
  complex line is equivalent to the coordinate Cauchy--Riemann equation
  `F (0, 1) = J (F (1, 0))`.
* `TauCeti.IsComplexLinearMap.apply_stdComplexLineImag`: for a complex-linear map
  `F : ℝ × ℝ →ₗ[ℝ] V`, `F (0, 1) = J (F (1, 0))`.
* `TauCeti.IsComplexLinearMap.apply_stdComplexLine`: such an `F` is determined by
  `F (1, 0)`, via `F (s, t) = s • v + t • J v`.
* `TauCeti.IsConstStructureJHolomorphicAt.fderiv_stdComplexLineImag` and
  `TauCeti.IsConstStructureJHolomorphicAt.fderiv_stdComplexLine_apply`: the corresponding statements
  for
  Frechet derivatives of constant-structure `J`-holomorphic maps.
* `TauCeti.IsComplexLinearMap.symplecticForm_apply_apply_*`: nonnegativity and positivity of
  `ω(F v, F (J v))` for a complex-linear map under tameness.
* `TauCeti.IsComplexLinearMap.symplecticForm_apply_stdComplexLineReal_stdComplexLineImag_*`:
  nonnegativity and positivity of `ω(F ∂s, F ∂t)` under tameness.

The Cauchy--Riemann sign convention matches McDuff--Salamon, *J-holomorphic Curves and
Symplectic Topology*, Section 2.1: `du ∘ j = J ∘ du`.
-/

public section

namespace TauCeti

/-- The real coordinate vector `(1, 0)` in the standard complex line `ℝ × ℝ`. -/
@[expose]
def stdComplexLineReal : ℝ × ℝ :=
  (1, 0)

/-- The imaginary coordinate vector `(0, 1)` in the standard complex line `ℝ × ℝ`. -/
@[expose]
def stdComplexLineImag : ℝ × ℝ :=
  (0, 1)

@[simp]
lemma stdComplexLineReal_fst : stdComplexLineReal.1 = 1 :=
  rfl

@[simp]
lemma stdComplexLineReal_snd : stdComplexLineReal.2 = 0 :=
  rfl

@[simp]
lemma stdComplexLineImag_fst : stdComplexLineImag.1 = 0 :=
  rfl

@[simp]
lemma stdComplexLineImag_snd : stdComplexLineImag.2 = 1 :=
  rfl

@[simp]
lemma AlmostComplexStructure.product_apply_stdComplexLineReal :
    AlmostComplexStructure.product ℝ stdComplexLineReal = stdComplexLineImag :=
  by
    ext <;> simp [stdComplexLineReal, stdComplexLineImag]

@[simp]
lemma AlmostComplexStructure.product_apply_stdComplexLineImag :
    AlmostComplexStructure.product ℝ stdComplexLineImag = -stdComplexLineReal := by
  ext <;> simp [stdComplexLineReal, stdComplexLineImag]

/-- Every vector in `ℝ × ℝ` decomposes in the standard real and imaginary coordinate vectors. -/
lemma stdComplexLine_eq_smul_real_add_smul_imag (z : ℝ × ℝ) :
    z = z.1 • stdComplexLineReal + z.2 • stdComplexLineImag := by
  ext <;> simp [stdComplexLineReal, stdComplexLineImag]

section Linear

variable {U : Type*} [AddCommGroup U] [Module ℝ U]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {J₀ : AlmostComplexStructure U}
variable {J : AlmostComplexStructure V}

/-- A real-linear map out of `ℝ × ℝ` is determined by its values on the real and imaginary
coordinate vectors. -/
lemma LinearMap.apply_stdComplexLine (F : (ℝ × ℝ) →ₗ[ℝ] V) (z : ℝ × ℝ) :
    F z = z.1 • F stdComplexLineReal + z.2 • F stdComplexLineImag := by
  calc
    F z = F (z.1 • stdComplexLineReal + z.2 • stdComplexLineImag) := by
      rw [← stdComplexLine_eq_smul_real_add_smul_imag z]
    _ = z.1 • F stdComplexLineReal + z.2 • F stdComplexLineImag := by
      rw [map_add, map_smul, map_smul]

/-- Complex-linearity for a real-linear map out of the standard complex line is exactly the
coordinate Cauchy--Riemann equation `F(0,1) = J(F(1,0))`. -/
lemma isComplexLinearMap_stdComplexLine_iff (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F ↔
      F stdComplexLineImag = J (F stdComplexLineReal) := by
  constructor
  · intro hF
    simpa [stdComplexLineImag] using
      (isComplexLinearMap_iff_apply (AlmostComplexStructure.product ℝ) J F).mp hF
        stdComplexLineReal
  · intro hF
    rw [isComplexLinearMap_iff_apply]
    intro z
    calc
      F (AlmostComplexStructure.product ℝ z) =
          (-z.2) • F stdComplexLineReal + z.1 • F stdComplexLineImag := by
        rw [LinearMap.apply_stdComplexLine]
        simp [AlmostComplexStructure.product_apply]
      _ = (-z.2) • F stdComplexLineReal + z.1 • J (F stdComplexLineReal) := by
        rw [hF]
      _ = J (z.1 • F stdComplexLineReal + z.2 • F stdComplexLineImag) := by
        rw [hF]
        simp [map_add, map_smul, smul_neg, add_comm]
      _ = J (F z) := by
        exact congrArg J (LinearMap.apply_stdComplexLine F z).symm

namespace IsComplexLinearMap

variable {F₀ : U →ₗ[ℝ] V}
variable {ω : SymplecticForm V}

/-- Under tameness, the pointwise symplectic area of a complex-linear image of `(v, J₀ v)` is
nonnegative. -/
lemma symplecticForm_apply_apply_nonneg (hF : IsComplexLinearMap J₀ J F₀) (hω : ω.Tames J) (v : U) :
    0 ≤ ω (F₀ v) (F₀ (J₀ v)) := by
  rw [(isComplexLinearMap_iff_apply J₀ J F₀).mp hF v]
  rcases eq_or_ne (F₀ v) 0 with hzero | hne
  · simp [hzero]
  · exact (hω (F₀ v) hne).le

/-- Under tameness, the pointwise symplectic area of a complex-linear image of `(v, J₀ v)` is
positive when the image of `v` is nonzero. -/
lemma symplecticForm_apply_apply_pos (hF : IsComplexLinearMap J₀ J F₀) (hω : ω.Tames J)
    {v : U} (hv : F₀ v ≠ 0) :
    0 < ω (F₀ v) (F₀ (J₀ v)) := by
  rw [(isComplexLinearMap_iff_apply J₀ J F₀).mp hF v]
  exact hω (F₀ v) hv

variable {F : (ℝ × ℝ) →ₗ[ℝ] V}

/-- A real-linear map out of the standard complex line is complex-linear when it satisfies the
coordinate Cauchy--Riemann equation `F(0,1) = J(F(1,0))`. -/
lemma of_apply_stdComplexLineImag (hF : F stdComplexLineImag = J (F stdComplexLineReal)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F :=
  (isComplexLinearMap_stdComplexLine_iff F).mpr hF

/-- For a complex-linear map from the standard complex line, the imaginary coordinate derivative
is `J` applied to the real coordinate derivative. -/
lemma apply_stdComplexLineImag (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    F stdComplexLineImag = J (F stdComplexLineReal) :=
  (isComplexLinearMap_stdComplexLine_iff F).mp hF

/-- The real coordinate derivative is `-J` applied to the imaginary coordinate derivative. -/
lemma apply_stdComplexLineReal (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    F stdComplexLineReal = -J (F stdComplexLineImag) := by
  rw [hF.apply_stdComplexLineImag]
  simp

/-- A complex-linear map out of the standard complex line is determined by its real-coordinate
value: `F (s, t) = s • F(1,0) + t • J(F(1,0))`. -/
lemma apply_stdComplexLine
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) (z : ℝ × ℝ) :
    F z = z.1 • F stdComplexLineReal + z.2 • J (F stdComplexLineReal) := by
  rw [LinearMap.apply_stdComplexLine F z, hF.apply_stdComplexLineImag]

/-- A complex-linear map from the standard complex line is zero exactly when its real-coordinate
value is zero. -/
@[simp]
lemma eq_zero_iff_apply_stdComplexLineReal
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    F = 0 ↔ F stdComplexLineReal = 0 := by
  constructor
  · intro h
    simp [h]
  · intro hreal
    apply LinearMap.ext
    intro z
    rw [hF.apply_stdComplexLine z, hreal]
    simp

/-- The real-coordinate value of a nonzero complex-linear map from the standard complex line is
nonzero. -/
lemma apply_stdComplexLineReal_ne_zero
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) (hFne : F ≠ 0) :
    F stdComplexLineReal ≠ 0 := by
  exact fun hreal => hFne ((hF.eq_zero_iff_apply_stdComplexLineReal).mpr hreal)

variable {ω : SymplecticForm V}

/-- Under tameness, the pointwise symplectic area of a complex-linear image of the standard
oriented coordinate pair is nonnegative. -/
lemma symplecticForm_apply_stdComplexLineReal_stdComplexLineImag_nonneg
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) (hω : ω.Tames J) :
    0 ≤ ω (F stdComplexLineReal) (F stdComplexLineImag) := by
  simpa [AlmostComplexStructure.product_apply_stdComplexLineReal, stdComplexLineImag] using
    hF.symplecticForm_apply_apply_nonneg hω stdComplexLineReal

/-- Under tameness, the pointwise symplectic area of a complex-linear image of the standard
oriented coordinate pair is positive if the real-coordinate image is nonzero. -/
lemma symplecticForm_apply_stdComplexLineReal_stdComplexLineImag_pos
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) (hω : ω.Tames J)
    (hreal : F stdComplexLineReal ≠ 0) :
    0 < ω (F stdComplexLineReal) (F stdComplexLineImag) := by
  simpa [AlmostComplexStructure.product_apply_stdComplexLineReal, stdComplexLineImag] using
    hF.symplecticForm_apply_apply_pos hω hreal

end IsComplexLinearMap

end Linear

namespace IsConstStructureJHolomorphicAt

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {J' : AlmostComplexStructure W} {f : ℝ × ℝ → W} {x z : ℝ × ℝ}

/-- For a constant-structure `J`-holomorphic map from the standard complex line, the Frechet
derivative in the
imaginary coordinate direction is `J` applied to the derivative in the real coordinate direction. -/
lemma fderiv_stdComplexLineImag
    (hf : IsConstStructureJHolomorphicAt (AlmostComplexStructure.product ℝ) J' f x) :
    fderiv ℝ f x stdComplexLineImag = J' (fderiv ℝ f x stdComplexLineReal) := by
  simpa [stdComplexLineImag] using hf.fderiv_apply_commute (v := stdComplexLineReal)

/-- The Frechet derivative of a constant-structure `J`-holomorphic map from the standard complex
line is determined
by its real-coordinate value. -/
lemma fderiv_stdComplexLine_apply
    (hf : IsConstStructureJHolomorphicAt (AlmostComplexStructure.product ℝ) J' f x) (z : ℝ × ℝ) :
    fderiv ℝ f x z =
      z.1 • fderiv ℝ f x stdComplexLineReal +
        z.2 • J' (fderiv ℝ f x stdComplexLineReal) := by
  exact hf.fderiv_isComplexLinear.apply_stdComplexLine z

end IsConstStructureJHolomorphicAt

namespace IsConstStructureJHolomorphicWithinAt

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {J' : AlmostComplexStructure W} {f : ℝ × ℝ → W} {s : Set (ℝ × ℝ)} {x : ℝ × ℝ}

/-- For a within-set constant-structure `J`-holomorphic map from the standard complex line, the
Frechet derivative
within the set sends the imaginary coordinate direction to `J` applied to the real direction,
provided derivatives within the set are unique. -/
lemma fderivWithin_stdComplexLineImag
    (hf : IsConstStructureJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J' f s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ f s x stdComplexLineImag =
      J' (fderivWithin ℝ f s x stdComplexLineReal) := by
  simpa [stdComplexLineImag] using hf.fderivWithin_apply_commute hs (v := stdComplexLineReal)

/-- The within-set Frechet derivative of a constant-structure `J`-holomorphic map from the standard
complex line is
determined by its real-coordinate value when derivatives within the set are unique. -/
lemma fderivWithin_stdComplexLine_apply
    (hf : IsConstStructureJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J' f s x)
    (hs : UniqueDiffWithinAt ℝ s x) (z : ℝ × ℝ) :
    fderivWithin ℝ f s x z =
      z.1 • fderivWithin ℝ f s x stdComplexLineReal +
        z.2 • J' (fderivWithin ℝ f s x stdComplexLineReal) := by
  exact (hf.fderivWithin_isComplexLinear hs).apply_stdComplexLine z

end IsConstStructureJHolomorphicWithinAt

end TauCeti
