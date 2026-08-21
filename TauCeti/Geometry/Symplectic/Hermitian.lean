/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic

/-!
# The Hermitian inner product of a compatible pair

A symplectic form `ω` compatible with an almost complex structure `J` packages the real metric
`g(v, w) = ω(v, J w)` and the symplectic form into a single complex Hermitian inner product
```
h(v, w) = g(v, w) + i ω(v, w) = ω(v, J w) + i ω(v, w)
```
on the complex vector space `(V, J)` (the complex structure of `ComplexModule.lean`, where
multiplication by `i` is `J`). This is the classical statement that a compatible triple
`(ω, J, g)` is the same data as a Hermitian structure (McDuff--Salamon, *J-holomorphic Curves and
Symplectic Topology*, Section 2.1): the real and imaginary parts of `h` recover the
metric and the symplectic form, `h` is conjugate-symmetric, it is complex linear in the second
argument over the `J`-induced complex structure, and it is positive definite.

This is the complex companion of `TauCeti.SymplecticForm.Compatible.innerProductCore`, which
records the real metric `g` of the same pair as an `InnerProductSpace.Core ℝ V`. Here the complex
form is built once, as `SymplecticForm.complexAssociatedForm`, and the Hermitian-structure facts
are proved under
the weakest hypothesis each one needs: conjugate symmetry and conjugate-linearity in the first
argument need only `ω.Invariant J`, while positive definiteness needs only `ω.Tames J`.
Compatibility (`Invariant` plus `Tames`) is what assembles all of them into the capstone
`Compatible.hermitianCore`, exhibiting `h` as an `InnerProductSpace.Core ℂ V` for the complex
structure `J.complexModule`.

## Main declarations

* `TauCeti.SymplecticForm.complexAssociatedForm`: the complex form
  `h(v, w) = ω(v, J w) + i ω(v, w)`.
* `TauCeti.SymplecticForm.complexAssociatedForm_re` / `complexAssociatedForm_im`: the real and
  imaginary parts of `h` are the metric `g(v, w) = ω(v, J w)` and the symplectic form `ω(v, w)`.
* `TauCeti.SymplecticForm.Invariant.complexAssociatedForm_conj_symm`: `h` is conjugate-symmetric,
  `conj (h(w, v)) = h(v, w)`, needing only `J`-invariance.
* `TauCeti.SymplecticForm.complexAssociatedForm_smul_right`: `h` is complex linear in its second
  argument, `h(v, z • w) = z · h(v, w)`, for the complex structure `J.complexModule` (no
  compatibility needed).
* `TauCeti.SymplecticForm.complexAssociatedForm_self`: `h(v, v) = ω(v, J v)`, with
  `TauCeti.SymplecticForm.Tames.complexAssociatedForm_self_re_pos` adding positivity on nonzero
  vectors.
* `TauCeti.SymplecticForm.Compatible.hermitianCore`: the Hermitian inner product of a compatible
  pair as an `InnerProductSpace.Core ℂ V`.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: a compatible pair `(ω, J)` gives the Hermitian form `⟨v, w⟩ = g(v, w) + i ω(v, w)`.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The complex form associated to a pair `(ω, J)`: `h(v, w) = ω(v, J w) + i ω(v, w)`.

Its real part is the metric `ω(·, J ·)` and its imaginary part is the symplectic form `ω`. The
bare definition needs no hypotheses on `(ω, J)`; the Hermitian-structure facts are each proved
under the weakest hypothesis they need: complex linearity in the second argument from `J² = -1`
alone (`complexAssociatedForm_smul_right`), conjugate symmetry and conjugate-linearity in the first
argument from `ω.Invariant J` (`Invariant.complexAssociatedForm_conj_symm`,
`Invariant.complexAssociatedForm_smul_left`), and positive definiteness from `ω.Tames J`
(`Tames.complexAssociatedForm_self_re_pos`). Full compatibility is needed only to assemble
`Compatible.hermitianCore`. -/
@[expose]
noncomputable def complexAssociatedForm (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (v w : V) : ℂ :=
  (ω v (J w) : ℂ) + Complex.I * (ω v w : ℂ)

@[simp]
lemma complexAssociatedForm_apply (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (v w : V) :
    ω.complexAssociatedForm J v w = (ω v (J w) : ℂ) + Complex.I * (ω v w : ℂ) := rfl

/-- The real part of the complex associated form is the metric `g(v, w) = ω(v, J w)`. -/
lemma complexAssociatedForm_re (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (v w : V) :
    (ω.complexAssociatedForm J v w).re = ω v (J w) := by
  simp [complexAssociatedForm]

/-- The imaginary part of the complex associated form is the symplectic form `ω(v, w)`. -/
lemma complexAssociatedForm_im (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (v w : V) :
    (ω.complexAssociatedForm J v w).im = ω v w := by
  simp [complexAssociatedForm]

/-- The complex associated form is additive in its first argument. -/
lemma complexAssociatedForm_add_left (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (v₁ v₂ w : V) :
    ω.complexAssociatedForm J (v₁ + v₂) w =
      ω.complexAssociatedForm J v₁ w + ω.complexAssociatedForm J v₂ w := by
  simp only [complexAssociatedForm, map_add, LinearMap.add_apply]
  push_cast
  ring

/-- The complex associated form is additive in its second argument. -/
lemma complexAssociatedForm_add_right (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (v w₁ w₂ : V) :
    ω.complexAssociatedForm J v (w₁ + w₂) =
      ω.complexAssociatedForm J v w₁ + ω.complexAssociatedForm J v w₂ := by
  simp only [complexAssociatedForm, map_add]
  push_cast
  ring

/-- Auxiliary real-scalar form of complex linearity in the second argument: feeding the real
decomposition `r.re • w + r.im • J w` of `r • w` to the second slot multiplies by `r`. This needs
only `J² = -1`, not compatibility. -/
private lemma complexAssociatedForm_smul_right_aux
    (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (r : ℂ) (v w : V) :
    ω.complexAssociatedForm J v (r.re • w + r.im • J w) =
      r * ω.complexAssociatedForm J v w := by
  have key1 : ω v (J (r.re • w + r.im • J w)) = r.re * ω v (J w) + r.im * -(ω v w) := by
    simp only [map_add, map_smul, smul_eq_mul, AlmostComplexStructure.apply_apply, map_neg]
  have key2 : ω v (r.re • w + r.im • J w) = r.re * ω v w + r.im * ω v (J w) := by
    simp only [map_add, map_smul, smul_eq_mul]
  simp only [complexAssociatedForm, key1, key2]
  apply Complex.ext <;> simp
  ring

/-- The complex associated form is complex linear in its second argument over the complex structure
`J.complexModule`: `h(v, z • w) = z · h(v, w)`. This is one of the defining properties of a
Hermitian inner product on the complex vector space `(V, J)`, and needs only `J² = -1`, not
compatibility. -/
lemma complexAssociatedForm_smul_right (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (z : ℂ) (v w : V) :
    letI := J.complexModule
    ω.complexAssociatedForm J v (z • w) = z * ω.complexAssociatedForm J v w := by
  let := J.complexModule
  rw [J.complexModule_smul_def]
  exact ω.complexAssociatedForm_smul_right_aux J z v w

/-- The diagonal of the complex associated form is real and equals the metric diagonal
`ω(v, J v)`. -/
lemma complexAssociatedForm_self (ω : SymplecticForm V) (J : AlmostComplexStructure V) (v : V) :
    ω.complexAssociatedForm J v v = (ω v (J v) : ℂ) := by
  simp [complexAssociatedForm]

namespace Tames

variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- The diagonal of the Hermitian form is positive on nonzero vectors. Only tameness is needed. -/
lemma complexAssociatedForm_self_re_pos (htames : ω.Tames J) {v : V} (hv : v ≠ 0) :
    0 < (ω.complexAssociatedForm J v v).re := by
  rw [complexAssociatedForm_re]
  exact htames v hv

/-- The real part of the diagonal of the Hermitian form is nonnegative, in the `RCLike.re` form
the inner-product-space core expects. Only tameness is needed. -/
lemma complexAssociatedForm_self_re_nonneg (htames : ω.Tames J) (v : V) :
    0 ≤ RCLike.re (ω.complexAssociatedForm J v v) := by
  rw [ω.complexAssociatedForm_self]
  simpa using SymplecticForm.symplecticForm_apply_apply_self_nonneg
    ((ω.tames_iff_associated_pos J).mp htames) v

/-- The diagonal of the Hermitian form vanishes exactly at zero. Only tameness is needed. -/
lemma complexAssociatedForm_self_eq_zero (htames : ω.Tames J) {v : V} :
    ω.complexAssociatedForm J v v = 0 ↔ v = 0 := by
  rw [ω.complexAssociatedForm_self, Complex.ofReal_eq_zero, ← associatedBilinForm_apply]
  exact SymplecticForm.associatedBilinForm_self_eq_zero ((ω.tames_iff_associated_pos J).mp htames)

end Tames

namespace Invariant

variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- The Hermitian form is conjugate-symmetric: `conj (h(w, v)) = h(v, w)`. Only `J`-invariance is
needed. -/
lemma complexAssociatedForm_conj_symm (hinv : ω.Invariant J) (v w : V) :
    (starRingEnd ℂ) (ω.complexAssociatedForm J w v) = ω.complexAssociatedForm J v w := by
  have hg : ω w (J v) = ω v (J w) := hinv.associatedBilinForm_apply_swap w v
  have hω : ω w v = -(ω v w) := (ω.neg_eq v w).symm
  simp only [complexAssociatedForm, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, hg, hω]
  push_cast
  ring

/-- Auxiliary real-scalar form of conjugate linearity in the first argument: feeding the real
decomposition `r.re • v + r.im • J v` of `r • v` to the first slot multiplies by `conj r`. Only
`J`-invariance is needed. -/
private lemma complexAssociatedForm_smul_left_aux (hinv : ω.Invariant J) (r : ℂ) (v w : V) :
    ω.complexAssociatedForm J (r.re • v + r.im • J v) w
      = (starRingEnd ℂ) r * ω.complexAssociatedForm J v w := by
  have hJvw : ω (J v) (J w) = ω v w := hinv.apply v w
  have hJv : ω (J v) w = -(ω v (J w)) := by
    have hskew := hinv.associatedBilinForm_skewAdjoint v (J w)
    simp [associatedBilinForm_apply, AlmostComplexStructure.apply_apply] at hskew
    linarith
  have key1 : ω (r.re • v + r.im • J v) (J w) = r.re * ω v (J w) + r.im * ω v w := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hJvw]
  have key2 : ω (r.re • v + r.im • J v) w = r.re * ω v w + r.im * -(ω v (J w)) := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hJv]
  simp only [complexAssociatedForm, key1, key2]
  apply Complex.ext <;> simp

/-- The Hermitian form is conjugate linear in its first argument over the complex structure
`J.complexModule`: `h(z • v, w) = conj z · h(v, w)`. Only `J`-invariance is needed. -/
lemma complexAssociatedForm_smul_left (hinv : ω.Invariant J) (z : ℂ) (v w : V) :
    letI := J.complexModule
    ω.complexAssociatedForm J (z • v) w =
      (starRingEnd ℂ) z * ω.complexAssociatedForm J v w := by
  let := J.complexModule
  rw [J.complexModule_smul_def]
  exact hinv.complexAssociatedForm_smul_left_aux z v w

end Invariant

namespace Compatible

variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- The diagonal of the Hermitian form is positive on nonzero vectors. -/
lemma complexAssociatedForm_self_re_pos (h : ω.Compatible J) {v : V} (hv : v ≠ 0) :
    0 < (ω.complexAssociatedForm J v v).re :=
  h.tames.complexAssociatedForm_self_re_pos hv

/-- The real part of the diagonal of the Hermitian form is nonnegative, in the `RCLike.re` form
the inner-product-space core expects. -/
lemma complexAssociatedForm_self_re_nonneg (h : ω.Compatible J) (v : V) :
    0 ≤ RCLike.re (ω.complexAssociatedForm J v v) :=
  h.tames.complexAssociatedForm_self_re_nonneg v

/-- The diagonal of the Hermitian form vanishes exactly at zero. -/
lemma complexAssociatedForm_self_eq_zero (h : ω.Compatible J) {v : V} :
    ω.complexAssociatedForm J v v = 0 ↔ v = 0 :=
  h.tames.complexAssociatedForm_self_eq_zero

/-- The Hermitian form is conjugate-symmetric: `conj (h(w, v)) = h(v, w)`. -/
lemma complexAssociatedForm_conj_symm (h : ω.Compatible J) (v w : V) :
    (starRingEnd ℂ) (ω.complexAssociatedForm J w v) = ω.complexAssociatedForm J v w :=
  h.invariant.complexAssociatedForm_conj_symm v w

/-- The Hermitian form is conjugate linear in its first argument over the complex structure
`J.complexModule`: `h(z • v, w) = conj z · h(v, w)`. -/
lemma complexAssociatedForm_smul_left (h : ω.Compatible J) (z : ℂ) (v w : V) :
    letI := J.complexModule
    ω.complexAssociatedForm J (z • v) w =
      (starRingEnd ℂ) z * ω.complexAssociatedForm J v w :=
  h.invariant.complexAssociatedForm_smul_left z v w

/-- The Hermitian inner product of a compatible pair, packaged as an `InnerProductSpace.Core ℂ V`
for the complex structure `J.complexModule`.

The inner product is `⟨v, w⟩ = ω(v, J w) + i ω(v, w)`, conjugate linear in the first argument and
complex linear in the second, with `⟨v, v⟩ = ω(v, J v) > 0` for `v ≠ 0`. -/
@[implicit_reducible]
noncomputable def hermitianCore (h : ω.Compatible J) :
    letI := J.complexModule
    InnerProductSpace.Core ℂ V :=
  letI := J.complexModule
  { inner := ω.complexAssociatedForm J
    conj_inner_symm := h.complexAssociatedForm_conj_symm
    re_inner_nonneg := h.complexAssociatedForm_self_re_nonneg
    add_left := ω.complexAssociatedForm_add_left J
    smul_left := fun v w z => h.complexAssociatedForm_smul_left z v w
    definite := fun _ hv => h.complexAssociatedForm_self_eq_zero.mp hv }

/-- The inner product from `hermitianCore` is the Hermitian form `ω(v, J w) + i ω(v, w)`. -/
@[simp]
lemma hermitianCore_inner (h : ω.Compatible J) (v w : V) :
    letI := J.complexModule
    @inner ℂ V h.hermitianCore.toInner v w = (ω v (J w) : ℂ) + Complex.I * (ω v w : ℂ) := by
  -- `hermitianCore` sets `inner := ω.complexAssociatedForm J`; `toInner` projects that field
  -- through the reducible wrapper installed by `InnerProductSpace.Core`.
  change ω.complexAssociatedForm J v w = _
  rw [complexAssociatedForm_apply]

end Compatible

end SymplecticForm

end TauCeti
