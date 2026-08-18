/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Symmetric kernels

A **symmetric kernel** on a measure space `(Ω, μ)` is an honest, everywhere-defined function
`Ω → Ω → ℝ` that is symmetric, jointly measurable, and uniformly bounded. It is the carrier the
dense graph limit theory is built on: a graphon is a `[0, 1]`-valued symmetric kernel, and the cut
norm is defined on kernels rather than on graphons precisely so that a *difference* `U - W` of two
graphons is in its domain.

**Strict, not `AEEqFun`.** The kernel carries a genuine function, not an a.e.-equivalence class.
The a.e. identification is taken once and later, at `GraphonSpace`, rather than being built into the
basic object. Two things follow, and they are why the roadmap makes this choice. First, the strict
kernel is a *pointwise* `ℝ`-module — `(U - W) x y = U x y - W x y` holds on the nose, so cut-norm
estimates never carry a null-set side condition. Second, pointwise hypotheses such as
`∀ x y, W x y ∈ Set.Icc 0 1` are stateable at all, which an a.e. class cannot support without
choosing a representative.

**The measure is a phantom parameter.** `SymmKernel Ω μ` does not mention `μ` in any field: none of
symmetry, measurability, or boundedness refers to it. It is carried in the type so that kernels over
different measures on the same space are not silently interchangeable, and so that later
measure-dependent structure (the cut norm, the `GraphonSpace` quotient) has somewhere to attach.
Consequently the algebra below needs no hypothesis on `μ` at all — in particular not
`IsProbabilityMeasure`.

## Main definitions

* `TauCeti.DenseGraphLimits.SymmKernel` — the strict symmetric kernel structure, with a `FunLike`
  coercion, extensionality by the underlying function, and `symm` / `measurable` / `exists_bound`
  accessors.
* `TauCeti.DenseGraphLimits.SymmKernel.comap` — the pullback of a kernel along a measurable map,
  acting on both arguments.

## Main results

* `AddCommGroup` and `Module ℝ` instances, defined pointwise. The `coe_zero`, `coe_add`, `coe_neg`,
  `coe_sub` and `coe_smul` simp lemmas identify every operation with the corresponding operation on
  `Ω → Ω → ℝ`, so the module structure can be computed entirely by `simp`.
* `comap_apply` evaluates a pullback, and `comap_zero` / `comap_add` / `comap_neg` / `comap_sub` /
  `comap_smul` say that pulling back is linear, so a pullback of a difference of kernels is the
  difference of the pullbacks. `comap_id` and `comap_comap` are the functoriality laws.

## Implementation

Each operation must re-establish all three fields. Symmetry and measurability are immediate.
Boundedness is where the constants are chosen: `C + D` for a sum or difference, `C` for a negation,
and `|c| * C` for a scalar multiple. Since the bound is existential (`∃ C, ∀ x y, |K x y| ≤ C`)
rather than a fixed constant, no sharpness is claimed or needed.

The algebraic instances are then transported along the injective coercion with
`Function.Injective.addCommGroup` and `Function.Injective.module`, which is what makes the pointwise
formulas definitional.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1 — the strict kernel carrier. The
  `Graphon` structure, `cutNorm`, homomorphism densities, and the `L⁰`-to-strict representative
  bridge are separate targets and are not built here.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013).
-/

public section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A **symmetric kernel**: an everywhere-defined symmetric, jointly measurable, uniformly bounded
function `Ω → Ω → ℝ`.

The measure is a phantom parameter — no field mentions it — but it is carried in the type so that
kernels over different measures do not unify, and so that the measure-dependent theory built on top
has somewhere to attach. -/
structure SymmKernel (Ω : Type*) [MeasurableSpace Ω] (_μ : Measure Ω) where
  /-- The underlying function. Use the `FunLike` coercion rather than this field. -/
  toFun : Ω → Ω → ℝ
  /-- The kernel is symmetric. Stated via `SymmKernel.symm`. -/
  symm' : ∀ x y, toFun x y = toFun y x
  /-- The kernel is jointly measurable. Stated via `SymmKernel.measurable`. -/
  meas' : Measurable (Function.uncurry toFun)
  /-- The kernel is uniformly bounded. Stated via `SymmKernel.exists_bound`. -/
  bdd' : ∃ C, ∀ x y, |toFun x y| ≤ C

namespace SymmKernel

instance instFunLike : FunLike (SymmKernel Ω μ) Ω (Ω → ℝ) where
  coe := SymmKernel.toFun
  coe_injective K L h := by cases K; cases L; congr

@[simp]
theorem coe_mk (f : Ω → Ω → ℝ) (hs hm hb) : ⇑(mk f hs hm hb : SymmKernel Ω μ) = f := rfl

@[ext]
theorem ext {K L : SymmKernel Ω μ} (h : ∀ x y, K x y = L x y) : K = L :=
  DFunLike.ext _ _ fun x => funext fun y => h x y

/-- A symmetric kernel is symmetric. -/
theorem symm (K : SymmKernel Ω μ) (x y : Ω) : K x y = K y x := K.symm' x y

/-- A symmetric kernel is jointly measurable. -/
theorem measurable (K : SymmKernel Ω μ) : Measurable (Function.uncurry (K : Ω → Ω → ℝ)) := K.meas'

/-- A symmetric kernel is uniformly bounded. The constant is not canonical. -/
theorem exists_bound (K : SymmKernel Ω μ) : ∃ C, ∀ x y, |K x y| ≤ C := K.bdd'

section Algebra

instance : Zero (SymmKernel Ω μ) :=
  ⟨⟨fun _ _ => 0, fun _ _ => rfl, measurable_const, 0, by simp⟩⟩

instance : Add (SymmKernel Ω μ) :=
  ⟨fun K L => ⟨fun x y => K x y + L x y, fun x y => by rw [K.symm, L.symm],
    by exact K.measurable.add L.measurable,
    by obtain ⟨C, hC⟩ := K.exists_bound; obtain ⟨D, hD⟩ := L.exists_bound
       exact ⟨C + D, fun x y => (abs_add_le _ _).trans (add_le_add (hC x y) (hD x y))⟩⟩⟩

instance : Neg (SymmKernel Ω μ) :=
  ⟨fun K => ⟨fun x y => -K x y, fun x y => by rw [K.symm],
    by exact K.measurable.neg,
    by obtain ⟨C, hC⟩ := K.exists_bound; exact ⟨C, fun x y => by simpa using hC x y⟩⟩⟩

instance : Sub (SymmKernel Ω μ) :=
  ⟨fun K L => ⟨fun x y => K x y - L x y, fun x y => by rw [K.symm, L.symm],
    by exact K.measurable.sub L.measurable,
    by obtain ⟨C, hC⟩ := K.exists_bound; obtain ⟨D, hD⟩ := L.exists_bound
       exact ⟨C + D, fun x y => (abs_sub _ _).trans (add_le_add (hC x y) (hD x y))⟩⟩⟩

instance : SMul ℝ (SymmKernel Ω μ) :=
  ⟨fun c K => ⟨fun x y => c * K x y, fun x y => by rw [K.symm],
    by exact K.measurable.const_mul c,
    by obtain ⟨C, hC⟩ := K.exists_bound
       exact ⟨|c| * C, fun x y => by
         rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC x y) (abs_nonneg c)⟩⟩⟩

instance : SMul ℕ (SymmKernel Ω μ) :=
  ⟨fun n K => ⟨fun x y => n • K x y, fun x y => by rw [K.symm],
    by exact K.measurable.const_smul (n : ℕ),
    by obtain ⟨C, hC⟩ := K.exists_bound
       exact ⟨n * C, fun x y => by
         simpa [abs_mul, nsmul_eq_mul] using
           mul_le_mul_of_nonneg_left (hC x y) (Nat.cast_nonneg (α := ℝ) n)⟩⟩⟩

instance : SMul ℤ (SymmKernel Ω μ) :=
  ⟨fun n K => ⟨fun x y => n • K x y, fun x y => by rw [K.symm],
    by exact K.measurable.const_smul (n : ℤ),
    by obtain ⟨C, hC⟩ := K.exists_bound
       exact ⟨|(n : ℝ)| * C, fun x y => by
         simpa [abs_mul, zsmul_eq_mul] using
           mul_le_mul_of_nonneg_left (hC x y) (abs_nonneg ((n : ℝ)))⟩⟩⟩

@[simp] theorem coe_zero : ⇑(0 : SymmKernel Ω μ) = 0 := rfl

@[simp] theorem coe_add (K L : SymmKernel Ω μ) : ⇑(K + L) = ⇑K + ⇑L := rfl

@[simp] theorem coe_neg (K : SymmKernel Ω μ) : ⇑(-K) = -⇑K := rfl

@[simp] theorem coe_sub (K L : SymmKernel Ω μ) : ⇑(K - L) = ⇑K - ⇑L := rfl

@[simp] theorem coe_smul (c : ℝ) (K : SymmKernel Ω μ) : ⇑(c • K) = c • ⇑K := rfl

@[simp] theorem coe_nsmul (n : ℕ) (K : SymmKernel Ω μ) : ⇑(n • K) = n • ⇑K := rfl

@[simp] theorem coe_zsmul (n : ℤ) (K : SymmKernel Ω μ) : ⇑(n • K) = n • ⇑K := rfl

instance : AddCommGroup (SymmKernel Ω μ) :=
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun K n => coe_nsmul n K) (fun K n => coe_zsmul n K)

instance : Module ℝ (SymmKernel Ω μ) :=
  DFunLike.coe_injective.module ℝ
    ({ toFun := DFunLike.coe, map_zero' := coe_zero, map_add' := coe_add } :
      SymmKernel Ω μ →+ (Ω → Ω → ℝ)) coe_smul

end Algebra

section Comap

variable {Ω' Ω'' : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω'']

/-- The **pullback of a symmetric kernel along a measurable map** `f : Ω' → Ω`, acting on both
arguments: `K.comap μ' hf x y = K (f x) (f y)`.

Symmetry, measurability and boundedness are all inherited from `K`, so no hypothesis beyond
measurability of `f` is needed — and none on either measure, since `μ` and `μ'` are phantom
parameters of the two kernel types. The target measure `μ'` is therefore an explicit argument: it is
not determined by the data.

This is how a kernel on one carrier is read on another. Two uses in the dense graph limit theory:
the **overlaid difference** on a coupling of two carriers is the difference of the two pullbacks
along the coordinate projections, and the measure-preserving-map form of the cut distance compares
pullbacks along maps out of a common carrier. -/
def comap (K : SymmKernel Ω μ) (μ' : Measure Ω') {f : Ω' → Ω} (hf : Measurable f) :
    SymmKernel Ω' μ' where
  toFun x y := K (f x) (f y)
  symm' x y := K.symm (f x) (f y)
  meas' := K.measurable.comp (hf.prodMap hf)
  bdd' := K.exists_bound.imp fun _ hC x y => hC (f x) (f y)

@[simp]
theorem comap_apply (K : SymmKernel Ω μ) (μ' : Measure Ω') {f : Ω' → Ω} (hf : Measurable f)
    (x y : Ω') : K.comap μ' hf x y = K (f x) (f y) := (rfl)

@[simp]
theorem comap_zero (μ' : Measure Ω') {f : Ω' → Ω} (hf : Measurable f) :
    (0 : SymmKernel Ω μ).comap μ' hf = 0 := by ext; simp

@[simp]
theorem comap_add (K L : SymmKernel Ω μ) (μ' : Measure Ω') {f : Ω' → Ω} (hf : Measurable f) :
    (K + L).comap μ' hf = K.comap μ' hf + L.comap μ' hf := by ext; simp

@[simp]
theorem comap_neg (K : SymmKernel Ω μ) (μ' : Measure Ω') {f : Ω' → Ω} (hf : Measurable f) :
    (-K).comap μ' hf = -K.comap μ' hf := by ext; simp

@[simp]
theorem comap_sub (K L : SymmKernel Ω μ) (μ' : Measure Ω') {f : Ω' → Ω} (hf : Measurable f) :
    (K - L).comap μ' hf = K.comap μ' hf - L.comap μ' hf := by ext; simp

@[simp]
theorem comap_smul (c : ℝ) (K : SymmKernel Ω μ) (μ' : Measure Ω') {f : Ω' → Ω}
    (hf : Measurable f) : (c • K).comap μ' hf = c • K.comap μ' hf := by ext; simp

/-- Pulling back along the identity is the identity. -/
@[simp]
theorem comap_id (K : SymmKernel Ω μ) : K.comap μ measurable_id = K := by
  ext; simp

/-- Pullbacks compose contravariantly. -/
theorem comap_comap (K : SymmKernel Ω μ) (μ' : Measure Ω') (μ'' : Measure Ω'') {f : Ω' → Ω}
    (hf : Measurable f) {g : Ω'' → Ω'} (hg : Measurable g) :
    (K.comap μ' hf).comap μ'' hg = K.comap μ'' (hf.comp hg) := by ext; simp

end Comap

end SymmKernel

end DenseGraphLimits

end TauCeti
