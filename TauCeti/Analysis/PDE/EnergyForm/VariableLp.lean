/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.SymmetricEnergy
public import TauCeti.MeasureTheory.Function.Lp.BilinearForm

/-!
# Variable-coefficient energy forms on `L²` jets

Lane D, item 16 of the PDE roadmap asks for the bounded bilinear form associated to a
divergence-form operator.  `TauCeti.Analysis.PDE.EnergyForm.Lp` treats constant coefficients;
this file supplies the variable-coefficient construction.  An essentially bounded field of
pointwise continuous bilinear forms acts by Hölder multiplication

`L∞(X; J →L J →L ℝ) × L²(X; J) → L²(X; J →L ℝ)`,

and the result pairs with a second `L²` jet.  Both operations are Mathlib's
`ContinuousLinearMap.holderL` and `ContinuousLinearMap.lpPairing`.

For PDE coefficients `a`, `b`, and `c`, the pointwise form is
`energyIntegrand (a x) (b x) (c x)`.  Requiring this field to belong to `L∞` is the precise
boundedness and measurability hypothesis needed by the construction.  The resulting form is
bundled and continuous, so later Sobolev value-gradient jets can feed it without carrying
integrability proofs at each use site.

## Main declarations

* `TauCeti.PDE.energyFormLpVariable`: the variable-coefficient divergence-form energy form.
* `TauCeti.PDE.energyFormLpVariable_apply`: its characterization by the expected energy
  integral.

No formal source is vendored.  The construction directly composes Mathlib's Hölder map and
`Lᵖ` pairing from `Mathlib.MeasureTheory.Function.Holder`.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open ENNReal MeasureTheory

variable {X : Type*} [MeasurableSpace X]

section Energy

open Matrix

variable {n : Type*} [Fintype n]

/-- The variable-coefficient divergence-form energy form on square-integrable value-gradient
jets.

The `MemLp ... ⊤ μ` argument records exactly that the pointwise energy forms are strongly
measurable and essentially bounded.  Its proof is irrelevant to the resulting form. -/
noncomputable def energyFormLpVariable (μ : Measure X) (a : X → Matrix n n ℝ)
    (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ μ) :
    Lp (ℝ × EuclideanSpace ℝ n) 2 μ →L[ℝ]
      Lp (ℝ × EuclideanSpace ℝ n) 2 μ →L[ℝ] ℝ :=
  lpBilinearForm μ (hcoeff.toLp (fun x => energyIntegrand (a x) (b x) (c x)))

/-- The variable-coefficient `L²` energy form is the integral of the pointwise jet energy
density. -/
@[simp]
theorem energyFormLpVariable_apply (μ : Measure X) (a : X → Matrix n n ℝ)
    (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ μ)
    (U V : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLpVariable μ a b c hcoeff U V =
      ∫ x, energyIntegrand (a x) (b x) (c x) (U x) (V x) ∂μ := by
  rw [energyFormLpVariable, lpBilinearForm_apply]
  apply integral_congr_ae
  have hcoe :
      (hcoeff.toLp (fun x => energyIntegrand (a x) (b x) (c x)) :
        X → ℝ × EuclideanSpace ℝ n →L[ℝ] ℝ × EuclideanSpace ℝ n →L[ℝ] ℝ) =ᵐ[μ]
          fun x => energyIntegrand (a x) (b x) (c x) := hcoeff.coeFn_toLp
  filter_upwards [hcoe] with x hx
  rw [hx]

/-- The variable-coefficient energy form is independent of the proof that its coefficient
field belongs to `L∞`. -/
theorem energyFormLpVariable_proof_irrel (μ : Measure X) (a : X → Matrix n n ℝ)
    (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
    (hcoeff hcoeff' : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ μ) :
    energyFormLpVariable μ a b c hcoeff = energyFormLpVariable μ a b c hcoeff' := by
  congr

/-- Almost-everywhere equal coefficient fields induce the same variable-coefficient energy
form. -/
theorem energyFormLpVariable_congr_ae {μ : Measure X}
    {a a' : X → Matrix n n ℝ} {b b' : X → EuclideanSpace ℝ n} {c c' : X → ℝ}
    (ha : a =ᵐ[μ] a') (hb : b =ᵐ[μ] b') (hc : c =ᵐ[μ] c')
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ μ)
    (hcoeff' : MemLp (fun x => energyIntegrand (a' x) (b' x) (c' x)) ⊤ μ) :
    energyFormLpVariable μ a b c hcoeff = energyFormLpVariable μ a' b' c' hcoeff' := by
  ext U V
  rw [energyFormLpVariable_apply, energyFormLpVariable_apply]
  apply integral_congr_ae
  filter_upwards [ha, hb, hc] with x hax hbx hcx
  rw [hax, hbx, hcx]

/-- Transposing the principal coefficient swaps the arguments of a variable zero-drift energy
form. -/
theorem energyFormLpVariable_zero_drift_transpose_apply (μ : Measure X)
    (a : X → Matrix n n ℝ) (c : X → ℝ)
    (hcoeff : MemLp (fun x => energyIntegrand (a x)ᵀ 0 (c x)) ⊤ μ)
    (hcoeff' : MemLp (fun x => energyIntegrand (a x) 0 (c x)) ⊤ μ)
    (U V : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLpVariable μ (fun x => (a x)ᵀ) (fun _ => 0) c hcoeff U V =
      energyFormLpVariable μ a (fun _ => 0) c hcoeff' V U := by
  rw [energyFormLpVariable_apply, energyFormLpVariable_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    energyIntegrand_zero_drift_transpose_apply (a x) (c x) (U x) (V x)

/-- An a.e. symmetric principal coefficient gives a symmetric variable zero-drift energy
form. -/
theorem energyFormLpVariable_zero_drift_comm_of_isSymm_ae {μ : Measure X}
    {a : X → Matrix n n ℝ} (ha : ∀ᵐ x ∂μ, (a x).IsSymm) (c : X → ℝ)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 (c x)) ⊤ μ)
    (U V : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLpVariable μ a (fun _ => 0) c hcoeff U V =
      energyFormLpVariable μ a (fun _ => 0) c hcoeff V U := by
  rw [energyFormLpVariable_apply, energyFormLpVariable_apply]
  apply integral_congr_ae
  filter_upwards [ha] with x hx
  exact energyIntegrand_zero_drift_comm_of_isSymm hx (c x) (U x) (V x)

/-- An a.e. symmetric principal coefficient makes the variable zero-drift energy form equal
to its flip. -/
@[simp]
theorem energyFormLpVariable_zero_drift_flip_eq_of_isSymm_ae {μ : Measure X}
    {a : X → Matrix n n ℝ} (ha : ∀ᵐ x ∂μ, (a x).IsSymm) (c : X → ℝ)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 (c x)) ⊤ μ) :
    (energyFormLpVariable μ a (fun _ => 0) c hcoeff).flip =
      energyFormLpVariable μ a (fun _ => 0) c hcoeff := by
  ext U V
  exact energyFormLpVariable_zero_drift_comm_of_isSymm_ae ha c hcoeff V U

/-- Replacing the principal coefficient by its symmetric part does not change the diagonal
variable energy form. -/
theorem energyFormLpVariable_coefficientSymmetricPart_self (μ : Measure X)
    (a : X → Matrix n n ℝ) (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
    (hcoeff : MemLp (fun x => energyIntegrand (coefficientSymmetricPart (a x))
      (b x) (c x)) ⊤ μ)
    (hcoeff' : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ μ)
    (U : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLpVariable μ (fun x => coefficientSymmetricPart (a x)) b c hcoeff U U =
      energyFormLpVariable μ a b c hcoeff' U U := by
  rw [energyFormLpVariable_apply, energyFormLpVariable_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    energyIntegrand_coefficientSymmetricPart_self (a x) (b x) (c x) (U x)

/-- The symmetric-part variable zero-drift energy form is the average of the original form and
its transpose. -/
theorem energyFormLpVariable_coefficientSymmetricPart_zero_drift_apply (μ : Measure X)
    (a : X → Matrix n n ℝ) (c : X → ℝ)
    (hsymm : MemLp (fun x => energyIntegrand (coefficientSymmetricPart (a x)) 0
      (c x)) ⊤ μ)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 (c x)) ⊤ μ)
    (U V : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLpVariable μ (fun x => coefficientSymmetricPart (a x))
        (fun _ => 0) c hsymm U V =
      (energyFormLpVariable μ a (fun _ => 0) c hcoeff U V +
        energyFormLpVariable μ a (fun _ => 0) c hcoeff V U) / 2 := by
  rw [energyFormLpVariable_apply, energyFormLpVariable_apply,
    energyFormLpVariable_apply]
  have hUV : Integrable (fun x => energyIntegrand (a x) 0 (c x) (U x) (V x)) μ :=
    integrable_bilinear_apply_of_memLp hcoeff U V
  have hVU : Integrable (fun x => energyIntegrand (a x) 0 (c x) (V x) (U x)) μ :=
    integrable_bilinear_apply_of_memLp hcoeff V U
  rw [← integral_add hUV hVU, ← integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    energyIntegrand_coefficientSymmetricPart_zero_drift_apply (a x) (c x) (U x) (V x)

/-- The symmetric-part variable zero-drift energy form is symmetric. -/
theorem energyFormLpVariable_coefficientSymmetricPart_zero_drift_comm (μ : Measure X)
    (a : X → Matrix n n ℝ) (c : X → ℝ)
    (hcoeff : MemLp (fun x => energyIntegrand (coefficientSymmetricPart (a x)) 0
      (c x)) ⊤ μ)
    (U V : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLpVariable μ (fun x => coefficientSymmetricPart (a x))
        (fun _ => 0) c hcoeff U V =
      energyFormLpVariable μ (fun x => coefficientSymmetricPart (a x))
        (fun _ => 0) c hcoeff V U :=
  energyFormLpVariable_zero_drift_comm_of_isSymm_ae
    (Filter.Eventually.of_forall fun _ => coefficientSymmetricPart_isSymm _) c hcoeff U V

/-- The symmetric-part variable zero-drift energy form is equal to its flip. -/
@[simp]
theorem energyFormLpVariable_coefficientSymmetricPart_zero_drift_flip_eq (μ : Measure X)
    (a : X → Matrix n n ℝ) (c : X → ℝ)
    (hcoeff : MemLp (fun x => energyIntegrand (coefficientSymmetricPart (a x)) 0
      (c x)) ⊤ μ) :
    (energyFormLpVariable μ (fun x => coefficientSymmetricPart (a x))
      (fun _ => 0) c hcoeff).flip =
      energyFormLpVariable μ (fun x => coefficientSymmetricPart (a x))
        (fun _ => 0) c hcoeff :=
  energyFormLpVariable_zero_drift_flip_eq_of_isSymm_ae
    (Filter.Eventually.of_forall fun _ => coefficientSymmetricPart_isSymm _) c hcoeff

end Energy

end PDE

end TauCeti

end
