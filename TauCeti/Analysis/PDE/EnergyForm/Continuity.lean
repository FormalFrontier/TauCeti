/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Linearity

/-!
# Continuity of pointwise PDE energy integrands in the coefficients

The finite-dimensional weak-form integrand
`energyIntegrand A b c` is linear in the principal, drift, and mass coefficients.  This file
bundles that linearity as continuous linear maps from coefficient spaces to spaces of
continuous bilinear maps.

This is a pointwise prerequisite for Lane D of the PDE roadmap.  Once the weak energy form is
defined by integrating `x ↦ energyIntegrand (a x) (b x) (c x)` over a domain, continuous
coefficient fields and continuous perturbation families should give continuous integrand
families without unfolding the jet form.

## Main declarations

* `TauCeti.PDE.energyIntegrandLinear`: the full coefficient triple-to-integrand map as a
  continuous linear map.
* `TauCeti.PDE.continuous_energyIntegrand`: continuity of the unbundled full integrand map.
* `Continuous.energyIntegrand` and `ContinuousOn.energyIntegrand`: composition lemmas for
  coefficient fields.
-/

public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {X n : Type*} [Fintype n]

/-- The coefficient triple-to-energy-integrand map as a continuous linear map. -/
noncomputable def energyIntegrandLinear : (Matrix n n ℝ × EuclideanSpace ℝ n × ℝ) →L[ℝ]
      (ℝ × EuclideanSpace ℝ n) →L[ℝ] (ℝ × EuclideanSpace ℝ n) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => energyIntegrand p.1 p.2.1 p.2.2
      map_add' := by
        rintro ⟨A, b, c⟩ ⟨B, d, e⟩
        apply ContinuousLinearMap.ext
        intro U
        apply ContinuousLinearMap.ext
        intro V
        exact energyIntegrand_add_apply A B b d c e U V
      map_smul' := by
        rintro r ⟨A, b, c⟩
        apply ContinuousLinearMap.ext
        intro U
        apply ContinuousLinearMap.ext
        intro V
        exact energyIntegrand_smul_apply A b c r U V }

/-- Applying `energyIntegrandLinear` recovers `energyIntegrand` for the coefficient triple. -/
@[simp]
lemma energyIntegrandLinear_apply (A : Matrix n n ℝ) (b : EuclideanSpace ℝ n) (c : ℝ) :
    energyIntegrandLinear (n := n) (A, b, c) = energyIntegrand A b c :=
  by
    apply ContinuousLinearMap.ext
    rintro ⟨u, η⟩
    apply ContinuousLinearMap.ext
    rintro ⟨v, ξ⟩
    simp [energyIntegrandLinear]

/-- The full coefficient triple-to-energy-integrand map is continuous. -/
lemma continuous_energyIntegrand :
    Continuous (fun p : Matrix n n ℝ × EuclideanSpace ℝ n × ℝ =>
      energyIntegrand p.1 p.2.1 p.2.2) :=
  (energyIntegrandLinear (n := n)).continuous.congr fun p =>
    energyIntegrandLinear_apply p.1 p.2.1 p.2.2

variable [TopologicalSpace X]

namespace Continuous

/-- Continuous coefficient fields give a continuous field of full pointwise energy
integrands. -/
lemma energyIntegrand {a : X → Matrix n n ℝ} {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous (fun x => PDE.energyIntegrand (a x) (b x) (c x)) :=
  continuous_energyIntegrand.comp (ha.prodMk (hb.prodMk hc))

end Continuous

namespace ContinuousOn

/-- Continuous coefficient fields on a set give a continuous field of full pointwise energy
integrands on that set. -/
lemma energyIntegrand {s : Set X} {a : X → Matrix n n ℝ} {b : X → EuclideanSpace ℝ n}
    {c : X → ℝ} (ha : ContinuousOn a s) (hb : ContinuousOn b s) (hc : ContinuousOn c s) :
    ContinuousOn (fun x => PDE.energyIntegrand (a x) (b x) (c x)) s :=
  continuous_energyIntegrand.comp_continuousOn (ha.prodMk (hb.prodMk hc))

end ContinuousOn

end PDE

end TauCeti
