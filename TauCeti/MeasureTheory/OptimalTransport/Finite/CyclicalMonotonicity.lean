/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Duality.Certificate
public import TauCeti.MeasureTheory.OptimalTransport.Finite.Duality

/-!
# Cyclical monotonicity of finite optimal transport plans

On finite spaces, Kantorovich duality gives a contact-potential certificate for every optimal
transportation matrix. This file uses the existential complementary-slackness theorem in
`TauCeti.MeasureTheory.OptimalTransport.Finite.Duality` to deduce that the support of every
optimal matrix is `c`-cyclically monotone.

The cost used by the finite linear program is real-valued. The cyclical-monotonicity API uses
extended-nonnegative costs, so the first theorem is stated for a nonnegative real cost. The
second treats a possibly infinite `ℝ≥0∞`-valued cost that is finite on the matrix support, but
its optimality hypothesis is explicitly for the real program obtained with `ENNReal.toReal`.
In that program an infinite cost becomes zero, so it represents optimality for the original
cost only when the cost is everywhere finite.

## Main statements

* `TauCeti.TransportMatrix.isCyclicallyMonotone_toPMF_support_of_forall_cost_le` shows that the
  support of a matrix minimizing a nonnegative real cost is cyclically monotone for the
  corresponding extended-nonnegative cost.
* `TauCeti.TransportMatrix.isCyclicallyMonotone_toPMF_support_of_forall_cost_toReal_le` gives the
  same conclusion for an extended-nonnegative cost finite on the support, when the matrix is
  optimal for the cost after applying `ENNReal.toReal` pointwise.

The converse from cyclical monotonicity alone is not proved here. Its general Polish-space form
is the Schachermayer--Teichmann theorem and requires the contact-potential representation that
remains later in Layer 2 of the optimal-transport roadmap.

## References

* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §1.1.2 and §2.3.
* W. Schachermayer and J. Teichmann, *Characterization of optimal transport plans for the
  Monge--Kantorovich problem*, Proc. Amer. Math. Soc. 137 (2009), 519--529.

This is the finite optimal-support direction of Layer 2, item 7 of the optimal-transport
roadmap.
-/

public section

noncomputable section

open scoped ENNReal

namespace TauCeti

universe u v

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] {μ : PMF ι} {ν : PMF κ}
  {A : TransportMatrix μ ν}

namespace TransportMatrix

/-- **The support of an optimal finite plan is cyclically monotone.** If a transportation
matrix minimizes a nonnegative real cost, the support of its associated probability mass
function is cyclically monotone for the cost embedded in `ℝ≥0∞`. -/
theorem isCyclicallyMonotone_toPMF_support_of_forall_cost_le (A : TransportMatrix μ ν)
    (c : ι × κ → ℝ) (hc : ∀ q, 0 ≤ c q)
    (hA : ∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c) :
    IsCyclicallyMonotone (fun q ↦ ENNReal.ofReal (c q)) A.toPMF.support := by
  obtain ⟨φ, ψ, hfeas, hsupp⟩ :=
    (A.forall_cost_le_iff_exists_forall_add_le_and_support_subset_contactSet c).1 hA
  have hdual : DualFeasible (fun q ↦ ENNReal.ofReal (c q)) φ ψ :=
    (dualFeasible_ofReal_iff hc φ ψ).2 hfeas
  have hsupp' : A.toPMF.support ⊆
      dualContactSet (fun q ↦ ENNReal.ofReal (c q)) φ ψ := by
    rwa [dualContactSet_ofReal hc]
  exact hdual.isCyclicallyMonotone_dualContactSet.mono hsupp'

/-- **The finite extended-cost form.** If an extended-nonnegative cost is finite on the support
of a transportation matrix minimizing its real-valued image, then that support is cyclically
monotone for the original cost. Optimality here is for the pointwise `ENNReal.toReal` image,
where an infinite cost has value zero; it is therefore not optimality for the original cost
unless that cost is everywhere finite. -/
theorem isCyclicallyMonotone_toPMF_support_of_forall_cost_toReal_le
    (A : TransportMatrix μ ν) (c : ι × κ → ℝ≥0∞) (hc : ∀ q ∈ A.toPMF.support, c q ≠ ∞)
    (hA : ∀ B : TransportMatrix μ ν,
      A.cost (fun q ↦ (c q).toReal) ≤ B.cost (fun q ↦ (c q).toReal)) :
    IsCyclicallyMonotone c A.toPMF.support := by
  have hmono := A.isCyclicallyMonotone_toPMF_support_of_forall_cost_le
    (fun q ↦ (c q).toReal) (fun q ↦ ENNReal.toReal_nonneg) hA
  refine isCyclicallyMonotone_iff.2 fun n x y hmem σ ↦ ?_
  calc ∑ i, c (x i, y i) = ∑ i, ENNReal.ofReal (c (x i, y i)).toReal :=
        Finset.sum_congr rfl fun i _ ↦ (ENNReal.ofReal_toReal (hc _ (hmem i))).symm
    _ ≤ ∑ i, ENNReal.ofReal (c (x i, y (σ i))).toReal := hmono.sum_le n x y hmem σ
    _ ≤ ∑ i, c (x i, y (σ i)) := Finset.sum_le_sum fun i _ ↦ ENNReal.ofReal_toReal_le

end TransportMatrix

end TauCeti

end

end
