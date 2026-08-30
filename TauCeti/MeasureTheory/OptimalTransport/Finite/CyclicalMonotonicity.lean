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
transportation matrix. This file records that existential form of complementary slackness and
deduces that the support of every optimal matrix is `c`-cyclically monotone.

The cost used by the finite linear program is real-valued. The cyclical-monotonicity API uses
extended-nonnegative costs, so the first theorem is stated for a nonnegative real cost and the
second for a finite `ℝ≥0∞`-valued cost, transported through `ENNReal.toReal`. Finiteness is
load-bearing: a real linear program cannot represent a forbidden pair of infinite cost.

## Main statements

* `TauCeti.TransportMatrix.forall_cost_le_iff_exists_support_subset_contactSet` says that a
  transportation matrix minimizes a real cost exactly when some feasible pair of Kantorovich
  potentials is equal to the cost throughout the matrix support.
* `TauCeti.TransportMatrix.isCyclicallyMonotone_toPMF_support_of_forall_cost_le` shows that the
  support of a matrix minimizing a nonnegative real cost is cyclically monotone for the
  corresponding extended-nonnegative cost.
* `TauCeti.TransportMatrix.isCyclicallyMonotone_toPMF_support_of_forall_toReal_cost_le` gives the
  same conclusion directly for a finite extended-nonnegative cost.
* `TauCeti.exists_transportMatrix_isCyclicallyMonotone_toPMF_support` supplies an optimal
  matrix with cyclically monotone support for every nonnegative finite-space cost.

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

/-- A pair belongs to the support of the probability mass function represented by a
transportation matrix exactly when the corresponding matrix entry is nonzero. -/
theorem mem_toPMF_support_iff (A : TransportMatrix μ ν) (q : ι × κ) :
    q ∈ A.toPMF.support ↔ A q.1 q.2 ≠ 0 := by
  rw [PMF.mem_support_iff, A.toPMF_apply]

/-- **Existential complementary slackness for a finite transport plan.** A transportation
matrix minimizes a real cost exactly when there is a dual-feasible pair of potentials whose
contact set contains the support of the matrix.

Unlike `TransportMatrix.forall_cost_le_and_forall_finiteDualValue_le_iff_mem_contactSet`, this
statement does not take a preselected dual optimizer: finite Kantorovich duality supplies one
from primal optimality. -/
theorem forall_cost_le_iff_exists_support_subset_contactSet (A : TransportMatrix μ ν)
    (c : ι × κ → ℝ) :
    (∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c) ↔
      ∃ φ : ι → ℝ, ∃ ψ : κ → ℝ, (∀ i j, φ i + ψ j ≤ c (i, j)) ∧
        A.toPMF.support ⊆ contactSet c (fun i ↦ (φ i : EReal)) (fun j ↦ (ψ j : EReal)) := by
  constructor
  · intro hA
    obtain ⟨B, φ, ψ, hB, hfeas, hB_eq⟩ := exists_cost_eq_finiteDualValue c μ ν
    have hA_eq : A.cost c = finiteDualValue μ ν φ ψ := by
      apply le_antisymm
      · exact (hA B).trans_eq hB_eq
      · exact A.finiteDualValue_le_cost hfeas
    refine ⟨φ, ψ, hfeas, ?_⟩
    intro q hq
    rw [mem_contactSet_iff, ← EReal.coe_add, EReal.coe_eq_coe_iff]
    exact (A.cost_eq_finiteDualValue_iff hfeas).1 hA_eq q.1 q.2
      (A.mem_toPMF_support_iff q |>.1 hq)
  · rintro ⟨φ, ψ, hfeas, hsupp⟩ B
    have hcontact : ∀ i j, A i j ≠ 0 → φ i + ψ j = c (i, j) := by
      intro i j hij
      have hmem := hsupp (A.mem_toPMF_support_iff (i, j) |>.2 hij)
      rw [mem_contactSet_iff, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hmem
      exact hmem
    rw [(A.cost_eq_finiteDualValue_iff hfeas).2 hcontact]
    exact B.finiteDualValue_le_cost hfeas

/-- A finite optimal transportation matrix admits feasible real potentials whose equality set,
viewed through the extended-nonnegative dual interface, contains the support of the plan. -/
theorem exists_support_subset_dualContactSet_of_forall_cost_le (A : TransportMatrix μ ν)
    (c : ι × κ → ℝ) (hc : ∀ q, 0 ≤ c q)
    (hA : ∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c) :
    ∃ φ : ι → ℝ, ∃ ψ : κ → ℝ,
      DualFeasible (fun q ↦ ENNReal.ofReal (c q)) φ ψ ∧
        A.toPMF.support ⊆ dualContactSet (fun q ↦ ENNReal.ofReal (c q)) φ ψ := by
  obtain ⟨φ, ψ, hfeas, hsupp⟩ :=
    (A.forall_cost_le_iff_exists_support_subset_contactSet c).1 hA
  refine ⟨φ, ψ, (dualFeasible_ofReal_iff hc φ ψ).2 hfeas, ?_⟩
  rwa [dualContactSet_ofReal hc]

/-- **The support of an optimal finite plan is cyclically monotone.** If a transportation
matrix minimizes a nonnegative real cost, the support of its associated probability mass
function is cyclically monotone for the cost embedded in `ℝ≥0∞`. -/
theorem isCyclicallyMonotone_toPMF_support_of_forall_cost_le (A : TransportMatrix μ ν)
    (c : ι × κ → ℝ) (hc : ∀ q, 0 ≤ c q)
    (hA : ∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c) :
    IsCyclicallyMonotone (fun q ↦ ENNReal.ofReal (c q)) A.toPMF.support := by
  obtain ⟨φ, ψ, hfeas, hsupp⟩ :=
    A.exists_support_subset_dualContactSet_of_forall_cost_le c hc hA
  exact hfeas.isCyclicallyMonotone_dualContactSet.mono hsupp

/-- **The finite extended-cost form.** If an extended-nonnegative cost is finite everywhere
and a transportation matrix minimizes its real-valued image, then the support of the matrix is
cyclically monotone for the original cost. -/
theorem isCyclicallyMonotone_toPMF_support_of_forall_toReal_cost_le
    (A : TransportMatrix μ ν) (c : ι × κ → ℝ≥0∞) (hc : ∀ q, c q ≠ ∞)
    (hA : ∀ B : TransportMatrix μ ν,
      A.cost (fun q ↦ (c q).toReal) ≤ B.cost (fun q ↦ (c q).toReal)) :
    IsCyclicallyMonotone c A.toPMF.support := by
  have hmono := A.isCyclicallyMonotone_toPMF_support_of_forall_cost_le
    (fun q ↦ (c q).toReal) (fun q ↦ ENNReal.toReal_nonneg) hA
  simpa only [ENNReal.ofReal_toReal (hc _)] using hmono

end TransportMatrix

/-- Every nonnegative real cost on two finite probability spaces has an optimal transportation
matrix whose support is cyclically monotone. The optimal matrix exists by finite Kantorovich
duality; cyclical monotonicity holds for every optimizer, not just the one selected here. -/
theorem exists_transportMatrix_isCyclicallyMonotone_toPMF_support (c : ι × κ → ℝ)
    (hc : ∀ q, 0 ≤ c q) (μ : PMF ι) (ν : PMF κ) :
    ∃ A : TransportMatrix μ ν,
      (∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c) ∧
        IsCyclicallyMonotone (fun q ↦ ENNReal.ofReal (c q)) A.toPMF.support := by
  obtain ⟨A, hA⟩ := TransportMatrix.exists_forall_cost_le c μ ν
  exact ⟨A, hA, A.isCyclicallyMonotone_toPMF_support_of_forall_cost_le c hc hA⟩

/-- Every everywhere-finite extended-nonnegative cost on two finite probability spaces has an
optimal transportation matrix whose support is cyclically monotone. Optimality is read through
the real-valued finite linear program, which is equivalent because the cost never takes the
value `∞`. -/
theorem exists_transportMatrix_isCyclicallyMonotone_toPMF_support_of_ne_top
    (c : ι × κ → ℝ≥0∞) (hc : ∀ q, c q ≠ ∞) (μ : PMF ι) (ν : PMF κ) :
    ∃ A : TransportMatrix μ ν,
      (∀ B : TransportMatrix μ ν,
        A.cost (fun q ↦ (c q).toReal) ≤ B.cost (fun q ↦ (c q).toReal)) ∧
        IsCyclicallyMonotone c A.toPMF.support := by
  obtain ⟨A, hA⟩ := TransportMatrix.exists_forall_cost_le (fun q ↦ (c q).toReal) μ ν
  exact ⟨A, hA,
    A.isCyclicallyMonotone_toPMF_support_of_forall_toReal_cost_le c hc hA⟩

end TauCeti

end

end
