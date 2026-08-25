/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite transport plans as matrices

On finite spaces, a probability mass function on a product is the same data as a nonnegative
matrix of total mass one. Prescribing its two marginals says exactly that the row and column sums
of this matrix are the prescribed probability vectors.

This file packages that correspondence. `TauCeti.TransportMatrix μ ν` is the type of
`ℝ≥0∞`-valued matrices with row sums `μ` and column sums `ν`, and
`TauCeti.transportMatrixEquiv` identifies it with the subtype of product PMFs whose two
pushforwards are `μ` and `ν`. The codomain `ℝ≥0∞` makes nonnegativity intrinsic, rather than
a separate side condition.

The entries are also read as a real-valued function `TauCeti.TransportMatrix.toRealFun` on the
product, whose row and column sums are the real marginal masses, and the total
`TauCeti.TransportMatrix.cost` of a matrix against a real cost function is recorded here. Both
are basic transportation-matrix API rather than duality results, and the cost is allowed to be
negative because the finite transport problem is a linear program.

This is the finite transportation-matrix acceptance case of Layer 0 of the optimal-transport
roadmap. It is also the representation used by later finite primal and dual problems.
-/

public section

noncomputable section

open scoped BigOperators ENNReal

namespace TauCeti

universe u v

variable {ι : Type u} {κ : Type v}

section Matrix

variable [Fintype ι] [Fintype κ]

/-- A finite transportation matrix with prescribed row distribution `μ` and column distribution
`ν`. Nonnegativity is built into the `ℝ≥0∞`-valued matrix. -/
structure TransportMatrix (μ : PMF ι) (ν : PMF κ) where
  /-- The mass assigned to each source-target pair. -/
  matrix : Matrix ι κ ℝ≥0∞
  /-- Every row has the mass prescribed by the source distribution. -/
  row_sum : ∀ i, ∑ j, matrix i j = μ i
  /-- Every column has the mass prescribed by the target distribution. -/
  col_sum : ∀ j, ∑ i, matrix i j = ν j

attribute [simp] TransportMatrix.row_sum TransportMatrix.col_sum

namespace TransportMatrix

variable {μ : PMF ι} {ν : PMF κ}

/-- Coerce a transportation matrix to its entries, allowing the notation `A i j`. -/
instance : CoeFun (TransportMatrix μ ν) fun _ ↦ ι → κ → ℝ≥0∞ :=
  ⟨TransportMatrix.matrix⟩

/-- Transportation matrices are equal when all their entries are equal. -/
@[ext]
theorem ext {A B : TransportMatrix μ ν} (h : ∀ i j, A i j = B i j) : A = B := by
  cases A with
  | mk A hArow hAcol =>
    cases B with
    | mk B hBrow hBcol =>
      have : A = B := Matrix.ext fun i j ↦ h i j
      subst this
      rfl

/-- The independent transportation matrix, whose entries are products of marginal masses. -/
def independent (μ : PMF ι) (ν : PMF κ) : TransportMatrix μ ν where
  matrix i j := μ i * ν j
  row_sum i := by
    rw [← Finset.mul_sum]
    simpa only [tsum_fintype, mul_one] using congrArg (μ i * ·) ν.tsum_coe
  col_sum j := by
    rw [← Finset.sum_mul]
    simpa only [tsum_fintype, one_mul] using congrArg (· * ν j) μ.tsum_coe

@[simp]
theorem independent_apply (μ : PMF ι) (ν : PMF κ) (i : ι) (j : κ) :
    independent μ ν i j = μ i * ν j := by
  rfl

/-- A transportation matrix gives a probability mass function on the product by reading its
entries as point masses. -/
def toPMF (A : TransportMatrix μ ν) : PMF (ι × κ) :=
  PMF.ofFintype (fun p ↦ A p.1 p.2) <| by
    rw [Fintype.sum_prod_type]
    calc
      ∑ i, ∑ j, A i j = ∑ i, μ i := Finset.sum_congr rfl fun i _ ↦ A.row_sum i
      _ = 1 := by simpa only [tsum_fintype] using μ.tsum_coe

@[simp]
theorem toPMF_apply (A : TransportMatrix μ ν) (p : ι × κ) : A.toPMF p = A p.1 p.2 :=
  by rfl

/-- Every entry of a transportation matrix is finite: it is bounded by a marginal mass. -/
theorem apply_ne_top (A : TransportMatrix μ ν) (i : ι) (j : κ) : A i j ≠ ⊤ := by
  refine ne_top_of_le_ne_top (μ.apply_ne_top i) ?_
  rw [← A.row_sum i]
  exact Finset.single_le_sum (f := fun j ↦ A i j) (fun _ _ ↦ zero_le) (Finset.mem_univ j)

/-- The entries of a transportation matrix, read as a real-valued function on the product. -/
def toRealFun (A : TransportMatrix μ ν) (q : ι × κ) : ℝ := (A q.1 q.2).toReal

/-- The defining formula for the real-valued entries. -/
@[simp]
theorem toRealFun_apply (A : TransportMatrix μ ν) (q : ι × κ) :
    A.toRealFun q = (A q.1 q.2).toReal := (rfl)

/-- The real-valued entries of a transportation matrix are nonnegative. -/
theorem toRealFun_nonneg (A : TransportMatrix μ ν) (q : ι × κ) : 0 ≤ A.toRealFun q :=
  ENNReal.toReal_nonneg

/-- The real-valued row sums are the masses of the source distribution. -/
theorem sum_toRealFun_row (A : TransportMatrix μ ν) (i : ι) :
    ∑ j, A.toRealFun (i, j) = (μ i).toReal := by
  simp only [toRealFun_apply]
  rw [← ENNReal.toReal_sum fun j _ ↦ A.apply_ne_top i j, A.row_sum]

/-- The real-valued column sums are the masses of the target distribution. -/
theorem sum_toRealFun_col (A : TransportMatrix μ ν) (j : κ) :
    ∑ i, A.toRealFun (i, j) = (ν j).toReal := by
  simp only [toRealFun_apply]
  rw [← ENNReal.toReal_sum fun i _ ↦ A.apply_ne_top i j, A.col_sum]

/-- The total cost of a finite transportation matrix. The cost function is real-valued, so
negative costs are allowed. -/
def cost (c : ι × κ → ℝ) (A : TransportMatrix μ ν) : ℝ := ∑ q, c q * A.toRealFun q

/-- The defining formula for the cost. The body of the definition is not exposed, so this is
the lemma downstream modules should rewrite with. -/
theorem cost_def (c : ι × κ → ℝ) (A : TransportMatrix μ ν) :
    A.cost c = ∑ q, c q * A.toRealFun q := (rfl)

end TransportMatrix

end Matrix

namespace PMF

section Fst

variable [Fintype κ] (π : PMF (ι × κ))

/-- The first marginal of a finite product PMF is obtained by summing each row of its matrix of
point masses. -/
theorem map_fst_apply (i : ι) : π.map Prod.fst i = ∑ j, π (i, j) := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod']
  rw [tsum_eq_single i]
  · simp
  · intro i' hi
    simp [hi.symm]

/-- A product PMF has first marginal `μ` exactly when its row sums are `μ`. -/
theorem map_fst_eq_iff (μ : PMF ι) :
    π.map Prod.fst = μ ↔ ∀ i, ∑ j, π (i, j) = μ i := by
  rw [PMF.ext_iff]
  simp only [map_fst_apply]

end Fst

section Snd

variable [Fintype ι] (π : PMF (ι × κ))

/-- The second marginal of a finite product PMF is obtained by summing each column of its matrix
of point masses. -/
theorem map_snd_apply (j : κ) : π.map Prod.snd j = ∑ i, π (i, j) := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod']
  simp

/-- A product PMF has second marginal `ν` exactly when its column sums are `ν`. -/
theorem map_snd_eq_iff (ν : PMF κ) :
    π.map Prod.snd = ν ↔ ∀ j, ∑ i, π (i, j) = ν j := by
  rw [PMF.ext_iff]
  simp only [map_snd_apply]

end Snd

end PMF

namespace TransportMatrix

variable [Fintype ι] [Fintype κ]
variable {μ : PMF ι} {ν : PMF κ}

/-- The PMF associated to a transportation matrix has the prescribed first marginal. -/
@[simp]
theorem map_fst_toPMF (A : TransportMatrix μ ν) : A.toPMF.map Prod.fst = μ :=
  (TauCeti.PMF.map_fst_eq_iff A.toPMF μ).2 A.row_sum

/-- The PMF associated to a transportation matrix has the prescribed second marginal. -/
@[simp]
theorem map_snd_toPMF (A : TransportMatrix μ ν) : A.toPMF.map Prod.snd = ν :=
  (TauCeti.PMF.map_snd_eq_iff A.toPMF ν).2 A.col_sum

/-- The transportation matrix obtained by recording the point masses of a finite product PMF
with prescribed marginals. -/
def ofPMF (π : PMF (ι × κ)) (hμ : π.map Prod.fst = μ) (hν : π.map Prod.snd = ν) :
    TransportMatrix μ ν where
  matrix i j := π (i, j)
  row_sum := (TauCeti.PMF.map_fst_eq_iff π μ).1 hμ
  col_sum := (TauCeti.PMF.map_snd_eq_iff π ν).1 hν

@[simp]
theorem ofPMF_apply (π : PMF (ι × κ)) (hμ : π.map Prod.fst = μ)
    (hν : π.map Prod.snd = ν) (i : ι) (j : κ) :
    ofPMF π hμ hν i j = π (i, j) := by
  rfl

@[simp]
theorem toPMF_ofPMF (π : PMF (ι × κ)) (hμ : π.map Prod.fst = μ)
    (hν : π.map Prod.snd = ν) : (ofPMF π hμ hν).toPMF = π := by
  ext p
  rfl

@[simp]
theorem ofPMF_toPMF (A : TransportMatrix μ ν) :
    ofPMF A.toPMF A.map_fst_toPMF A.map_snd_toPMF = A := by
  ext i j
  rfl

end TransportMatrix

variable [Fintype ι] [Fintype κ]

/-- Finite product PMFs with prescribed marginals are equivalent to nonnegative transportation
matrices with the corresponding row and column sums. -/
def transportMatrixEquiv (μ : PMF ι) (ν : PMF κ) :
    {π : PMF (ι × κ) // π.map Prod.fst = μ ∧ π.map Prod.snd = ν} ≃
      TransportMatrix μ ν where
  toFun π := TransportMatrix.ofPMF π π.2.1 π.2.2
  invFun A := ⟨A.toPMF, A.map_fst_toPMF, A.map_snd_toPMF⟩
  left_inv π := by
    apply Subtype.ext
    exact TransportMatrix.toPMF_ofPMF (μ := μ) (ν := ν) π.1 π.2.1 π.2.2
  right_inv := TransportMatrix.ofPMF_toPMF

@[simp]
theorem transportMatrixEquiv_apply (μ : PMF ι) (ν : PMF κ)
    (π : {π : PMF (ι × κ) // π.map Prod.fst = μ ∧ π.map Prod.snd = ν})
    (i : ι) (j : κ) :
    transportMatrixEquiv μ ν π i j = π.1 (i, j) :=
  by rfl

@[simp]
theorem transportMatrixEquiv_symm_apply (μ : PMF ι) (ν : PMF κ)
    (A : TransportMatrix μ ν) (p : ι × κ) :
    ((transportMatrixEquiv μ ν).symm A).1 p = A p.1 p.2 := by
  rfl

end TauCeti
