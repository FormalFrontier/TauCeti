/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Spectrum
public import TauCeti.Analysis.InnerProductSpace.Variational.Fredholm

/-!
# The spectrum of a coercive variational problem

Let `B` be a bounded coercive bilinear form on a real Hilbert space `V` and let `J : V →L[ℝ] H`
be a continuous linear map into a second real Hilbert space.  The **variational eigenvalue
problem** attached to this pair asks for `κ : ℝ` and `u ≠ 0` with

`B u v = κ ⟪J u, J v⟫` for every `v : V`.

This file studies that problem through the **solution operator** on `H`.  For `h : H`,
Lax--Milgram produces the unique `u : V` with `B u v = ⟪h, J v⟫` for all `v`; the map
`h ↦ u` is `IsCoercive.formSolutionMap`, and composing it with `J` gives
`IsCoercive.formSolutionOperator`, an operator `S : H →L[ℝ] H`.

`S` is the right object to spectralize.  It is compact as soon as `J` is, it is symmetric as
soon as `B` is, and its nonzero eigenvalues are exactly the reciprocals of the variational
eigenvalues: `S` has eigenvalue `κ⁻¹` at `κ • J u` precisely when `u` solves the variational
eigenvalue problem for `κ`.  Mathlib's spectral theorem for compact symmetric operators then
applies verbatim, giving eigenvectors with dense span and finite-dimensional eigenspaces at the
*nonzero* eigenvalues.  The eigenspace at `0` is the kernel of `S`, which is `(range J)ᗮ` and so
can be infinite dimensional; it vanishes exactly when `J` has dense range.

Coercivity forces every variational eigenvalue to be positive, and quantitatively to be at
least the coercivity constant whenever `J` is a contraction; this is the abstract form of the
statement that the first eigenvalue of a Dirichlet problem is bounded below by the constant in
the corresponding Poincaré inequality.

The kernel of `S` is the orthogonal complement of the range of `J`
(`IsCoercive.ker_formSolutionOperator`), so `S` is injective exactly when `J` has dense range;
that is the hypothesis under which every eigenvector of `S` comes from a variational
eigenfunction.

## Main declarations

* `IsCoercive.formSolutionMap`: the Lax--Milgram solution map `H →L[ℝ] V` of the forcing
  `v ↦ ⟪h, J v⟫`, characterized by `IsCoercive.apply_formSolutionMap`.
* `IsCoercive.formSolutionOperator`: the induced solution operator `S : H →L[ℝ] H`, with
  `IsCoercive.isCompactOperator_formSolutionOperator`,
  `IsCoercive.isSymmetric_formSolutionOperator` and
  `IsCoercive.inner_formSolutionOperator_self_nonneg`.
* `IsCoercive.ker_formSolutionOperator`: the kernel of `S` is `(range J)ᗮ`.
* `IsCoercive.hasEigenvalue_formSolutionOperator_iff`: the reciprocal correspondence between
  the nonzero eigenvalues of `S` and the variational eigenvalues.
* `IsCoercive.exists_ne_zero_forall_apply_eq_smul_inner`: existence of a variational
  eigenvalue.
* `IsCoercive.exists_ne_zero_forall_apply_eq_inv_norm_smul_inner`: the reciprocal of the norm
  of the solution operator is a variational eigenvalue.
* `IsCoercive.pos_of_forall_apply_eq_smul_inner` and
  `IsCoercive.le_of_forall_apply_eq_smul_inner`: positivity of a variational eigenvalue, and
  the lower bound by the coercivity constant.
* `IsCoercive.orthogonalComplement_iSup_eigenspaces_formSolutionOperator_eq_bot` and
  `IsCoercive.orthogonalComplement_iSup_eigenspaces_ne_zero_formSolutionOperator_eq_bot`: the
  eigenvectors of `S` span a dense subspace, and only the nonzero eigenvalues are needed when
  `J` has dense range.
* `IsCoercive.exists_hilbertBasis_forall_apply_eq_smul_inner`: the variational eigenfunctions
  form an orthonormal basis of `H`.

## References

L. C. Evans, *Partial Differential Equations*, Section 6.5 (eigenvalues of symmetric elliptic
operators); H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Section 6.4.
-/

public section

noncomputable section

open Module.End
open scoped InnerProduct InnerProductSpace

namespace IsCoercive

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-! ### The solution map and the solution operator -/

/-- The **Lax--Milgram solution map** of a coercive form `B` along `J : V →L[ℝ] H`: it sends
`h : H` to the unique `u : V` solving `B u v = ⟪h, J v⟫` for every `v : V`.  It is characterized
by `IsCoercive.apply_formSolutionMap` together with `IsCoercive.eq_formSolutionMap`. -/
def formSolutionMap (hB : IsCoercive B) (J : V →L[ℝ] H) : H →L[ℝ] V :=
  hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp (J†)

/-- The solution map is the inverse Lax--Milgram operator applied to the adjoint of `J`. -/
theorem formSolutionMap_apply (hB : IsCoercive B) (J : V →L[ℝ] H) (h : H) :
    hB.formSolutionMap J h = hB.solutionOfInner ((J†) h) := by
  rw [formSolutionMap, ContinuousLinearMap.comp_apply, solutionOfInner_def]
  rfl

/-- **The variational equation solved by the solution map.** -/
@[simp]
theorem apply_formSolutionMap (hB : IsCoercive B) (J : V →L[ℝ] H) (h : H) (v : V) :
    B (hB.formSolutionMap J h) v = ⟪h, J v⟫_ℝ := by
  rw [formSolutionMap_apply, apply_solutionOfInner_eq_inner,
    ContinuousLinearMap.adjoint_inner_left]

/-- A vector solving the variational equation of `h` is the solution map's value at `h`. -/
theorem eq_formSolutionMap (hB : IsCoercive B) (J : V →L[ℝ] H) {h : H} {u : V}
    (hu : ∀ v : V, B u v = ⟪h, J v⟫_ℝ) : u = hB.formSolutionMap J h := by
  rw [formSolutionMap_apply]
  refine eq_solutionOfInner hB fun v => ?_
  rw [hu, ContinuousLinearMap.adjoint_inner_left]

/-- The form perturbation operator on `V` is the solution map precomposed with `J`, where the
solution operator on `H` is the same pair of maps composed in the other order. -/
theorem formPerturbationOperator_eq_comp (hB : IsCoercive B) (J : V →L[ℝ] H) :
    hB.formPerturbationOperator J = (hB.formSolutionMap J).comp J := by
  ext u
  rw [ContinuousLinearMap.comp_apply]
  exact eq_formSolutionMap hB J fun v => hB.apply_formPerturbationOperator J u v

/-- The **solution operator** of a coercive form `B` along `J : V →L[ℝ] H`: it sends `h : H` to
`J u`, where `u` is the solution of `B u v = ⟪h, J v⟫`.  For a coercive elliptic form and the
inclusion of a Sobolev space into `L²` it is the operator inverting the elliptic problem, whose
spectrum is that of the corresponding eigenvalue problem. -/
def formSolutionOperator (hB : IsCoercive B) (J : V →L[ℝ] H) : H →L[ℝ] H :=
  J.comp (hB.formSolutionMap J)

/-- The solution operator is `J` applied to the solution of the variational equation. -/
@[simp]
theorem formSolutionOperator_apply (hB : IsCoercive B) (J : V →L[ℝ] H) (h : H) :
    hB.formSolutionOperator J h = J (hB.formSolutionMap J h) := by
  rw [formSolutionOperator, ContinuousLinearMap.comp_apply]

/-! ### Compactness, symmetry, positivity -/

/-- The solution operator is compact as soon as `J` is. -/
theorem isCompactOperator_formSolutionOperator (hB : IsCoercive B) {J : V →L[ℝ] H}
    (hJ : IsCompactOperator J) : IsCompactOperator (hB.formSolutionOperator J) := by
  rw [formSolutionOperator]
  exact hJ.comp_clm (hB.formSolutionMap J)

/-- The solution operator is symmetric as soon as the form is. -/
theorem isSymmetric_formSolutionOperator (hB : IsCoercive B) (J : V →L[ℝ] H)
    (hsymm : ∀ u v : V, B u v = B v u) :
    LinearMap.IsSymmetric (hB.formSolutionOperator J : H →ₗ[ℝ] H) := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, formSolutionOperator_apply]
  calc ⟪J (hB.formSolutionMap J x), y⟫_ℝ
      = ⟪y, J (hB.formSolutionMap J x)⟫_ℝ := real_inner_comm _ _
    _ = B (hB.formSolutionMap J y) (hB.formSolutionMap J x) :=
        (apply_formSolutionMap hB J y _).symm
    _ = B (hB.formSolutionMap J x) (hB.formSolutionMap J y) := hsymm _ _
    _ = ⟪x, J (hB.formSolutionMap J y)⟫_ℝ := apply_formSolutionMap hB J x _

/-- The quadratic form of the solution operator is the energy of the solution. -/
theorem inner_formSolutionOperator_self (hB : IsCoercive B) (J : V →L[ℝ] H) (h : H) :
    ⟪h, hB.formSolutionOperator J h⟫_ℝ =
      B (hB.formSolutionMap J h) (hB.formSolutionMap J h) :=
  (apply_formSolutionMap hB J h _).symm

/-- The solution operator is positive semidefinite: its quadratic form is the energy of the
solution, which coercivity keeps nonnegative. -/
theorem inner_formSolutionOperator_self_nonneg (hB : IsCoercive B) (J : V →L[ℝ] H) (h : H) :
    0 ≤ ⟪h, hB.formSolutionOperator J h⟫_ℝ := by
  obtain ⟨C, hC, hle⟩ := id hB
  refine (inner_formSolutionOperator_self hB J h).trans_ge ?_
  refine le_trans ?_ (hle (hB.formSolutionMap J h))
  positivity

/-! ### The kernel of the solution operator -/

/-- The solution operator kills exactly the vectors orthogonal to the range of `J`. -/
theorem formSolutionOperator_apply_eq_zero_iff (hB : IsCoercive B) (J : V →L[ℝ] H) (h : H) :
    hB.formSolutionOperator J h = 0 ↔ ∀ v : V, ⟪h, J v⟫_ℝ = 0 := by
  constructor
  · intro hzero v
    obtain ⟨C, hC, hle⟩ := id hB
    have hself : B (hB.formSolutionMap J h) (hB.formSolutionMap J h) = 0 := by
      rw [apply_formSolutionMap, ← formSolutionOperator_apply, hzero, inner_zero_right]
    have hnorm : ‖hB.formSolutionMap J h‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖hB.formSolutionMap J h‖ := (norm_nonneg _).lt_of_ne (Ne.symm hne)
      have h2 : 0 < C * ‖hB.formSolutionMap J h‖ * ‖hB.formSolutionMap J h‖ :=
        mul_pos (mul_pos hC hpos) hpos
      linarith [hle (hB.formSolutionMap J h)]
    have hzero' : hB.formSolutionMap J h = 0 := norm_eq_zero.mp hnorm
    rw [← apply_formSolutionMap hB J h v, hzero']
    simp
  · intro horth
    have hsol : (0 : V) = hB.formSolutionMap J h :=
      eq_formSolutionMap hB J fun v => by rw [horth v]; simp
    rw [formSolutionOperator_apply, ← hsol, map_zero]

/-- The solution operator is nonzero whenever the map defining it is nonzero. -/
theorem formSolutionOperator_ne_zero (hB : IsCoercive B) {J : V →L[ℝ] H} (hJ : J ≠ 0) :
    hB.formSolutionOperator J ≠ 0 := by
  obtain ⟨w, hw⟩ : ∃ w : V, J w ≠ 0 := by
    simpa only [zero_apply] using DFunLike.ne_iff.mp hJ
  intro hzero
  have hJw : hB.formSolutionOperator J (J w) = 0 := by rw [hzero, zero_apply]
  exact hw (inner_self_eq_zero.mp
    ((hB.formSolutionOperator_apply_eq_zero_iff J (J w)).mp hJw w))

/-- **The kernel of the solution operator** is the orthogonal complement of the range of `J`;
`IsCoercive.eigenspace_formSolutionOperator_zero_eq_bot` draws the consequence for a `J` with
dense range. -/
theorem ker_formSolutionOperator (hB : IsCoercive B) (J : V →L[ℝ] H) :
    LinearMap.ker (hB.formSolutionOperator J : H →ₗ[ℝ] H) =
      (LinearMap.range (J : V →ₗ[ℝ] H))ᗮ := by
  ext h
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    formSolutionOperator_apply_eq_zero_iff hB J h, Submodule.mem_orthogonal]
  constructor
  · rintro hh - ⟨v, rfl⟩
    rw [real_inner_comm]
    exact hh v
  · intro hh v
    rw [real_inner_comm]
    exact hh (J v) ⟨v, rfl⟩

/-- With `J` of dense range, `0` is not an eigenvalue of the solution operator. -/
theorem eigenspace_formSolutionOperator_zero_eq_bot (hB : IsCoercive B) {J : V →L[ℝ] H}
    (hJ : DenseRange J) :
    eigenspace (hB.formSolutionOperator J : H →ₗ[ℝ] H) 0 = ⊥ := by
  rw [eigenspace_zero]
  refine le_antisymm (fun h hh => ?_) bot_le
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    formSolutionOperator_apply_eq_zero_iff hB J h] at hh
  exact (Submodule.mem_bot ℝ).mpr (hJ.eq_zero_of_inner_left ℝ hh)

/-! ### Variational eigenvalues -/

omit [CompleteSpace V] [CompleteSpace H] in
/-- A variational eigenvalue is positive: coercivity bounds the energy of an eigenfunction
below by a positive multiple of its squared norm. -/
theorem pos_of_forall_apply_eq_smul_inner (hB : IsCoercive B) (J : V →L[ℝ] H) {kappa : ℝ}
    {u : V} (hu : u ≠ 0) (heq : ∀ v : V, B u v = kappa * ⟪J u, J v⟫_ℝ) : 0 < kappa := by
  obtain ⟨C, hC, hle⟩ := id hB
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hself : B u u = kappa * ‖J u‖ ^ 2 := by
    rw [heq u, real_inner_self_eq_norm_sq]
  rcases le_or_gt kappa 0 with hk | hk
  · exfalso
    have h1 : kappa * ‖J u‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖J u‖]
    have h2 : 0 < C * ‖u‖ * ‖u‖ := mul_pos (mul_pos hC hpos) hpos
    linarith [hle u]
  · exact hk

omit [CompleteSpace V] [CompleteSpace H] in
/-- **A variational eigenvalue is at least the coercivity constant**, when `J` is a
contraction.  For the Dirichlet problem this is the statement that the first eigenvalue is
bounded below by the constant appearing in the Poincaré inequality. -/
theorem le_of_forall_apply_eq_smul_inner (hB : IsCoercive B) {J : V →L[ℝ] H} {C : ℝ}
    (hlower : ∀ w : V, C * ‖w‖ ^ 2 ≤ B w w) (hJ : ∀ w : V, ‖J w‖ ≤ ‖w‖) {kappa : ℝ} {u : V}
    (hu : u ≠ 0) (heq : ∀ v : V, B u v = kappa * ⟪J u, J v⟫_ℝ) : C ≤ kappa := by
  have hkappa : 0 < kappa := hB.pos_of_forall_apply_eq_smul_inner J hu heq
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hself : B u u = kappa * ‖J u‖ ^ 2 := by
    rw [heq u, real_inner_self_eq_norm_sq]
  have hJu : ‖J u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    have := hJ u
    nlinarith [norm_nonneg (J u)]
  have hstep : kappa * ‖J u‖ ^ 2 ≤ kappa * ‖u‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hJu hkappa.le
  have hsq : 0 < ‖u‖ ^ 2 := by positivity
  exact le_of_mul_le_mul_right (by linarith [hlower u]) hsq

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- **A variational eigenfunction has nonzero image in `H`.**  If `J u` vanished, the
eigenvalue equation would make the energy of `u` vanish too, which coercivity forbids for
`u ≠ 0`. -/
theorem apply_ne_zero_of_forall_apply_eq_smul_inner (hB : IsCoercive B) (J : V →L[ℝ] H)
    {kappa : ℝ} {u : V} (hu : u ≠ 0) (heq : ∀ v : V, B u v = kappa * ⟪J u, J v⟫_ℝ) :
    J u ≠ 0 := by
  intro hzero
  obtain ⟨C, hC, hle⟩ := id hB
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hself : B u u = 0 := by rw [heq u, hzero, inner_zero_left, mul_zero]
  have h2 : 0 < C * ‖u‖ * ‖u‖ := mul_pos (mul_pos hC hpos) hpos
  linarith [hle u]

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- A variational eigenfunction for `κ ≠ 0` produces an eigenvector of the solution operator
with eigenvalue `κ⁻¹`. -/
theorem hasEigenvector_formSolutionOperator (hB : IsCoercive B) (J : V →L[ℝ] H) {kappa : ℝ}
    (hkappa : kappa ≠ 0) {u : V} (hu : u ≠ 0) (heq : ∀ v : V, B u v = kappa * ⟪J u, J v⟫_ℝ) :
    HasEigenvector (hB.formSolutionOperator J : H →ₗ[ℝ] H) kappa⁻¹ (kappa • J u) := by
  have hsol : u = hB.formSolutionMap J (kappa • J u) :=
    eq_formSolutionMap hB J fun v => by rw [heq v, real_inner_smul_left]
  refine ⟨mem_eigenspace_iff.mpr ?_,
    smul_ne_zero hkappa (hB.apply_ne_zero_of_forall_apply_eq_smul_inner J hu heq)⟩
  rw [ContinuousLinearMap.coe_coe, formSolutionOperator_apply, ← hsol, smul_smul,
    inv_mul_cancel₀ hkappa, one_smul]

/-- An eigenvector of the solution operator with nonzero eigenvalue produces a variational
eigenfunction for the reciprocal eigenvalue. -/
theorem exists_forall_apply_eq_smul_inner (hB : IsCoercive B) (J : V →L[ℝ] H) {mu : ℝ}
    (hmu : mu ≠ 0) (h : HasEigenvalue (hB.formSolutionOperator J : H →ₗ[ℝ] H) mu) :
    ∃ u : V, u ≠ 0 ∧ ∀ v : V, B u v = mu⁻¹ * ⟪J u, J v⟫_ℝ := by
  obtain ⟨w, hw, hwne⟩ := h.exists_hasEigenvector
  have hSw : J (hB.formSolutionMap J w) = mu • w := by
    have := mem_eigenspace_iff.mp hw
    rwa [ContinuousLinearMap.coe_coe, formSolutionOperator_apply] at this
  refine ⟨hB.formSolutionMap J w, ?_, fun v => ?_⟩
  · intro hzero
    rw [hzero, map_zero] at hSw
    rcases smul_eq_zero.mp hSw.symm with hz | hz
    · exact hmu hz
    · exact hwne hz
  · rw [apply_formSolutionMap, hSw, real_inner_smul_left, ← mul_assoc, inv_mul_cancel₀ hmu,
      one_mul]

/-- **Existence of a variational eigenvalue.**  For a symmetric form and a nonzero compact `J`,
the variational eigenvalue problem has a nonzero eigenvalue with an eigenfunction. -/
theorem exists_ne_zero_forall_apply_eq_smul_inner (hB : IsCoercive B) {J : V →L[ℝ] H}
    (hJ : IsCompactOperator J) (hsymm : ∀ u v : V, B u v = B v u) (hJne : J ≠ 0) :
    ∃ kappa : ℝ, kappa ≠ 0 ∧ ∃ u : V, u ≠ 0 ∧ ∀ v : V, B u v = kappa * ⟪J u, J v⟫_ℝ := by
  have hSne := hB.formSolutionOperator_ne_zero hJne
  have hcompact := hB.isCompactOperator_formSolutionOperator hJ
  have hsym := hB.isSymmetric_formSolutionOperator J hsymm
  have hex : ¬ ∀ mu : ℝ,
      HasEigenvalue (hB.formSolutionOperator J : H →ₗ[ℝ] H) mu → mu = 0 := fun hcontra =>
    hSne ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hcompact hsym).mp hcontra)
  obtain ⟨mu, hmu⟩ := not_forall.mp hex
  obtain ⟨hmu_eigen, hmu_ne⟩ := Classical.not_imp.mp hmu
  obtain ⟨u, hu, heq⟩ := hB.exists_forall_apply_eq_smul_inner J hmu_ne hmu_eigen
  exact ⟨mu⁻¹, inv_ne_zero hmu_ne, u, hu, heq⟩

/-- **The variational eigenvalues are the reciprocals of the nonzero eigenvalues of the
solution operator.** -/
theorem hasEigenvalue_formSolutionOperator_iff (hB : IsCoercive B) (J : V →L[ℝ] H) {kappa : ℝ}
    (hkappa : kappa ≠ 0) :
    HasEigenvalue (hB.formSolutionOperator J : H →ₗ[ℝ] H) kappa⁻¹ ↔
      ∃ u : V, u ≠ 0 ∧ ∀ v : V, B u v = kappa * ⟪J u, J v⟫_ℝ := by
  constructor
  · intro h
    obtain ⟨u, hu, heq⟩ :=
      hB.exists_forall_apply_eq_smul_inner J (inv_ne_zero hkappa) h
    exact ⟨u, hu, by simpa only [inv_inv] using heq⟩
  · rintro ⟨u, hu, heq⟩
    exact hasEigenvalue_of_hasEigenvector
      (hB.hasEigenvector_formSolutionOperator J hkappa hu heq)

/-- **The reciprocal of the norm of the solution operator is a variational eigenvalue.**
Compactness of `J` is what makes `‖S‖` itself an eigenvalue of `S`, and positivity of `S` is what
excludes `-‖S‖`. -/
theorem exists_ne_zero_forall_apply_eq_inv_norm_smul_inner (hB : IsCoercive B)
    {J : V →L[ℝ] H} (hJ : IsCompactOperator J) (hsymm : ∀ u v : V, B u v = B v u)
    (hJne : J ≠ 0) :
    ∃ u : V, u ≠ 0 ∧
      ∀ v : V, B u v = ‖hB.formSolutionOperator J‖⁻¹ * ⟪J u, J v⟫_ℝ := by
  obtain ⟨w, hw⟩ : ∃ w : V, J w ≠ 0 := by
    simpa only [zero_apply] using DFunLike.ne_iff.mp hJne
  have _ : Nontrivial H := nontrivial_of_ne (J w) 0 hw
  set S := hB.formSolutionOperator J with hS
  have hSne : S ≠ 0 := by
    rw [hS]
    exact hB.formSolutionOperator_ne_zero hJne
  have hnorm_pos : 0 < ‖S‖ := norm_pos_iff.mpr hSne
  have hcompact : IsCompactOperator S := hB.isCompactOperator_formSolutionOperator hJ
  have hsym : LinearMap.IsSymmetric (S : H →ₗ[ℝ] H) :=
    hB.isSymmetric_formSolutionOperator J hsymm
  have hnorm_or_neg : ‖S‖ ∈ spectrum ℝ S ∨ -‖S‖ ∈ spectrum ℝ S := by
    simp_rw [spectrum, Set.mem_compl_iff]
    by_contra! h
    obtain ⟨d, hd, hle⟩ := S.abs_rayleighQuotient_le_of_norm_mem_resolventSet h.1 h.2
    have hsup := ciSup_le hle
    have heq := ContinuousLinearMap.norm_eq_iSup_rayleighQuotient S hsym
    linarith
  have hnorm_mem : ‖S‖ ∈ spectrum ℝ S := hnorm_or_neg.resolve_right fun hneg => by
    have hneg_eigen : HasEigenvalue (S : H →ₗ[ℝ] H) (-‖S‖) :=
      (hcompact.hasEigenvalue_iff_mem_spectrum (neg_ne_zero.mpr hnorm_pos.ne')).mpr hneg
    have hnonneg : 0 ≤ -‖S‖ := eigenvalue_nonneg_of_nonneg hneg_eigen fun f => by
      simpa [hS] using hB.inner_formSolutionOperator_self_nonneg J f
    linarith
  have hnorm_eigen : HasEigenvalue (S : H →ₗ[ℝ] H) ‖S‖ :=
    (hcompact.hasEigenvalue_iff_mem_spectrum hnorm_pos.ne').mpr hnorm_mem
  refine (hB.hasEigenvalue_formSolutionOperator_iff J (inv_ne_zero hnorm_pos.ne')).mp ?_
  simpa only [hS, inv_inv] using hnorm_eigen

/-! ### The spectral theorem for the solution operator -/

/-- Eigenspaces of the solution operator at nonzero eigenvalues are finite dimensional. -/
theorem finiteDimensional_eigenspace_formSolutionOperator (hB : IsCoercive B) {J : V →L[ℝ] H}
    (hJ : IsCompactOperator J) {mu : ℝ} (hmu : mu ≠ 0) :
    FiniteDimensional ℝ (eigenspace (hB.formSolutionOperator J : H →ₗ[ℝ] H) mu) :=
  ContinuousLinearMap.finite_dimensional_eigenspace
    (hB.isCompactOperator_formSolutionOperator hJ) mu hmu

/-- **The spectral theorem for the solution operator**: its eigenvectors span a dense subspace
of `H`. -/
theorem orthogonalComplement_iSup_eigenspaces_formSolutionOperator_eq_bot (hB : IsCoercive B)
    {J : V →L[ℝ] H} (hJ : IsCompactOperator J) (hsymm : ∀ u v : V, B u v = B v u) :
    (⨆ mu : ℝ, eigenspace (hB.formSolutionOperator J : H →ₗ[ℝ] H) mu)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (hB.isCompactOperator_formSolutionOperator hJ)
    (hB.isSymmetric_formSolutionOperator J hsymm)

/-- **The eigenfunctions of the variational eigenvalue problem span a dense subspace of `H`**:
when `J` is compact with dense range and the form is symmetric, the eigenspaces of the solution
operator at its nonzero eigenvalues already have trivial orthogonal complement. -/
theorem orthogonalComplement_iSup_eigenspaces_ne_zero_formSolutionOperator_eq_bot
    (hB : IsCoercive B)
    {J : V →L[ℝ] H} (hJ : IsCompactOperator J) (hJdense : DenseRange J)
    (hsymm : ∀ u v : V, B u v = B v u) :
    (⨆ mu : ℝ, ⨆ _ : mu ≠ 0,
      eigenspace (hB.formSolutionOperator J : H →ₗ[ℝ] H) mu)ᗮ = ⊥ := by
  refine le_bot_iff.mp ?_
  rw [← hB.orthogonalComplement_iSup_eigenspaces_formSolutionOperator_eq_bot hJ hsymm]
  refine Submodule.orthogonal_le (iSup_le fun mu => ?_)
  rcases eq_or_ne mu 0 with rfl | hne
  · rw [hB.eigenspace_formSolutionOperator_zero_eq_bot hJdense]
    exact bot_le
  · exact le_iSup₂ (f := fun mu (_ : mu ≠ 0) =>
      eigenspace (hB.formSolutionOperator J : H →ₗ[ℝ] H) mu) mu hne

/-- **The variational eigenfunctions form an orthonormal basis of `H`.**  For a symmetric form
and a compact `J` of dense range, `H` has an orthonormal basis `b` each of whose vectors is `J u`
for an eigenfunction `u` of the variational problem at a positive eigenvalue `κ`, and the
solution operator is diagonal in that basis: its value, equivalently the `J`-image of the
solution of `B u v = ⟪h, J v⟫`, is the eigenfunction expansion `∑ κ⁻¹ ⟪b i, h⟫ b i`.
This is the abstract form of the eigenfunction expansion of a symmetric elliptic operator; `H`
is not assumed separable, so the basis is indexed by a set of vectors of `H` as in
`exists_hilbertBasis`. -/
theorem exists_hilbertBasis_forall_apply_eq_smul_inner (hB : IsCoercive B) {J : V →L[ℝ] H}
    (hJ : IsCompactOperator J) (hJdense : DenseRange J) (hsymm : ∀ u v : V, B u v = B v u) :
    ∃ (s : Set H) (b : HilbertBasis s ℝ H) (kappa : s → ℝ) (u : s → V),
      ⇑b = ((↑) : s → H) ∧ (∀ x : s, 0 < kappa x) ∧ (∀ x : s, u x ≠ 0) ∧
      (∀ x : s, J (u x) = (x : H)) ∧
      (∀ (x : s) (v : V), B (u x) v = kappa x * ⟪J (u x), J v⟫_ℝ) ∧
      ∀ h : H, HasSum (fun x : s => (kappa x)⁻¹ • b.repr h x • b x)
        (hB.formSolutionOperator J h) := by
  have hker : LinearMap.ker (hB.formSolutionOperator J : H →ₗ[ℝ] H) = ⊥ := by
    rw [← eigenspace_zero]
    exact hB.eigenspace_formSolutionOperator_zero_eq_bot hJdense
  obtain ⟨s, b, nu, hb, hnu, hev⟩ :=
    ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector_ne_zero
    (hB.isCompactOperator_formSolutionOperator hJ)
    (hB.isSymmetric_formSolutionOperator J hsymm) hker
  have hdiag : ∀ x : s, hB.formSolutionOperator J (b x) = nu x • b x := by
    intro x
    rw [hb]
    simpa only [ContinuousLinearMap.coe_coe] using mem_eigenspace_iff.mp (hev x).1
  have hSx : ∀ x : s, J (hB.formSolutionMap J (x : H)) = nu x • (x : H) := by
    intro x
    simpa only [ContinuousLinearMap.coe_coe, formSolutionOperator_apply] using
      mem_eigenspace_iff.mp (hev x).1
  have hJu : ∀ x : s, J ((nu x)⁻¹ • hB.formSolutionMap J (x : H)) = (x : H) := fun x => by
    rw [map_smul, hSx, smul_smul, inv_mul_cancel₀ (hnu x), one_smul]
  have heq : ∀ (x : s) (v : V), B ((nu x)⁻¹ • hB.formSolutionMap J (x : H)) v =
      (nu x)⁻¹ * ⟪J ((nu x)⁻¹ • hB.formSolutionMap J (x : H)), J v⟫_ℝ := fun x v => by
    rw [hJu, map_smul, smul_apply, smul_eq_mul, apply_formSolutionMap]
  have hune : ∀ x : s, (nu x)⁻¹ • hB.formSolutionMap J (x : H) ≠ 0 := by
    intro x hzero
    have h0 := hJu x
    rw [hzero, map_zero] at h0
    exact (hev x).2 h0.symm
  refine ⟨s, b, fun x => (nu x)⁻¹, fun x => (nu x)⁻¹ • hB.formSolutionMap J (x : H), hb,
    fun x => hB.pos_of_forall_apply_eq_smul_inner J (hune x) (heq x), hune, hJu, heq, fun h => ?_⟩
  simpa only [inv_inv] using
    (hB.formSolutionOperator J).hasSum_smul_repr_of_apply_eq_smul b nu hdiag h

end IsCoercive
