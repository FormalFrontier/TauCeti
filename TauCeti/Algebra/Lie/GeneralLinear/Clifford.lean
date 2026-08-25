/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.TraceForm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Representation
import Mathlib.Algebra.Lie.Classical
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors

/-!
# The quadratic Clifford lift of the general linear Lie algebra

The adjoint action of `gl n K` preserves its trace form. Adding the central character
`(card n / 2) trace` to its quadratic realization gives the normal-ordered quadratic lift in the
corresponding Clifford algebra.

## Main results

* `TauCeti.glCliffordHom`: the normal-ordered Lie homomorphism from matrices to the Clifford
  algebra of their trace quadratic form.
* `TauCeti.glCliffordHom_lie_ι`: its commutator action on Clifford generators.
* `TauCeti.glCliffordHom_single`: its formula on matrix units.
* `TauCeti.glCliffordHom_normalOrdering`: its decomposition into bivectors and the central
  normal-ordering constant.
* `TauCeti.glCliffordHom_injective`: it is injective once `Fintype.card n` is invertible, which
  the quadratic part alone is not — the centre of `gl n K` is what the normal-ordering constant
  separates.

## References

* [Tau Ceti Roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), Representation Theory / Spin
  Representations, Layer 9, “The worked instance: `gl_N` on `M_N(ℂ)` (the CAR algebra)”.
-/

public section

namespace TauCeti

open CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K n : Type*} [Field K] [Fintype n] [Invertible (2 : K)]

attribute [local instance] Classical.decEq

private noncomputable def traceQuadraticLift :
    Matrix n n K →ₗ⁅K⁆ CliffordAlgebra (traceQuadraticForm K n) :=
  CliffordAlgebra.quadraticLift (traceQuadraticForm K n)
    (traceQuadraticForm_nondegenerate K n) (traceAdjointSO K n)

private noncomputable def scalarTrace :
    Matrix n n K →ₗ[K] CliffordAlgebra (traceQuadraticForm K n) :=
  (Algebra.linearMap K (CliffordAlgebra (traceQuadraticForm K n))).comp <|
    (Fintype.card n / 2 : K) • Matrix.traceLinearMap n K K

omit [Invertible (2 : K)] in
private theorem scalarTrace_lie (X : Matrix n n K)
    (c : CliffordAlgebra (traceQuadraticForm K n)) :
    ⁅scalarTrace (K := K) (n := n) X, c⁆ = 0 := by
  -- Expose the central scalar before using commutation with the algebra map.
  change ⁅algebraMap K _ ((Fintype.card n / 2 : K) * X.trace), c⁆ = 0
  exact Commute.lie_eq (Algebra.commutes _ c)

/-- The normal-ordered quadratic Clifford lift of the general linear Lie algebra. -/
noncomputable def glCliffordHom :
    Matrix n n K →ₗ⁅K⁆ CliffordAlgebra (traceQuadraticForm K n) :=
  { (traceQuadraticLift (K := K) (n := n)).toLinearMap + scalarTrace (K := K) (n := n) with
    map_lie' := by
      intro X Y
      -- Expose the sum of the quadratic and central linear maps.
      change traceQuadraticLift ⁅X, Y⁆ + scalarTrace ⁅X, Y⁆ =
        ⁅traceQuadraticLift X + scalarTrace X, traceQuadraticLift Y + scalarTrace Y⁆
      rw [LieHom.map_lie]
      have hs : scalarTrace (K := K) (n := n) ⁅X, Y⁆ = 0 := by
        simp [scalarTrace, LieAlgebra.matrix_trace_commutator_zero]
      rw [hs]
      simp only [add_zero, add_lie, lie_add]
      rw [scalarTrace_lie, scalarTrace_lie]
      have hright : ⁅traceQuadraticLift (K := K) (n := n) X, scalarTrace Y⁆ = 0 := by
        rw [← lie_skew, scalarTrace_lie, neg_zero]
      rw [hright]
      simp }

/-- The normal-ordered lift is the sum of the quadratic lift and its scalar trace correction. -/
theorem glCliffordHom_apply (X : Matrix n n K) :
    glCliffordHom X =
      CliffordAlgebra.quadraticLift (traceQuadraticForm K n)
          (traceQuadraticForm_nondegenerate K n) (traceAdjointSO K n) X +
        algebraMap K _ ((Fintype.card n / 2 : K) * X.trace) := by
  -- Expose the two private summands used to assemble the public homomorphism.
  change traceQuadraticLift X + scalarTrace X = _
  rfl

/-- The normal-ordered lift acts on Clifford generators by the matrix commutator. -/
@[simp, grind =]
theorem glCliffordHom_lie_ι (X Y : Matrix n n K) :
    ⁅glCliffordHom (K := K) (n := n) X,
        ι (traceQuadraticForm K n) Y⁆ =
      ι (traceQuadraticForm K n) ⁅X, Y⁆ := by
  -- Expose the two summands before applying bracket bilinearity.
  change ⁅traceQuadraticLift X + scalarTrace X, ι (traceQuadraticForm K n) Y⁆ = _
  rw [add_lie, traceQuadraticLift, CliffordAlgebra.quadraticLift_lie_ι,
    coe_traceAdjointSO, _root_.LieAlgebra.ad_apply, scalarTrace_lie, add_zero]

private theorem matrixUnit_ad_eq_bivector_sum (i j : n) (Y : Matrix n n K) :
    (2⁻¹ : K) • ∑ k : n,
        (QuadraticMap.polar (traceQuadraticForm K n) (Matrix.single k j 1) Y •
            Matrix.single i k 1 -
          QuadraticMap.polar (traceQuadraticForm K n) (Matrix.single i k 1) Y •
            Matrix.single k j 1) =
      ⁅Matrix.single i j (1 : K), Y⁆ := by
  have hpolar₁ (k : n) :
      QuadraticMap.polar (traceQuadraticForm K n) (Matrix.single k j 1) Y = 2 * Y j k := by
    rw [← QuadraticMap.polarBilin_apply_apply, polarBilin_traceQuadraticForm,
      Matrix.trace_single_mul]
    simp
  have hpolar₂ (k : n) :
      QuadraticMap.polar (traceQuadraticForm K n) (Matrix.single i k 1) Y = 2 * Y k i := by
    rw [← QuadraticMap.polarBilin_apply_apply, polarBilin_traceQuadraticForm,
      Matrix.trace_single_mul]
    simp
  simp_rw [hpolar₁, hpolar₂]
  ext a b
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero _
  by_cases hia : i = a <;> by_cases hjb : j = b <;>
    simp +contextual [Ring.lie_def, Matrix.mul_apply, Matrix.sum_apply, Matrix.single,
      hia, hjb, h2]
  field_simp

private noncomputable def matrixUnitQuadratic (i j : n) :
    quadraticLieSubalgebra (traceQuadraticForm K n) :=
  ⟨(2⁻¹ : K) • ∑ k : n,
      bivector (traceQuadraticForm K n) (Matrix.single i k 1) (Matrix.single k j 1),
    (quadraticLieSubalgebra (traceQuadraticForm K n)).smul_mem _ <|
      (quadraticLieSubalgebra (traceQuadraticForm K n)).sum_mem fun k _ =>
        bivector_mem_quadraticLieSubalgebra (traceQuadraticForm K n) (Matrix.single i k 1)
          (Matrix.single k j 1)⟩

private theorem matrixUnitQuadratic_lie_ι (i j : n) (Y : Matrix n n K) :
    ⁅(matrixUnitQuadratic (K := K) i j : CliffordAlgebra (traceQuadraticForm K n)),
        ι (traceQuadraticForm K n) Y⁆ =
      ι (traceQuadraticForm K n) ⁅Matrix.single i j (1 : K), Y⁆ := by
  -- Expose scalar multiplication and the finite sum in the ambient Clifford algebra.
  change ⁅(2⁻¹ : K) • ∑ k : n,
      bivector (traceQuadraticForm K n) (Matrix.single i k 1) (Matrix.single k j 1),
        ι (traceQuadraticForm K n) Y⁆ = _
  rw [smul_lie, sum_lie]
  simp_rw [bivector_lie_ι]
  rw [← map_sum, ← map_smul, matrixUnit_ad_eq_bivector_sum]

private theorem traceQuadraticLift_single (i j : n) :
    traceQuadraticLift (K := K) (n := n) (Matrix.single i j 1) =
      (matrixUnitQuadratic (K := K) i j : CliffordAlgebra (traceQuadraticForm K n)) := by
  let Q := traceQuadraticForm K n
  let hQ := traceQuadraticForm_nondegenerate K n
  let e := soEquivQuadratic Q hQ
  rw [traceQuadraticLift, CliffordAlgebra.quadraticLift_apply]
  -- Expose the generic quadratic lift through the local equivalence `e`.
  change (e (traceAdjointSO K n (Matrix.single i j 1)) : CliffordAlgebra Q) = _
  have heq : e (traceAdjointSO K n (Matrix.single i j 1)) = matrixUnitQuadratic i j := by
    apply quadraticLieSubalgebra_ext Q hQ
    intro Y
    rw [soEquivQuadratic_lie_ι, matrixUnitQuadratic_lie_ι, coe_traceAdjointSO,
      _root_.LieAlgebra.ad_apply]
  exact congrArg Subtype.val heq

/-- The matrix-unit lift is its antisymmetrized quadratic part plus the central normal-ordering
constant. -/
theorem glCliffordHom_normalOrdering (i j : n) :
    glCliffordHom (K := K) (n := n) (Matrix.single i j (1 : K)) =
      (2⁻¹ : K) • ∑ k : n,
          bivector (traceQuadraticForm K n) (Matrix.single i k 1) (Matrix.single k j 1) +
        algebraMap K (CliffordAlgebra (traceQuadraticForm K n))
          (if i = j then (Fintype.card n : K) / 2 else 0) := by
  rw [glCliffordHom]
  -- Expose the sum defining the underlying linear map.
  change traceQuadraticLift (K := K) (n := n) (Matrix.single i j (1 : K)) +
    scalarTrace (K := K) (n := n) (Matrix.single i j (1 : K)) = _
  rw [traceQuadraticLift_single]
  -- Unfold the private matrix-unit value after rewriting the quadratic lift.
  change (2⁻¹ : K) • ∑ k : n,
      bivector (traceQuadraticForm K n) (Matrix.single i k 1) (Matrix.single k j 1) +
        scalarTrace (K := K) (n := n) (Matrix.single i j (1 : K)) = _
  by_cases h : i = j
  · subst j
    simp [scalarTrace]
  · simp [scalarTrace, h]

private theorem matrixUnit_ι_mul_eq_bivector_add (i j k : n) :
    ι (traceQuadraticForm K n) (Matrix.single i k 1) *
        ι (traceQuadraticForm K n) (Matrix.single k j 1) =
      bivector (traceQuadraticForm K n) (Matrix.single i k 1) (Matrix.single k j 1) +
        algebraMap K (CliffordAlgebra (traceQuadraticForm K n)) (if i = j then 1 else 0) := by
  rw [ι_mul_ι_eq_bivector_add, invOf_eq_inv, ← QuadraticMap.polarBilin_apply_apply,
    polarBilin_traceQuadraticForm, ← traceBilinForm_apply, traceBilinForm_single_single]
  by_cases h : i = j
  · subst j
    simp only [Algebra.smul_def, and_self, ↓reduceIte, mul_one, map_one, add_right_inj]
    rw [← map_mul, inv_mul_cancel₀ (Invertible.ne_zero (2 : K)), map_one]
  · simp [eq_comm, h]

/-- On a matrix unit, the lift is the normal-ordered quadratic sum
`Eᵢⱼ ↦ 1/2 ∑ₖ dᵢₖ dₖⱼ`. -/
@[simp, grind =]
theorem glCliffordHom_single (i j : n) :
    glCliffordHom (K := K) (n := n) (Matrix.single i j (1 : K)) =
      (2⁻¹ : K) • ∑ k : n,
        ι (traceQuadraticForm K n) (Matrix.single i k 1) *
          ι (traceQuadraticForm K n) (Matrix.single k j 1) := by
  rw [glCliffordHom_normalOrdering]
  simp_rw [matrixUnit_ι_mul_eq_bivector_add]
  by_cases h : i = j
  · subst j
    simp only [↓reduceIte, map_one]
    have hcentral :
        (2⁻¹ : K) • ∑ _ : n, (1 : CliffordAlgebra (traceQuadraticForm K n)) =
          algebraMap K _ ((Fintype.card n : K) / 2) := by
      rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul K, smul_smul,
        Algebra.algebraMap_eq_smul_one]
      rw [Finset.card_univ]
      congr 1
      ring_nf
    rw [← hcentral]
    rw [Finset.sum_add_distrib, smul_add]
  · simp [h, Finset.smul_sum]

/-! ### Injectivity -/

/-- A matrix annihilated by the normal-ordered lift is central: the lift acts on Clifford
generators by the matrix commutator, and the generators are a faithful copy of the matrices. -/
private theorem commute_of_glCliffordHom_eq_zero {X : Matrix n n K}
    (hX : glCliffordHom (K := K) (n := n) X = 0) (Y : Matrix n n K) : Commute Y X := by
  have h : ι (traceQuadraticForm K n) ⁅X, Y⁆ = 0 := by
    rw [← glCliffordHom_lie_ι, hX, zero_lie]
  have hXY : ⁅X, Y⁆ = 0 := by rwa [ι_eq_zero_iff] at h
  rw [Ring.lie_def, sub_eq_zero] at hXY
  exact hXY.symm

/-- On a central matrix the lift is its normal-ordering constant alone: the adjoint action the
quadratic part lifts already vanishes there. -/
private theorem glCliffordHom_eq_algebraMap_of_commute {X : Matrix n n K}
    (hX : ∀ Y : Matrix n n K, Commute Y X) :
    glCliffordHom (K := K) (n := n) X =
      algebraMap K (CliffordAlgebra (traceQuadraticForm K n))
        ((Fintype.card n / 2 : K) * X.trace) := by
  have hzero : traceAdjointSO K n X = 0 := by
    refine Subtype.ext (LinearMap.ext fun Y => ?_)
    rw [coe_traceAdjointSO, _root_.LieAlgebra.ad_apply, Ring.lie_def, (hX Y).eq, sub_self]
    rfl
  rw [glCliffordHom_apply, CliffordAlgebra.quadraticLift_apply, hzero, map_zero,
    ZeroMemClass.coe_zero, zero_add]

/-- **The normal-ordered lift is injective as soon as `Fintype.card n` is invertible in `K`.**
The adjoint action of `gl n K` is not faithful — its kernel is the centre, the scalar matrices
(`TauCeti.ker_traceAdjointSO`) — so the quadratic part alone is not injective; this is the
reductive-not-semisimple behaviour that distinguishes `gl n K` from a Killing-semisimple Lie
algebra, where `CliffordAlgebra.adjointCliffordHom_injective` needs no hypothesis. It is the
normal-ordering constant that repairs it: on the scalar matrix `r • 1` the lift is the scalar
`(card n) ^ 2 * r / 2`, nonzero exactly when `r` is. The hypothesis is not removable, since in
characteristic dividing `card n` those scalar matrices are again killed. -/
theorem glCliffordHom_injective (h : (Fintype.card n : K) ≠ 0) :
    Function.Injective (glCliffordHom (K := K) (n := n)) := by
  have key : ∀ X : Matrix n n K, glCliffordHom (K := K) (n := n) X = 0 → X = 0 := by
    intro X hX
    have hcomm := commute_of_glCliffordHom_eq_zero hX
    obtain ⟨r, hr⟩ :=
      Matrix.mem_range_scalar_iff_commute_single'.mpr fun i j => hcomm (Matrix.single i j 1)
    have htrace : X.trace = r * Fintype.card n := by
      rw [← hr]
      simp [Matrix.scalar_apply, Matrix.trace_diagonal, mul_comm]
    have hscalar :
        algebraMap K (CliffordAlgebra (traceQuadraticForm K n))
          ((Fintype.card n / 2 : K) * X.trace) = 0 := by
      rw [← glCliffordHom_eq_algebraMap_of_commute hcomm, hX]
    have hcoef : (Fintype.card n / 2 : K) * X.trace = 0 :=
      ((ι_eq_algebraMap_iff (traceQuadraticForm K n) 0
        ((Fintype.card n / 2 : K) * X.trace)).mp (by rw [map_zero, hscalar])).2
    rw [htrace] at hcoef
    have hr0 : r = 0 := by
      rcases mul_eq_zero.mp hcoef with hc | hc
      · rcases div_eq_zero_iff.mp hc with hc | hc
        · exact absurd hc h
        · exact absurd hc (Invertible.ne_zero (2 : K))
      · rcases mul_eq_zero.mp hc with hc | hc
        · exact hc
        · exact absurd hc h
    rw [← hr, hr0]
    simp
  intro X Y hXY
  have h0 : glCliffordHom (K := K) (n := n) (X - Y) = 0 := by rw [map_sub, hXY, sub_self]
  exact sub_eq_zero.mp (key _ h0)

end TauCeti
