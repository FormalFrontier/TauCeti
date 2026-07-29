/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Analysis.Fredholm.Splitting
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Stability of Fredholm operators under small perturbations

This file proves that Fredholm operators between Banach spaces form an open set in the operator
norm topology and that their index is locally constant. Equivalently, every Fredholm operator
`T` has an `ε > 0` such that any operator `S` with `‖S - T‖ < ε` is Fredholm and has the same
index.

The proof uses the kernel and cokernel splittings from
`TauCeti.Analysis.Fredholm.Splitting`. In the resulting block decomposition, the corner from the
chosen kernel complement to the range is an equivalence for `T`, and remains an equivalence in a
neighbourhood of `T` because continuous linear equivalences form an open subset of the operator
space. Elementary block elimination then reduces a nearby operator to the product of that
invertible corner with a map between the finite-dimensional kernel and cokernel.
The openness input is Mathlib's `ContinuousLinearEquiv.isOpen`; no implementation is vendored.

## Main declarations

* `TauCeti.IsFredholm.eventually_isFredholm_and_index_eq`: Fredholmness and the index are stable
  in a neighbourhood of a Fredholm operator.
* `TauCeti.IsFredholm.exists_pos_isFredholm_and_index_eq_of_norm_sub_lt`: the corresponding
  operator-norm `ε` statement.
* `TauCeti.isOpen_setOf_isFredholm`: Fredholm operators form an open set.
* `TauCeti.isOpen_setOf_isFredholm_index_eq`: Fredholm operators of a fixed index form an open
  set.

The argument follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix
A.1, and supplies the small-perturbation stability target in Lane F0 of the analytic Heegaard
Floer roadmap.
-/

public section

namespace TauCeti

open Filter Module
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [CompleteSpace 𝕜]

private def blockCorner
    {K X Y C : Type*}
    [NormedAddCommGroup K] [NormedSpace 𝕜 K]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C]
    (A : K × X →L[𝕜] Y × C) : X →L[𝕜] Y :=
  (ContinuousLinearMap.fst 𝕜 Y C).comp
    (A.comp (ContinuousLinearMap.inr 𝕜 K X))

omit [IsRCLikeNormedField 𝕜] in
private theorem isFredholm_and_index_eq_of_blockCorner_equiv
    {K X Y C : Type*}
    [NormedAddCommGroup K] [NormedSpace 𝕜 K] [FiniteDimensional 𝕜 K]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [FiniteDimensional 𝕜 C]
    (A : K × X →L[𝕜] Y × C) (e : X ≃L[𝕜] Y)
    (he : blockCorner A = (e : X →L[𝕜] Y)) :
    IsFredholm A ∧
      ContinuousLinearMap.index A = (finrank 𝕜 K : ℤ) - finrank 𝕜 C := by
  -- Write `A` as a two-by-two block operator. The lower-case maps below are its four
  -- corners, with `e` the invertible infinite-dimensional corner.
  letI : CompleteSpace K := FiniteDimensional.complete 𝕜 K
  letI : CompleteSpace C := FiniteDimensional.complete 𝕜 C
  let fstY := ContinuousLinearMap.fst 𝕜 Y C
  let sndC := ContinuousLinearMap.snd 𝕜 Y C
  let inlK := ContinuousLinearMap.inl 𝕜 K X
  let inrX := ContinuousLinearMap.inr 𝕜 K X
  let a : K →L[𝕜] Y := fstY.comp (A.comp inlK)
  let c : K →L[𝕜] C := sndC.comp (A.comp inlK)
  let d : X →L[𝕜] C := sndC.comp (A.comp inrX)
  let bInvA : K →L[𝕜] X := (e.symm : Y →L[𝕜] X).comp a
  let dBInv : Y →L[𝕜] C := d.comp (e.symm : Y →L[𝕜] X)
  let schur : K →L[𝕜] C := c - d.comp bInvA
  -- The domain shear subtracts `e⁻¹ a`, eliminating the upper-left off-diagonal block.
  let P : (K × X) ≃L[𝕜] (K × X) :=
    (ContinuousLinearEquiv.refl 𝕜 K).skewProd
      (ContinuousLinearEquiv.refl 𝕜 X) (-bInvA)
  -- The codomain shear subtracts `d e⁻¹`, eliminating the other off-diagonal block.
  let Q : (Y × C) ≃L[𝕜] (Y × C) :=
    (ContinuousLinearEquiv.refl 𝕜 Y).skewProd
      (ContinuousLinearEquiv.refl 𝕜 C) (-dBInv)
  let swap : (C × Y) ≃L[𝕜] (Y × C) :=
    (LinearIsometryEquiv.prodComm 𝕜 C Y).toContinuousLinearEquiv
  let B : K × X →L[𝕜] Y × C :=
    (Q : Y × C →L[𝕜] Y × C).comp
      (A.comp (P : K × X →L[𝕜] K × X))
  have he_apply (x : X) : (A (0, x)).1 = e x := by
    have hx := DFunLike.congr_fun he x
    simpa [blockCorner] using hx
  have hA_decomp (k : K) (x : X) :
      A (k, x) = A (k, 0) + A (0, x) := by
    simpa using (A.comp_inl_add_comp_inr (k, x)).symm
  have hP_apply (k : K) (x : X) :
      (P : K × X →L[𝕜] K × X) (k, x) = (k, x - bInvA k) := by
    simp [P, sub_eq_add_neg]
  have hQ_apply (y : Y) (z : C) :
      (Q : Y × C →L[𝕜] Y × C) (y, z) = (y, z - dBInv y) := by
    simp [Q, sub_eq_add_neg]
  have ha_apply (k : K) : (A (k, 0)).1 = a k := by
    simp [a, fstY, inlK]
  have hc_apply (k : K) : (A (k, 0)).2 = c k := by
    simp [c, sndC, inlK]
  have hd_apply (x : X) : (A (0, x)).2 = d x := by
    simp [d, sndC, inrX]
  have hA_fst_apply (k : K) (x : X) : (A (k, x)).1 = a k + e x := by
    rw [hA_decomp]
    simp only [Prod.fst_add, ha_apply, he_apply]
  have hA_snd_apply (k : K) (x : X) : (A (k, x)).2 = c k + d x := by
    rw [hA_decomp]
    simp only [Prod.snd_add, hc_apply, hd_apply]
  have hA_apply (k : K) (x : X) :
      A (k, x) = (a k + e x, c k + d x) :=
    Prod.ext (hA_fst_apply k x) (hA_snd_apply k x)
  -- After both shears, `A` is the product of its finite-dimensional Schur complement and
  -- the equivalence `e`, up to swapping the two target factors.
  have hB :
      B = (swap : C × Y →L[𝕜] Y × C).comp
        (schur.prodMap (e : X →L[𝕜] Y)) := by
    apply ContinuousLinearMap.ext
    rintro ⟨k, x⟩
    simp only [B, ContinuousLinearMap.comp_apply]
    rw [hP_apply, hA_apply, hQ_apply]
    apply Prod.ext
    · simp [bInvA, schur, swap, map_sub]
    · simp [bInvA, dBInv, schur, swap, map_sub]
      abel
  have hSchur : IsFredholm schur := isFredholm_of_finiteDimensional schur
  have heFredholm : IsFredholm (e : X →L[𝕜] Y) :=
    IsFredholm.of_continuousLinearEquiv e
  have hBfredholm : IsFredholm B := by
    rw [hB]
    exact (hSchur.prodMap heFredholm).equiv_comp swap
  -- Undoing the shears preserves both Fredholmness and the index.
  have hrecover :
      A = (Q.symm : Y × C →L[𝕜] Y × C).comp
        (B.comp (P.symm : K × X →L[𝕜] K × X)) := by
    apply ContinuousLinearMap.ext
    intro z
    simp [B]
  have hA : IsFredholm A := by
    rw [hrecover]
    exact (hBfredholm.comp_equiv P.symm).equiv_comp Q.symm
  refine ⟨hA, ?_⟩
  calc
    ContinuousLinearMap.index A = ContinuousLinearMap.index B := by
      rw [hrecover]
      simp
    _ = ContinuousLinearMap.index (schur.prodMap (e : X →L[𝕜] Y)) := by
      rw [hB]
      simp
    _ = ContinuousLinearMap.index schur +
        ContinuousLinearMap.index (e : X →L[𝕜] Y) :=
      ContinuousLinearMap.index_prodMap schur (e : X →L[𝕜] Y) hSchur heFredholm
    _ = ((finrank 𝕜 K : ℤ) - finrank 𝕜 C) + 0 := by
      rw [ContinuousLinearMap.index_eq_of_finiteDimensional]
      simp
    _ = (finrank 𝕜 K : ℤ) - finrank 𝕜 C := add_zero _

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- Fredholmness and the Fredholm index are stable in a neighbourhood of a Fredholm operator. -/
theorem IsFredholm.eventually_isFredholm_and_index_eq {T : E →L[𝕜] F}
    (hT : IsFredholm T) :
    ∀ᶠ S : E →L[𝕜] F in 𝓝 T,
      IsFredholm S ∧ ContinuousLinearMap.index S = ContinuousLinearMap.index T := by
  letI := hT.finiteDimensional_ker
  letI := hT.finiteDimensional_coker
  letI : CompleteSpace hT.kerComplement := hT.isClosed_kerComplement.completeSpace_coe
  letI : CompleteSpace (LinearMap.range (T : E →ₗ[𝕜] F)) :=
    hT.isClosed_range.completeSpace_coe
  let domainEquiv := hT.kerProdComplementEquiv
  let codomainEquiv := hT.rangeProdCokerComplementEquiv
  let A (S : E →L[𝕜] F) :
      (LinearMap.ker (T : E →ₗ[𝕜] F) × hT.kerComplement) →L[𝕜]
        (LinearMap.range (T : E →ₗ[𝕜] F) × hT.cokerComplement) :=
    (codomainEquiv.symm : F →L[𝕜]
      LinearMap.range (T : E →ₗ[𝕜] F) × hT.cokerComplement).comp
      (S.comp (domainEquiv :
        (LinearMap.ker (T : E →ₗ[𝕜] F) × hT.kerComplement) →L[𝕜] E))
  let D (S : E →L[𝕜] F) :
      hT.kerComplement →L[𝕜] LinearMap.range (T : E →ₗ[𝕜] F) :=
    blockCorner (A S)
  -- For `T`, the distinguished corner is exactly the equivalence from the chosen kernel
  -- complement onto the range.
  have hDT : D T = (hT.kerComplementEquivRange :
      hT.kerComplement →L[𝕜] LinearMap.range (T : E →ₗ[𝕜] F)) := by
    ext x
    simp [D, A, blockCorner, domainEquiv, codomainEquiv]
  have hD : Continuous D := by
    dsimp only [D, A, blockCorner]
    fun_prop
  -- Equivalences form an open subset of the operator space, so this corner remains invertible
  -- for all operators in a neighbourhood of `T`.
  have hnhds :
      D ⁻¹' Set.range ((↑) :
        (hT.kerComplement ≃L[𝕜] LinearMap.range (T : E →ₗ[𝕜] F)) →
          hT.kerComplement →L[𝕜] LinearMap.range (T : E →ₗ[𝕜] F)) ∈ 𝓝 T := by
    apply hD.continuousAt.preimage_mem_nhds
    rw [hDT]
    exact ContinuousLinearEquiv.nhds hT.kerComplementEquivRange
  filter_upwards [hnhds] with S hS
  obtain ⟨e, he⟩ := hS
  have hA := isFredholm_and_index_eq_of_blockCorner_equiv (A S) e he.symm
  have hSfredholm : IsFredholm S := by
    have hAS : IsFredholm (A S) := hA.1
    have hrecover :
        S = (codomainEquiv : _ →L[𝕜] F).comp
          ((A S).comp (domainEquiv.symm : E →L[𝕜] _)) := by
      ext x
      simp [A]
    rw [hrecover]
    exact (hAS.comp_equiv domainEquiv.symm).equiv_comp codomainEquiv
  refine ⟨hSfredholm, ?_⟩
  have hindexAS : ContinuousLinearMap.index (A S) =
      (finrank 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F)) : ℤ) -
        finrank 𝕜 hT.cokerComplement :=
    hA.2
  rw [ContinuousLinearMap.index_eq_finrank_sub T,
    LinearEquiv.finrank_eq hT.cokerEquivComplement.toLinearEquiv]
  calc
    ContinuousLinearMap.index S = ContinuousLinearMap.index (A S) := by
      simp [A]
    _ = _ := hindexAS

/-- A sufficiently small operator-norm perturbation of a Fredholm operator is Fredholm with the
same index. -/
theorem IsFredholm.exists_pos_isFredholm_and_index_eq_of_norm_sub_lt
    {T : E →L[𝕜] F} (hT : IsFredholm T) :
    ∃ ε > 0, ∀ S : E →L[𝕜] F, ‖S - T‖ < ε →
      IsFredholm S ∧ ContinuousLinearMap.index S = ContinuousLinearMap.index T := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp hT.eventually_isFredholm_and_index_eq
  exact ⟨ε, hε, fun S hS => hball (by simpa [dist_eq_norm] using hS)⟩

/-- The set of Fredholm operators between two Banach spaces is open in the operator norm
topology. -/
theorem isOpen_setOf_isFredholm :
    IsOpen {T : E →L[𝕜] F | IsFredholm T} := by
  rw [isOpen_iff_mem_nhds]
  intro T hT
  filter_upwards [hT.eventually_isFredholm_and_index_eq] with S hS
  exact hS.1

/-- For every integer `n`, the set of Fredholm operators of index `n` is open in the operator
norm topology. -/
theorem isOpen_setOf_isFredholm_index_eq (n : ℤ) :
    IsOpen {T : E →L[𝕜] F |
      IsFredholm T ∧ ContinuousLinearMap.index T = n} := by
  rw [isOpen_iff_mem_nhds]
  rintro T ⟨hT, hindex⟩
  filter_upwards [hT.eventually_isFredholm_and_index_eq] with S hS
  exact ⟨hS.1, hS.2.trans hindex⟩

end TauCeti

end
