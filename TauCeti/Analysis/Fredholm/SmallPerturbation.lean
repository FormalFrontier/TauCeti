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

omit [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜] in
/-- Block elimination. Write the operator as the block matrix `!![a, e; c, d]`, acting by
`(k, x) ↦ (a k + e x, c k + d x)`, and suppose the corner `e : X → Y` is invertible. Shearing the
domain by `x ↦ x - e⁻¹ a k` kills `a`, and then shearing the codomain by `z ↦ z - d e⁻¹ y` kills
`d`. What survives is the anti-diagonal `!![0, e; c - d e⁻¹ a, 0]` — the direct sum of `e` with
the Schur complement `c - d e⁻¹ a`, with the two target factors interchanged, which is where the
swap in the statement comes from.

Only the factorization is recorded, not the Schur complement itself: all the index computation
needs is that the remaining factor is *some* operator `K → C`, since between finite-dimensional
spaces every operator has index `finrank K - finrank C`. -/
private theorem exists_factorization_of_blocks
    {K X Y C : Type*}
    [NormedAddCommGroup K] [NormedSpace 𝕜 K]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C]
    (A : K × X →L[𝕜] Y × C) (a : K →L[𝕜] Y) (c : K →L[𝕜] C) (d : X →L[𝕜] C) (e : X ≃L[𝕜] Y)
    (hA : ∀ (k : K) (x : X), A (k, x) = (a k + e x, c k + d x)) :
    ∃ (f : K →L[𝕜] C) (P : (K × X) ≃L[𝕜] (K × X)) (Q : (C × Y) ≃L[𝕜] (Y × C)),
      A = (Q : C × Y →L[𝕜] Y × C).comp
        ((f.prodMap (e : X →L[𝕜] Y)).comp (P : K × X →L[𝕜] K × X)) := by
  -- The two shears here are the *inverses* of the eliminating ones: the domain shear adds
  -- `e⁻¹ a` and the codomain shear adds `d e⁻¹`, the latter composed with the swap that puts
  -- the two target factors back in their original order.
  refine ⟨c - d.comp ((e.symm : Y →L[𝕜] X).comp a),
    (ContinuousLinearEquiv.refl 𝕜 K).skewProd (ContinuousLinearEquiv.refl 𝕜 X)
      ((e.symm : Y →L[𝕜] X).comp a),
    (LinearIsometryEquiv.prodComm 𝕜 C Y).toContinuousLinearEquiv.trans
      ((ContinuousLinearEquiv.refl 𝕜 Y).skewProd (ContinuousLinearEquiv.refl 𝕜 C)
        (d.comp (e.symm : Y →L[𝕜] X))), ?_⟩
  apply ContinuousLinearMap.ext
  rintro ⟨k, x⟩
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  apply Prod.ext
  · simp [hA, add_comm]
  · simp [hA, map_add]

omit [IsRCLikeNormedField 𝕜] in
private theorem isFredholm_and_index_eq_of_blocks
    {K X Y C : Type*}
    [NormedAddCommGroup K] [NormedSpace 𝕜 K] [FiniteDimensional 𝕜 K]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [FiniteDimensional 𝕜 C]
    (A : K × X →L[𝕜] Y × C) (a : K →L[𝕜] Y) (c : K →L[𝕜] C) (d : X →L[𝕜] C) (e : X ≃L[𝕜] Y)
    (hA : ∀ (k : K) (x : X), A (k, x) = (a k + e x, c k + d x)) :
    IsFredholm A ∧
      ContinuousLinearMap.index A = (finrank 𝕜 K : ℤ) - finrank 𝕜 C := by
  letI : CompleteSpace K := FiniteDimensional.complete 𝕜 K
  letI : CompleteSpace C := FiniteDimensional.complete 𝕜 C
  obtain ⟨f, P, Q, hfac⟩ := exists_factorization_of_blocks A a c d e hA
  have hf : IsFredholm f := isFredholm_of_finiteDimensional f
  have he : IsFredholm (e : X →L[𝕜] Y) := IsFredholm.of_continuousLinearEquiv e
  have hprod : IsFredholm (f.prodMap (e : X →L[𝕜] Y)) := hf.prodMap he
  refine ⟨by rw [hfac]; exact (hprod.comp_equiv P).equiv_comp Q, ?_⟩
  calc
    ContinuousLinearMap.index A
        = ContinuousLinearMap.index (f.prodMap (e : X →L[𝕜] Y)) := by
      rw [hfac]; simp
    _ = ContinuousLinearMap.index f + ContinuousLinearMap.index (e : X →L[𝕜] Y) :=
      ContinuousLinearMap.index_prodMap f (e : X →L[𝕜] Y) hf he
    _ = ((finrank 𝕜 K : ℤ) - finrank 𝕜 C) + 0 := by
      rw [ContinuousLinearMap.index_eq_of_finiteDimensional]
      simp
    _ = (finrank 𝕜 K : ℤ) - finrank 𝕜 C := add_zero _

omit [IsRCLikeNormedField 𝕜] in
private theorem isFredholm_and_index_eq_of_blockCorner_equiv
    {K X Y C : Type*}
    [NormedAddCommGroup K] [NormedSpace 𝕜 K] [FiniteDimensional 𝕜 K]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [FiniteDimensional 𝕜 C]
    (A : K × X →L[𝕜] Y × C) (e : X ≃L[𝕜] Y)
    (he : blockCorner A = (e : X →L[𝕜] Y)) :
    IsFredholm A ∧
      ContinuousLinearMap.index A = (finrank 𝕜 K : ℤ) - finrank 𝕜 C := by
  -- Read off the other three corners of `A`, so that `isFredholm_and_index_eq_of_blocks`
  -- applies. The hypothesis `he` names the fourth.
  let fstY := ContinuousLinearMap.fst 𝕜 Y C
  let sndC := ContinuousLinearMap.snd 𝕜 Y C
  let inlK := ContinuousLinearMap.inl 𝕜 K X
  let inrX := ContinuousLinearMap.inr 𝕜 K X
  refine isFredholm_and_index_eq_of_blocks A (fstY.comp (A.comp inlK))
    (sndC.comp (A.comp inlK)) (sndC.comp (A.comp inrX)) e fun k x => ?_
  have he_apply : (A (0, x)).1 = e x := by
    have hx := DFunLike.congr_fun he x
    simpa [blockCorner] using hx
  have hA_decomp : A (k, x) = A (k, 0) + A (0, x) := by
    simpa using (A.comp_inl_add_comp_inr (k, x)).symm
  refine Prod.ext ?_ ?_
  · rw [hA_decomp]
    simp only [Prod.fst_add, he_apply]
    simp [fstY, inlK]
  · rw [hA_decomp]
    simp only [Prod.snd_add]
    simp [sndC, inlK, inrX]

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

omit [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜] in
/-- **Invertibility is an open condition along a family continuous at a point.** If `D T` is an
equivalence and `D` is continuous at `T`, then `D S` is an equivalence for every `S` near `T`.

This is the sole topological input to the stability theorem; nothing in it is specific to block
forms. -/
private theorem eventually_exists_continuousLinearEquiv_eq {G : Type*} [TopologicalSpace G]
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {D : G → (X →L[𝕜] Y)} {T : G} (hD : ContinuousAt D T) {e₀ : X ≃L[𝕜] Y}
    (hT : D T = (e₀ : X →L[𝕜] Y)) :
    ∀ᶠ S in 𝓝 T, ∃ e : X ≃L[𝕜] Y, D S = (e : X →L[𝕜] Y) := by
  -- Mathlib's `ContinuousLinearEquiv.nhds` says the equivalences are a neighbourhood of each of
  -- their members; continuity at `T` pulls that back along `D`.
  have hmem : D ⁻¹' Set.range ((↑) : (X ≃L[𝕜] Y) → (X →L[𝕜] Y)) ∈ 𝓝 T := by
    apply hD.preimage_mem_nhds
    rw [hT]
    exact ContinuousLinearEquiv.nhds e₀
  filter_upwards [hmem] with S hS
  obtain ⟨e, he⟩ := hS
  exact ⟨e, he.symm⟩

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- **A splitting with an invertible corner makes an operator Fredholm.** Suppose the domain splits
as `K × X` and the codomain as `Y × C`, with `K` and `C` finite-dimensional, and that in the
resulting block form of `S` the corner `X → Y` is an equivalence. Then `S` is Fredholm of index
`finrank K - finrank C`. -/
private theorem isFredholm_and_index_eq_of_splitting
    {K X Y C : Type*}
    [NormedAddCommGroup K] [NormedSpace 𝕜 K] [FiniteDimensional 𝕜 K]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [FiniteDimensional 𝕜 C]
    (S : E →L[𝕜] F) (p : (K × X) ≃L[𝕜] E) (q : (Y × C) ≃L[𝕜] F) {e : X ≃L[𝕜] Y}
    (he : blockCorner ((q.symm : F →L[𝕜] Y × C).comp (S.comp (p : K × X →L[𝕜] E))) =
      (e : X →L[𝕜] Y)) :
    IsFredholm S ∧
      ContinuousLinearMap.index S = (finrank 𝕜 K : ℤ) - finrank 𝕜 C := by
  -- Conjugating by the two splitting equivalences changes neither Fredholmness nor the index, so
  -- this is `isFredholm_and_index_eq_of_blockCorner_equiv` transported along `p` and `q`.
  set A := (q.symm : F →L[𝕜] Y × C).comp (S.comp (p : K × X →L[𝕜] E)) with hAdef
  obtain ⟨hAfredholm, hAindex⟩ := isFredholm_and_index_eq_of_blockCorner_equiv A e he
  have hrecover : S = (q : Y × C →L[𝕜] F).comp (A.comp (p.symm : E →L[𝕜] K × X)) := by
    ext x
    simp [hAdef]
  refine ⟨by rw [hrecover]; exact (hAfredholm.comp_equiv p.symm).equiv_comp q, ?_⟩
  rw [← hAindex, hrecover]
  simp

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
  filter_upwards [eventually_exists_continuousLinearEquiv_eq hD.continuousAt hDT] with S hS
  obtain ⟨e, he⟩ := hS
  obtain ⟨hSfredholm, hSindex⟩ :=
    isFredholm_and_index_eq_of_splitting S domainEquiv codomainEquiv he
  refine ⟨hSfredholm, ?_⟩
  rw [hSindex, ContinuousLinearMap.index_eq_finrank_sub T,
    LinearEquiv.finrank_eq hT.cokerEquivComplement.toLinearEquiv]

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
