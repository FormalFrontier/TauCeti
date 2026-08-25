/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Local frames: duality with the coefficient functionals, and testing hom-bundle sections

Let `V → M` be a smooth vector bundle, let `e` be a trivialization of `V` and let `b` be a basis
of the model fibre, so that `e.localFrame b` is a local frame of `V` over `e.baseSet` with
coefficient functionals `e.localFrameCoeff I b`. This file records that over `e.baseSet` the frame
and its coefficient functionals are dual to each other: the `i`-th functional takes the value `1`
on the `i`-th frame vector and `0` on the others.

It then uses a local frame of the *source* bundle to test smoothness of a section of a bundle of
continuous linear maps: such a section is `C^n` on an open subset of the two base sets as soon as
its evaluations on the frame sections are. Read through a trivialization, a continuous linear map
out of a finite-dimensional space is recovered from its values on a basis by
`T = ∑ j, (b.coord j).smulRight (T (b j))`, and each summand depends continuously linearly on
`T (b j)`. This is the criterion through which a covariant derivative is proved to be `C^n`:
`ContMDiffCovariantDerivativeOn` asks for smoothness of the hom-bundle section `∇σ`, while the
constructions of connections produce smoothness of the vector fields `∇_X σ` one direction `X` at
a time.

## Main results

* `TauCeti.Manifold.localFrameCoeff_basisAt`: the coefficient functionals are dual to the basis
  `e.basisAt b hx` of the fibre at a point of `e.baseSet`.
* `TauCeti.Manifold.localFrameCoeff_localFrame`: the same duality, stated for the frame sections
  themselves.
* `TauCeti.Manifold.contMDiffOn_hom_of_localFrame`: a section of the bundle of continuous linear
  maps is `C^n` once its evaluations on a local frame of the source bundle are.
-/

public section

open Bundle Module Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
  {x : M} {ι : Type*} (b : Basis ι 𝕜 F)
  {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]

/-- A local frame is dual to its own coefficient functionals on the basis sections at `x`. -/
@[simp]
theorem localFrameCoeff_basisAt [DecidableEq ι] (hx : x ∈ e.baseSet) (i j : ι) :
    e.localFrameCoeff I b i x (e.basisAt b hx j) = if i = j then 1 else 0 := by
  rw [← e.localFrame_apply_of_mem_baseSet b hx,
    e.localFrameCoeff_apply_of_mem_baseSet b hx (e.localFrame b j) i,
    e.localFrame_apply_of_mem_baseSet b hx, Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]

/-- A local frame is dual to its own coefficient functionals. -/
theorem localFrameCoeff_localFrame [DecidableEq ι] (hx : x ∈ e.baseSet) (i j : ι) :
    e.localFrameCoeff I b i x (e.localFrame b j x) = if i = j then 1 else 0 := by
  rw [e.localFrame_apply_of_mem_baseSet b hx, localFrameCoeff_basisAt b hx]

/-! ### Testing a hom-bundle section on a local frame -/

section Hom

variable [Finite ι] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')]
  [∀ x, AddCommGroup (V' x)] [∀ x, Module 𝕜 (V' x)] [∀ x, TopologicalSpace (V' x)]
  [FiberBundle F' V'] [VectorBundle 𝕜 F' V']
  {e' : Trivialization F' (TotalSpace.proj : TotalSpace F' V' → M)} [MemTrivializationAtlas e']
  {n : ℕ∞ω} {u : Set M}

omit [ContMDiffVectorBundle 1 F V I] [Finite ι] in
/-- A continuous linear map out of a finite-dimensional space is the sum, over a basis of the
source, of the `smulRight`s of its values on that basis. -/
private theorem eq_sum_coord_smulRight [Fintype ι] (T : F →L[𝕜] F') :
    T = ∑ j, (LinearMap.toContinuousLinearMap (b.coord j)).smulRight (T (b j)) := by
  classical
  refine ContinuousLinearMap.coe_injective (b.ext fun j ↦ ?_)
  simp [Basis.coord_apply, Finsupp.single_apply]

variable [∀ x, IsTopologicalAddGroup (V' x)] [∀ x, ContinuousSMul 𝕜 (V' x)]
  [ContMDiffVectorBundle n F V I] [ContMDiffVectorBundle n F' V' I]

omit [ContMDiffVectorBundle 1 F V I] in
/-- **A hom-bundle section is tested on a local frame.** A section `A` of the bundle of continuous
linear maps from `V` to `V'` is `C^n` on an open subset of `e.baseSet ∩ e'.baseSet` as soon as each
of its evaluations `A (e.localFrame b j)` on the local frame of the source bundle is. -/
theorem contMDiffOn_hom_of_localFrame (hu : IsOpen u)
    (hu' : u ⊆ e.baseSet ∩ e'.baseSet) {A : Π y : M, V y →L[𝕜] V' y}
    (hA : ∀ j : ι, ContMDiffOn I (I.prod 𝓘(𝕜, F')) n
      (fun y ↦ TotalSpace.mk' F' y (A y (e.localFrame b j y))) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F →L[𝕜] F')) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F') y (A y)) u := by
  have : Fintype ι := Fintype.ofFinite ι
  set eh := e.continuousLinearMap (RingHom.id 𝕜) e' with heh
  rw [eh.contMDiffOn_section_iff hu hu']
  -- The `j`-th coordinate of the trivialized section is the trivialized evaluation on the frame.
  have key {y : M} (hy : y ∈ u) (j : ι) :
      (eh ⟨y, A y⟩).2 (b j) = (e' ⟨y, A y (e.localFrame b j y)⟩).2 := by
    rw [heh, Bundle.Trivialization.continuousLinearMap_apply]
    simp only [ContinuousLinearMap.comp_apply]
    rw [e.symmL_apply (hu' hy).1]
    have hframe : e.symm y (b j) = e.localFrame b j y := by
      simp [Bundle.Trivialization.localFrame_apply_of_mem_baseSet,
        Bundle.Trivialization.basisAt, (hu' hy).1]
    rw [hframe, Bundle.Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 e' (hu' hy).2]
  have hcoord (j : ι) : ContMDiffOn I 𝓘(𝕜, F') n (fun y ↦ (eh ⟨y, A y⟩).2 (b j)) u := by
    refine ContMDiffOn.congr ?_ fun y hy ↦ key hy j
    exact (e'.contMDiffOn_section_iff hu (hu'.trans inter_subset_right)).1 (hA j)
  have hsum : ContMDiffOn I 𝓘(𝕜, F →L[𝕜] F') n
      (fun y ↦ ∑ j, (LinearMap.toContinuousLinearMap (b.coord j)).smulRight
        ((eh ⟨y, A y⟩).2 (b j))) u := by
    refine contMDiffOn_finsetSum fun j _ ↦ ?_
    exact ContMDiffOn.clm_apply
      (g := fun _ ↦ ContinuousLinearMap.smulRightL 𝕜 F F'
        (LinearMap.toContinuousLinearMap (b.coord j))) contMDiffOn_const (hcoord j)
  exact hsum.congr fun y _ ↦ eq_sum_coord_smulRight b _

end Hom

end TauCeti.Manifold
