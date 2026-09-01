/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.LinearAlgebra.Graded.LinearMap
public import TauCeti.LinearAlgebra.TensorProduct.Decomposition

/-!
# Tensor products of internally graded modules

The tensor product of internally `ℤ`-graded modules is graded by total degree. Its degree-`n`
piece is the sum of the images of

`G.piece p ⊗ H.piece (n - p)`

inside the ambient tensor product. These pieces form an internal direct sum: first use
`DirectSum.IsInternal.tensorProduct` for the bidegree decomposition, then collect bidegrees with
the same sum.

The resulting grading has the expected API on pure tensors. In particular, a tensor of elements
of degrees `p` and `q` has degree `p + q`, and tensoring homogeneous linear maps adds their
degrees. This is the tensor-product compatibility requested in Layer 0 of the `DGAInfinity`
roadmap and supplies the grading used by tensor products of DG objects.

## Main definitions

* `TauCeti.InternalGrading.tensorProduct`: the internal total-degree grading.

## Main results

* `TauCeti.InternalGrading.tensorProduct_piece_eq_iSup`: the degree-`n` piece is the sum over
  `G.piece p ⊗ H.piece (n - p)`.
* `TauCeti.InternalGrading.tmul_mem_tensorProduct`: degrees add on pure tensors.
* `TauCeti.LinearMap.IsHomogeneous.tensorProduct`: tensoring homogeneous maps adds their degrees.

The proof reuses Tau Ceti's two-factor internal decomposition theorem
`DirectSum.IsInternal.tensorProduct`; no formalization is vendored.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

universe u v w v' w'

namespace InternalGrading

section Pieces

variable {R : Type u} [CommSemiring R]
variable {M : Type v} {N : Type w}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The bidegree-`(p, q)` submodule in a tensor product of internally graded modules. -/
private def tensorProductBidegreePiece (G : InternalGrading R M) (H : InternalGrading R N)
    (d : ℤ × ℤ) : Submodule R (M ⊗[R] N) :=
  Submodule.map₂ (TensorProduct.mk R M N) (G.piece d.1) (H.piece d.2)

private def tensorProductPiece (G : InternalGrading R M) (H : InternalGrading R N) (n : ℤ) :
    Submodule R (M ⊗[R] N) :=
  ⨆ d : ℤ × ℤ, ⨆ _ : d.1 + d.2 = n, tensorProductBidegreePiece G H d

private theorem tensorProductPiece_eq_iSup (G : InternalGrading R M)
    (H : InternalGrading R N) (n : ℤ) :
    tensorProductPiece G H n =
      ⨆ p : ℤ, Submodule.map₂ (TensorProduct.mk R M N) (G.piece p) (H.piece (n - p)) := by
  apply le_antisymm
  · refine iSup_le fun d ↦ iSup_le fun hd ↦ ?_
    refine le_iSup_of_le d.1 ?_
    have hdeg : d.2 = n - d.1 := by omega
    simpa only [tensorProductBidegreePiece, hdeg] using
      (le_rfl : Submodule.map₂ (TensorProduct.mk R M N) (G.piece d.1)
        (H.piece (n - d.1)) ≤ _)
  · refine iSup_le fun p ↦ ?_
    refine le_iSup_of_le (p, n - p) ?_
    refine le_iSup_of_le (by omega) ?_
    rfl

end Pieces

section Internal

variable {R : Type u} [CommSemiring R]
variable {M : Type v} {N : Type w}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Regrouping a family by the fibers of a degree map does not alter its supremum. -/
private theorem iSup_fiber_eq_iSup {I J : Type*} (P : I → Submodule R M) (degree : I → J) :
    (⨆ j, ⨆ i, ⨆ _ : degree i = j, P i) = ⨆ i, P i := by
  apply le_antisymm
  · exact iSup_le fun _ ↦ iSup_le fun i ↦ iSup_le fun _ ↦ le_iSup P i
  · exact iSup_le fun i ↦
      le_iSup_of_le (degree i) (le_iSup_of_le i (le_iSup_of_le rfl le_rfl))

/-- Projection onto each fiber proves that the canonical recomposition map for the collected
pieces is injective. -/
private theorem coeLinearMap_iSup_fiber_injective {I J : Type*} [DecidableEq I] [DecidableEq J]
    {P : I → Submodule R M} (hP : DirectSum.IsInternal P) (degree : I → J) :
    Function.Injective <| DirectSum.coeLinearMap fun j ↦ ⨆ i, ⨆ _ : degree i = j, P i := by
  let Q : J → Submodule R M := fun j ↦ ⨆ i, ⨆ _ : degree i = j, P i
  let _ : DirectSum.Decomposition P := hP.chooseDecomposition
  let projection (j : J) : M →ₗ[R] M :=
    (DirectSum.toModule R I M fun i ↦
      if degree i = j then (P i).subtype else 0) ∘ₗ
        (DirectSum.decomposeLinearEquiv P).toLinearMap
  have projection_piece (j : J) (i : I) {x : M} (hx : x ∈ P i) :
      projection j x = if degree i = j then x else 0 := by
    dsimp only [projection]
    rw [LinearMap.comp_apply]
    -- The decomposition lemma takes an element of the summand; `hx` supplies that subtype view.
    change (DirectSum.toModule R I M fun i ↦
      if degree i = j then (P i).subtype else 0)
        ((DirectSum.decomposeLinearEquiv P) (⟨x, hx⟩ : P i)) = _
    rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]
    split <;> rfl
  have Q_eq (j : J) : Q j = ⨆ i : {i // degree i = j}, P i := by
    apply le_antisymm
    · refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
      exact le_iSup_of_le ⟨i, hi⟩ le_rfl
    · exact iSup_le fun i ↦ le_iSup_of_le i.1 (le_iSup_of_le i.2 le_rfl)
  have projection_mem (j k : J) {x : M} (hx : x ∈ Q k) :
      projection j x = if k = j then x else 0 := by
    rw [Q_eq] at hx
    refine Submodule.iSup_induction (fun i : {i // degree i = k} ↦ P i)
      (motive := fun y ↦ projection j y = if k = j then y else 0) hx
      (fun i x hx ↦ ?_) (by simp) (fun x y ihx ihy ↦ ?_)
    · simpa only [i.property] using projection_piece j i hx
    · simp only [map_add, ihx, ihy, ite_add_zero]
  have projection_coe (j : J) (z : ⨁ k, ↥(Q k)) :
      projection j (DirectSum.coeLinearMap Q z) = z j := by
    induction z using DirectSum.induction_on with
    | zero => simp
    | of k x =>
        rw [DirectSum.coeLinearMap_of, projection_mem j k x.property]
        simp only [DirectSum.coe_of_apply]
        split <;> rfl
    | add x y ihx ihy =>
        rw [map_add (DirectSum.coeLinearMap Q), map_add (projection j), ihx, ihy]
        rfl
  intro x y hxy
  apply DirectSum.ext fun j ↦ Subtype.ext ?_
  exact (projection_coe j x).symm.trans ((congrArg (projection j) hxy).trans
    (projection_coe j y))

/-- Collecting an internal decomposition along an arbitrary degree map again gives an internal
decomposition. This local form is used to collect tensor bidegrees by their sum. -/
private theorem isInternal_iSup_fiber {I J : Type*} [DecidableEq I] [DecidableEq J]
    {P : I → Submodule R M} (hP : DirectSum.IsInternal P) (degree : I → J) :
    DirectSum.IsInternal fun j ↦ ⨆ i, ⨆ _ : degree i = j, P i := by
  -- `IsInternal` uses the canonical additive recomposition map. For submodules its underlying
  -- function is definitionally the canonical linear recomposition map used below.
  change Function.Bijective (DirectSum.coeLinearMap fun j ↦ ⨆ i, ⨆ _ : degree i = j, P i)
  refine ⟨coeLinearMap_iSup_fiber_injective hP degree, ?_⟩
  rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap]
  rw [iSup_fiber_eq_iSup P degree]
  exact hP.submodule_iSup_eq_top

/-- The tensor product of internally graded modules, graded by total degree. -/
noncomputable def tensorProduct (G : InternalGrading R M) (H : InternalGrading R N) :
    InternalGrading R (M ⊗[R] N) where
  piece := tensorProductPiece G H
  isInternal := by
    -- The reused theorem is declared in a `Classical` scope, whereas `InternalGrading` fixes the
    -- canonical decidable equality on `ℤ`; transport the two input decompositions across that
    -- implementation-only difference before applying it.
    classical
    have hG : @DirectSum.IsInternal ℤ M (Submodule R M) (Classical.decEq ℤ)
        _ _ _ G.piece := by
      have hdec : (Int.instDecidableEq : DecidableEq ℤ) = Classical.decEq ℤ :=
        Subsingleton.elim _ _
      exact hdec ▸ G.isInternal
    have hH : @DirectSum.IsInternal ℤ N (Submodule R N) (Classical.decEq ℤ)
        _ _ _ H.piece := by
      have hdec : (Int.instDecidableEq : DecidableEq ℤ) = Classical.decEq ℤ :=
        Subsingleton.elim _ _
      exact hdec ▸ H.isInternal
    apply isInternal_iSup_fiber
    -- Unfold the private bidegree wrapper to match the reused tensor-product decomposition.
    change DirectSum.IsInternal fun d : ℤ × ℤ ↦
      Submodule.map₂ (TensorProduct.mk R M N) (G.piece d.1) (H.piece d.2)
    have hPair := DirectSum.IsInternal.tensorProduct G.piece H.piece hG hH
    -- Only the proof-irrelevant decidable-equality and additive instances now differ.
    convert hPair using 1

/-- The degree-`n` piece of the tensor-product grading is the sum of the tensor-product images
whose first degree is `p` and whose second degree is `n - p`. -/
theorem tensorProduct_piece_eq_iSup (G : InternalGrading R M) (H : InternalGrading R N) (n : ℤ) :
    (G.tensorProduct H).piece n =
      ⨆ p : ℤ, Submodule.map₂ (TensorProduct.mk R M N) (G.piece p) (H.piece (n - p)) :=
  tensorProductPiece_eq_iSup G H n

/-- A pure tensor of elements of degrees `p` and `q` is homogeneous of degree `p + q` in the
tensor-product grading. -/
theorem tmul_mem_tensorProduct (G : InternalGrading R M) (H : InternalGrading R N)
    {p q : ℤ} {x : M} {y : N} (hx : x ∈ G.piece p) (hy : y ∈ H.piece q) :
    x ⊗ₜ[R] y ∈ (G.tensorProduct H).piece (p + q) := by
  rw [tensorProduct_piece_eq_iSup]
  refine Submodule.mem_iSup_of_mem p ?_
  simpa only [add_sub_cancel_left, TensorProduct.mk_apply] using
    Submodule.apply_mem_map₂ (TensorProduct.mk R M N) hx hy

end Internal

end InternalGrading

namespace LinearMap.IsHomogeneous

variable {R : Type u} [CommSemiring R]
variable {M : Type v} {N : Type w} {M' : Type v'} {N' : Type w'}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']

/-- Tensoring homogeneous linear maps adds their degrees for the total tensor-product gradings. -/
@[grind →]
theorem tensorProduct {G : InternalGrading R M} {H : InternalGrading R N}
    {G' : InternalGrading R M'} {H' : InternalGrading R N'} {f : M →ₗ[R] M'} {g : N →ₗ[R] N'}
    {a b : ℤ} (hf : LinearMap.IsHomogeneous f G.piece G'.piece a)
    (hg : LinearMap.IsHomogeneous g H.piece H'.piece b) :
    LinearMap.IsHomogeneous (TensorProduct.map f g) (G.tensorProduct H).piece
      (G'.tensorProduct H').piece (a + b) := by
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  rw [InternalGrading.tensorProduct_piece_eq_iSup] at hz
  rw [InternalGrading.tensorProduct_piece_eq_iSup]
  let target := ⨆ p : ℤ,
    Submodule.map₂ (TensorProduct.mk R M' N') (G'.piece p)
      (H'.piece (n + (a + b) - p))
  suffices hmap : z ∈ (target.comap (TensorProduct.map f g)) by
    exact hmap
  have hle :
      (⨆ p : ℤ, Submodule.map₂ (TensorProduct.mk R M N) (G.piece p) (H.piece (n - p))) ≤
        target.comap (TensorProduct.map f g) := by
    refine iSup_le fun p ↦ Submodule.map₂_le.mpr fun x hx y hy ↦ ?_
    rw [Submodule.mem_comap, TensorProduct.mk_apply, TensorProduct.map_tmul]
    refine Submodule.mem_iSup_of_mem (p + a) ?_
    have hfx := hf.map_mem hx
    have hgy := hg.map_mem hy
    have hxy := Submodule.apply_mem_map₂ (TensorProduct.mk R M' N') hfx hgy
    have hdeg : n + (a + b) - (p + a) = n - p + b := by ring
    rw [hdeg]
    simpa only [TensorProduct.mk_apply] using hxy
  exact hle hz

end LinearMap.IsHomogeneous

end TauCeti
