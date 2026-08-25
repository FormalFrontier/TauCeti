/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Geometric invariance of the Laplacian

Mathlib's `Mathlib/Analysis/InnerProductSpace/Laplacian.lean` records that the Laplacian `Δ`
commutes with *left* composition by a continuous linear map or equivalence acting on the
*values* of a function (`ContDiffAt.laplacian_CLM_comp_left`, `laplacian_CLE_comp_left`).
This file supplies the complementary *right* composition, acting on the *domain* variable: the
geometric invariance of `Δ` under rigid motions and scalar homotheties of a Euclidean space:
affine isometry equivalences, with orthogonal changes of variable (linear isometry equivalences)
and translations as special cases, and affine homotheties with the expected quadratic scaling.

For an affine isometry equivalence `e : E ≃ᵃⁱ[ℝ] E'` and any `f : E' → F`,

`Δ (f ∘ e) = (Δ f) ∘ e`.

In particular, for a linear isometry equivalence `l : E ≃ₗᵢ[ℝ] E'`,

`Δ (f ∘ l) = (Δ f) ∘ l`,

and for a translation by `a : E`,

`Δ (fun y ↦ f (y + a)) = fun y ↦ (Δ f) (y + a)`.

All three identities hold with *no* differentiability hypothesis on `f`, because the underlying
`iteratedFDeriv` composition laws are unconditional (the iterated derivative is junk-valued off
the smooth locus, yet still transforms correctly under a linear change of variable). The harmonic
corollaries, where smoothness re-enters, live in the companion files
`TauCeti/Analysis/InnerProductSpace/Harmonic/Isometry.lean` and
`TauCeti/Analysis/InnerProductSpace/Harmonic/Dilation.lean`.

The file also records the base second-derivative computation `laplacian_norm_sq`
(`Δ ‖x‖² = 2 · dim E`), a reusable characteristic value of the Laplacian on the squared norm.

## Main declarations

* `TauCeti.laplacian_comp_affineIsometryEquiv_right`: `Δ (f ∘ e) = (Δ f) ∘ e` for an
  affine isometry equivalence `e`.
* `TauCeti.laplacian_comp_linearIsometryEquiv_right`: `Δ (f ∘ l) = (Δ f) ∘ l` for an
  isometry `l`.
* `TauCeti.laplacian_comp_add_right`: translation invariance of `Δ`.
* `TauCeti.laplacian_comp_homothety_right`: `Δ` scales by `c ^ 2` under
  `AffineMap.homothety a c`.
* `TauCeti.laplacian_comp_smul_right`: the origin-centered homothety special case.
* `TauCeti.laplacian_norm_sq`: `Δ (fun x => ‖x‖ ^ 2) x = 2 * dim E`, the Laplacian of the
  squared norm.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- Scalar dilation as a continuous linear equivalence. -/
private noncomputable abbrev smulLeftContinuousLinearEquiv (c : ℝ) (hc : c ≠ 0) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The iterated derivative transforms under a linear isometry equivalence on the right by
pulling the directions through the isometry. This is the unconditional engine behind the
geometric invariance of the Laplacian. -/
private theorem iteratedFDeriv_comp_linearIsometryEquiv_apply (l : E ≃ₗᵢ[ℝ] E') (f : E' → F)
    (i : ℕ) (x : E) (m : Fin i → E) :
    iteratedFDeriv ℝ i (f ∘ l) x m = iteratedFDeriv ℝ i f (l x) (fun j ↦ l (m j)) := by
  have h := l.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (x := x) (Set.mem_univ _) i
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  rw [← LinearIsometryEquiv.coe_toContinuousLinearEquiv l]
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

/-- **Geometric invariance of the Laplacian under isometries.** For a linear isometry
equivalence `l`, the Laplacian commutes with right composition by `l`:
`Δ (f ∘ l) = (Δ f) ∘ l`. No differentiability hypothesis is needed. -/
theorem laplacian_comp_linearIsometryEquiv_right (l : E ≃ₗᵢ[ℝ] E') (f : E' → F) :
    Δ (f ∘ l) = (Δ f) ∘ l := by
  ext x
  simp only [Function.comp_apply,
    laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ l) (stdOrthonormalBasis ℝ E),
    laplacian_eq_iteratedFDeriv_orthonormalBasis f ((stdOrthonormalBasis ℝ E).map l)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_comp_linearIsometryEquiv_apply l f 2 x]
  congr 1
  funext j
  fin_cases j <;> simp [OrthonormalBasis.map_apply]

/-- **Translation invariance of the Laplacian.** Shifting the argument by a constant `a`
commutes with the Laplacian: `Δ (fun y ↦ f (y + a)) = fun y ↦ (Δ f) (y + a)`. No
differentiability hypothesis is needed. -/
theorem laplacian_comp_add_right (f : E → F) (a : E) :
    Δ (fun y ↦ f (y + a)) = fun y ↦ (Δ f) (y + a) := by
  ext x
  simp only [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (stdOrthonormalBasis ℝ E)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_comp_add_right']

/-- **Geometric invariance of the Laplacian under affine isometries.** For an affine isometry
equivalence `e`, the Laplacian commutes with right composition by `e`:
`Δ (f ∘ e) = (Δ f) ∘ e`. No differentiability hypothesis is needed. -/
theorem laplacian_comp_affineIsometryEquiv_right (e : E ≃ᵃⁱ[ℝ] E') (f : E' → F) :
    Δ (f ∘ e) = (Δ f) ∘ e := by
  have hcomp : f ∘ e = (fun y ↦ f (y + e 0)) ∘ e.linearIsometryEquiv := by
    funext x
    have hx : e x = e.linearIsometryEquiv x + e 0 := by
      simpa using e.map_vadd (0 : E) x
    simp [Function.comp_apply, hx]
  rw [hcomp, laplacian_comp_linearIsometryEquiv_right e.linearIsometryEquiv
      (fun y ↦ f (y + e 0)),
    laplacian_comp_add_right f (e 0)]
  ext x
  have hx : e x = e.linearIsometryEquiv x + e 0 := by
    simpa using e.map_vadd (0 : E) x
  simp [Function.comp_apply, hx]

/-- **Scaling law for the Laplacian under origin-centered dilation.**

Right-composition by `x ↦ c • x` multiplies the Laplacian by `c ^ 2`. The statement is
unconditional in `f`, matching Mathlib's unconditional definition of `Δ` through iterated
Fréchet derivatives. -/
theorem laplacian_comp_smul_right (c : ℝ) (f : E → F) :
    Δ (fun x ↦ f (c • x)) = fun x ↦ c ^ 2 • (Δ f) (c • x) := by
  by_cases hc : c = 0
  · subst c
    ext x
    simp
  · let l : E ≃L[ℝ] E := smulLeftContinuousLinearEquiv c hc
    have hfun : (fun x : E ↦ f (c • x)) = f ∘ l := by
      funext x
      simp [l, smulLeftContinuousLinearEquiv]
    rw [hfun]
    ext x
    simp only [laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ l)
      (stdOrthonormalBasis ℝ E), laplacian_eq_iteratedFDeriv_orthonormalBasis f
      (stdOrthonormalBasis ℝ E), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hder :
        (iteratedFDeriv ℝ 2 (f ∘ l) x)
            ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i] =
          ((iteratedFDeriv ℝ 2 f (l x)).compContinuousLinearMap fun _ => (l : E →L[ℝ] E))
            ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i] := by
      have h := l.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (Set.mem_univ (l x)) 2
      simpa [← iteratedFDerivWithin_univ, Set.preimage_univ] using
        congrArg
          (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F =>
            L ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]) h
    rw [hder]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have hx : l x = c • x := by
      simp [l, smulLeftContinuousLinearEquiv]
    rw [hx]
    let M := iteratedFDeriv ℝ 2 f (c • x)
    let v : Fin 2 → E := ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]
    -- `compContinuousLinearMap_apply` exposes the two derivative directions as `fun j ↦ c • v j`;
    -- `map_smul_univ` then pulls the two scalar factors out of the bilinear map.
    change M (fun j => c • v j) = c ^ 2 • M v
    simpa [M, v, pow_two] using M.map_smul_univ (fun _ : Fin 2 => c) v

/-- **Scaling law for the Laplacian under a homothety.**

Right-composition by `AffineMap.homothety a c` multiplies the Laplacian by `c ^ 2`. -/
theorem laplacian_comp_homothety_right (a : E) (c : ℝ) (f : E → F) :
    Δ (fun x ↦ f (AffineMap.homothety a c x)) =
      fun x ↦ c ^ 2 • (Δ f) (AffineMap.homothety a c x) := by
  have hfun : (fun x : E ↦ f (AffineMap.homothety a c x)) =
      fun x ↦ (fun z ↦ f (c • z + a)) (x + -a) := by
    funext x
    simp [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, sub_eq_add_neg, add_comm]
  rw [hfun, laplacian_comp_add_right (fun z ↦ f (c • z + a)) (-a)]
  rw [laplacian_comp_smul_right c (fun z ↦ f (z + a))]
  rw [laplacian_comp_add_right f a]
  ext x
  simp [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, sub_eq_add_neg, add_comm]

/-- The Laplacian of the squared norm on a finite-dimensional real inner product space is twice
the dimension. -/
@[simp]
theorem laplacian_norm_sq (x : E) :
    Δ (fun y : E => ‖y‖ ^ 2) x = 2 * (Module.finrank ℝ E : ℝ) := by
  -- The Hessian of `‖·‖²` is the constant bilinear map `2 • innerSL ℝ`.
  have hsnd : fderiv ℝ (fderiv ℝ fun y : E => ‖y‖ ^ 2) x
      = (2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) := by
    rw [fderiv_norm_sq]
    exact (2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).fderiv
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis (fun y : E => ‖y‖ ^ 2)
    (stdOrthonormalBasis ℝ E)) x]
  -- Each orthonormal diagonal Hessian entry equals `2`.
  have hterm : ∀ i, iteratedFDeriv ℝ 2 (fun y : E => ‖y‖ ^ 2) x
      ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i] = 2 := by
    intro i
    have hself : (innerSL ℝ (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) = (1 : ℝ) := by
      rw [innerSL_apply_apply, real_inner_self_eq_norm_sq,
        (stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one i, one_pow]
    rw [iteratedFDeriv_two_apply, hsnd]
    simp [hself]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_comm]

end TauCeti
