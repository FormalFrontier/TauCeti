/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Smooth
public import TauCeti.Geometry.Lie.Adjoint.Exponential
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
import TauCeti.Geometry.Lie.InvariantVectorField.Commutation
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The infinitesimal adjoint action

This file identifies the derivative of the tangent-space adjoint action at the identity with
Mathlib's Lie-algebra adjoint map. This is the geometric prerequisite for transporting the result
to the derivation-valued group adjoint representation.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main results

* `TauCeti.Lie.hasDerivAt_tangentAd_mulInvariantExp_smul_apply`: along an exponential line,
  the derivative of the tangent adjoint action is the Lie bracket.
* `TauCeti.Lie.mvfderiv_tangentAd_apply`: the differential of the tangent adjoint action at the
  identity is the Lie-algebra adjoint action.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
-/

public section

noncomputable section

namespace TauCeti.Lie

open Bundle Manifold
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]

local instance lieGroupMinSmoothnessThreeInfinitesimalAdjoint :
    LieGroup I (minSmoothness ℝ 3) G :=
  LieGroup.of_le (I := I) (G := G) (m := minSmoothness ℝ 3) (n := ∞)
    (by simpa using (inferInstance : ENat.LEInfty (3 : ℕ∞ω)).out)

local instance lieGroupBoundarylessManifoldInfinitesimalAdjoint : BoundarylessManifold I G where
  isInteriorPoint' g :=
    ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) g

/-- A smooth scalar function on a conjugation orbit is smooth in the two exponential
parameters. -/
private theorem ContMDiffMap.contDiff_comp_mulInvariantExp_conjParameters
    (f : C^∞⟮I, G; ℝ⟯) (X : GroupLieAlgebra I G) (g : G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      f (mulInvariantExp (I := I) (G := G) (p.1 • X) * g *
        mulInvariantExp (I := I) (G := G) (p.2 • (-X)))) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  have hX : ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => mulInvariantExp (I := I) (G := G) (t • X)) := by
    exact contMDiff_mulInvariantExp_smul (I := I) (G := G) X
  have hnegX : ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => mulInvariantExp (I := I) (G := G) (t • (-X))) := by
    exact contMDiff_mulInvariantExp_smul (I := I) (G := G) (-X)
  have hMprod : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : ℝ × ℝ =>
        mulInvariantExp (I := I) (G := G) (p.1 • X) * g *
          mulInvariantExp (I := I) (G := G) (p.2 • (-X))) :=
    ((hX.comp contMDiff_fst).mul contMDiff_const).mul (hnegX.comp contMDiff_snd)
  have hM : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ =>
        mulInvariantExp (I := I) (G := G) (p.1 • X) * g *
          mulInvariantExp (I := I) (G := G) (p.2 • (-X))) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hMprod
  exact (f.contMDiff.comp hM).contDiff

/-- The infinitesimal generator of conjugation acts on scalar functions by the difference of
right- and left-invariant differentiation. -/
private theorem ContMDiffMap.hasDerivAt_comp_conj_mulInvariantExp_smul
    (f : C^∞⟮I, G; ℝ⟯) (X : GroupLieAlgebra I G) (g : G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    HasDerivAt
      (fun t : ℝ => f (mulInvariantExp (I := I) (G := G) (t • X) * g *
        mulInvariantExp (I := I) (G := G) (t • (-X))))
      (mvfderiv I f g
        (mulRightInvariantVectorField X g - mulInvariantVectorField X g)) 0 := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let F : ℝ × ℝ → ℝ := fun p =>
    f (mulInvariantExp (I := I) (G := G) (p.1 • X) * g *
      mulInvariantExp (I := I) (G := G) (p.2 • (-X)))
  have hF : ContDiff ℝ ∞ F :=
    ContMDiffMap.contDiff_comp_mulInvariantExp_conjParameters f X g
  have hdiag : HasDerivAt (fun t : ℝ => F (t, t))
      (fderiv ℝ F (0, 0) (1, 1)) 0 := by
    have hemb : HasDerivAt (fun t : ℝ => (t, t)) (1, 1) 0 :=
      (hasDerivAt_id (𝕜 := ℝ) 0).prodMk (hasDerivAt_id (𝕜 := ℝ) 0)
    exact (hF.differentiable (by simp) (0, 0)).hasFDerivAt.comp_hasDerivAt
      (f := fun t : ℝ => (t, t)) 0 hemb
  have hfAt := f.contMDiff.mdifferentiable (by simp) g |>.hasMFDerivAt
  have hright := HasMFDerivAt.hasDerivAt_comp_mulInvariantExp_smul_mul hfAt X
  have hleftNeg := HasMFDerivAt.hasDerivAt_comp_mul_mulInvariantExp_smul hfAt (-X)
  have ht : fderiv ℝ F (0, 0) (1, 0) =
      mvfderiv I f g (mulRightInvariantVectorField X g) := by
    have hemb : HasDerivAt (fun t : ℝ => (t, (0 : ℝ))) (1, 0) 0 :=
      (hasDerivAt_id (𝕜 := ℝ) 0).prodMk (hasDerivAt_const (x := (0 : ℝ)) (0 : ℝ))
    have hpartial :=
      (hF.differentiable (by simp) (0, 0)).hasFDerivAt.comp_hasDerivAt
        (f := fun t : ℝ => (t, (0 : ℝ))) 0 hemb
    have hright' : HasDerivAt (fun t : ℝ => F (t, 0))
        (mvfderiv I f g (mulRightInvariantVectorField X g)) 0 := by
      have hfun : (fun t : ℝ => F (t, 0)) =
          fun t => f (mulInvariantExp (I := I) (G := G) (t • X) * g) := by
        funext t
        simp only [F, zero_smul, mulInvariantExp_zero, mul_one]
      rw [hfun]
      apply hright.congr_deriv
      with_unfolding_all rfl
    exact hpartial.unique hright'
  have hs : fderiv ℝ F (0, 0) (0, 1) =
      mvfderiv I f g (-mulInvariantVectorField X g) := by
    have hemb : HasDerivAt (fun t : ℝ => ((0 : ℝ), t)) (0, 1) 0 :=
      (hasDerivAt_const (x := (0 : ℝ)) (0 : ℝ)).prodMk
        (hasDerivAt_id (𝕜 := ℝ) 0)
    have hpartial :=
      (hF.differentiable (by simp) (0, 0)).hasFDerivAt.comp_hasDerivAt
        (f := fun t : ℝ => ((0 : ℝ), t)) 0 hemb
    have hleftNeg' : HasDerivAt (fun t : ℝ => F (0, t))
        (mvfderiv I f g (-mulInvariantVectorField X g)) 0 := by
      have hfun : (fun t : ℝ => F (0, t)) =
          fun t => f (g * mulInvariantExp (I := I) (G := G) (t • (-X))) := by
        funext t
        simp only [F, zero_smul, mulInvariantExp_zero, one_mul]
      have hvec : mulInvariantVectorField (-X) g = -mulInvariantVectorField X g := by
        simp [mulInvariantVectorField]
        rfl
      rw [hfun]
      rw [hvec] at hleftNeg
      apply hleftNeg.congr_deriv
      with_unfolding_all rfl
    exact hpartial.unique hleftNeg'
  have hder : fderiv ℝ F (0, 0) (1, 1) =
      mvfderiv I f g
        (mulRightInvariantVectorField X g - mulInvariantVectorField X g) := by
    have hsplit : fderiv ℝ F (0, 0) (1, 1) =
        fderiv ℝ F (0, 0) (1, 0) + fderiv ℝ F (0, 0) (0, 1) := by
      calc
        fderiv ℝ F (0, 0) (1, 1) =
            fderiv ℝ F (0, 0) ((1, 0) + (0, 1)) :=
          congrArg (fderiv ℝ F (0, 0)) (by norm_num)
        _ = _ := map_add _ _ _
    rw [hsplit, ht, hs]
    rw [sub_eq_add_neg, map_add, map_neg]
  simpa only [F] using hdiag.congr_deriv hder

/-- Differentiating the scalar conjugation generator along a left-invariant direction gives the
Lie bracket. -/
private theorem mvfderiv_conjugationGenerator_eq_bracket
    (f : C^∞⟮I, G; ℝ⟯) (X Y : GroupLieAlgebra I G) :
    mvfderiv I
        (fun g => mvfderiv I f g
          (mulRightInvariantVectorField X g - mulInvariantVectorField X g)) 1 Y =
      mvfderiv I f 1 ⁅X, Y⁆ := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let RXf : C^∞⟮I, G; ℝ⟯ :=
    ⟨fun g => mvfderiv I f g (mulRightInvariantVectorField X g),
      contMDiff_mvfderiv_mulRightInvariantVectorField X f⟩
  let LXf : C^∞⟮I, G; ℝ⟯ :=
    ⟨fun g => mvfderiv I f g (mulInvariantVectorField X g),
      contMDiff_mvfderiv_mulInvariantVectorField X f⟩
  let LYf : C^∞⟮I, G; ℝ⟯ :=
    ⟨fun g => mvfderiv I f g (mulInvariantVectorField Y g),
      contMDiff_mvfderiv_mulInvariantVectorField Y f⟩
  have hgenerator :
      (fun g => mvfderiv I f g
        (mulRightInvariantVectorField X g - mulInvariantVectorField X g)) =
        (RXf : G → ℝ) - (LXf : G → ℝ) := by
    funext g
    change mvfderiv I f g (_ - _) = _ - _
    rw [map_sub]
    rfl
  rw [hgenerator]
  rw [mvfderiv_sub
    (RXf.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (LXf.contMDiff.mdifferentiable (by simp)).mdifferentiableAt]
  simp only [sub_apply]
  have hcomm :=
    mvfderiv_mulRightInvariantVectorField_mulInvariantVectorField_commute f (1 : G) X Y
  rw [mulRightInvariantVectorField_one, mulInvariantVectorField_one] at hcomm
  change mvfderiv I LYf 1 X = mvfderiv I RXf 1 Y at hcomm
  rw [← hcomm]
  have hbridge := mvfderiv_mlieBracket
    (f := (f : G → ℝ))
    (V := mulInvariantVectorField X)
    (W := mulInvariantVectorField Y)
    (x := (1 : G))
    (f.contMDiff.contMDiffAt.of_le (show
      ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) from
        WithTop.coe_le_coe.mpr le_top))
    (by simp)
    ((contMDiff_mulInvariantVectorField_infty X).mdifferentiable
      (by simp)).mdifferentiableAt
    ((contMDiff_mulInvariantVectorField_infty Y).mdifferentiable
      (by simp)).mdifferentiableAt
  rw [mulInvariantVectorField_one, mulInvariantVectorField_one] at hbridge
  change mvfderiv I f 1
      (VectorField.mlieBracket I (mulInvariantVectorField X) (mulInvariantVectorField Y) 1) =
    mvfderiv I LYf 1 X - mvfderiv I LXf 1 Y at hbridge
  rw [← hbridge]
  congr 1

/-- A smooth scalar function evaluated on a conjugated exponential line is jointly smooth in the
conjugating and conjugated parameters. -/
private theorem ContMDiffMap.contDiff_comp_conj_mulInvariantExp_mulInvariantExp
    (f : C^∞⟮I, G; ℝ⟯) (X Y : GroupLieAlgebra I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      f (mulInvariantExp (I := I) (G := G) (p.1 • X) *
        mulInvariantExp (I := I) (G := G) (p.2 • Y) *
        mulInvariantExp (I := I) (G := G) (p.1 • (-X)))) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  have hX : ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => mulInvariantExp (I := I) (G := G) (t • X)) := by
    exact contMDiff_mulInvariantExp_smul (I := I) (G := G) X
  have hY : ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => mulInvariantExp (I := I) (G := G) (t • Y)) := by
    exact contMDiff_mulInvariantExp_smul (I := I) (G := G) Y
  have hnegX : ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => mulInvariantExp (I := I) (G := G) (t • (-X))) := by
    exact contMDiff_mulInvariantExp_smul (I := I) (G := G) (-X)
  have hMprod : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : ℝ × ℝ =>
        mulInvariantExp (I := I) (G := G) (p.1 • X) *
          mulInvariantExp (I := I) (G := G) (p.2 • Y) *
          mulInvariantExp (I := I) (G := G) (p.1 • (-X))) :=
    ((hX.comp contMDiff_fst).mul (hY.comp contMDiff_snd)).mul
      (hnegX.comp contMDiff_fst)
  have hM : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ =>
        mulInvariantExp (I := I) (G := G) (p.1 • X) *
          mulInvariantExp (I := I) (G := G) (p.2 • Y) *
          mulInvariantExp (I := I) (G := G) (p.1 • (-X))) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hMprod
  exact (f.contMDiff.comp hM).contDiff

/-- Along an exponential line, the derivative of the tangent adjoint action is the Lie bracket. -/
theorem hasDerivAt_tangentAd_mulInvariantExp_smul_apply
    (X Y : GroupLieAlgebra I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    HasDerivAt
      (fun t : ℝ => @id E (tangentAd (I := I)
        (mulInvariantExp (I := I) (G := G) (t • X)) Y))
      (@id E (LieAlgebra.ad ℝ (GroupLieAlgebra I G) X Y)) 0 := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let γX : ℝ → G := fun t => mulInvariantExp (I := I) (G := G) (t • X)
  let γY : ℝ → G := fun t => mulInvariantExp (I := I) (G := G) (t • Y)
  let A : ℝ → E := fun t => @id E (tangentAd (I := I) (γX t) Y)
  have hγX : ContMDiff 𝓘(ℝ, ℝ) I ∞ γX := by
    simpa only [γX] using contMDiff_mulInvariantExp_smul (I := I) (G := G) X
  have hA : ContDiff ℝ ∞ A := by
    have hpair : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
        (fun t => (γX t, @id E Y)) := hγX.prodMk contMDiff_const
    exact (contMDiff_tangentAd_apply (I := I) (G := G)).comp hpair |>.contDiff
  have hAder : HasDerivAt A (deriv A 0) 0 :=
    (hA.differentiable (by simp) 0).hasDerivAt
  let bracketTangent : GroupLieAlgebra I G :=
    LieAlgebra.ad ℝ (GroupLieAlgebra I G) X Y
  let bracketModel : E := @id E bracketTangent
  apply hAder.congr_deriv
  -- Tangent vectors at the identity are determined by their action on pointed smooth functions.
  with_unfolding_all apply tangentToPointDerivation_injective (I := I) (1 : G)
  ext f
  let q : E →L[ℝ] ℝ := by
    with_unfolding_all exact mvfderiv I f 1
  let F : ℝ × ℝ → ℝ := fun p =>
    f (γX p.1 * γY p.2 *
      mulInvariantExp (I := I) (G := G) (p.1 • (-X)))
  have hF : ContDiff ℝ 2 F :=
    (ContMDiffMap.contDiff_comp_conj_mulInvariantExp_mulInvariantExp f X Y).of_le
      (show ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) from
        WithTop.coe_le_coe.mpr le_top)
  -- Varying the second parameter conjugates the `Y`-line by `γX t`, so this spatial partial
  -- evaluates the tangent adjoint orbit against the chosen test function.
  have hspace (t : ℝ) : spatialFDeriv F 0 t 1 = q (A t) := by
    have hemb : HasDerivAt (fun s : ℝ => (t, s)) (0, 1) 0 :=
      (hasDerivAt_const (x := 0) t).prodMk (hasDerivAt_id (𝕜 := ℝ) 0)
    have hpartialRaw := (hF.differentiable (by norm_num) (t, 0)).hasFDerivAt
      |>.comp_hasDerivAt (f := fun s : ℝ => (t, s)) 0 hemb
    have hpartial : HasDerivAt (fun s => F (t, s)) (spatialFDeriv F 0 t 1) 0 := by
      simpa only [Function.comp_def, spatialFDeriv_apply, zero_smul, one_smul] using hpartialRaw
    have hfOne := f.contMDiff.mdifferentiable (by simp) (1 : G) |>.hasMFDerivAt
    have hdirection := HasMFDerivAt.hasDerivAt_comp_mulInvariantExp_smul hfOne
      (tangentAd (I := I) (γX t) Y)
    have hcurve : (fun s : ℝ => F (t, s)) =
        fun s => f (mulInvariantExp (I := I) (G := G)
          (s • tangentAd (I := I) (γX t) Y)) := by
      funext s
      have hinv : mulInvariantExp (I := I) (G := G) (t • (-X)) = (γX t)⁻¹ := by
        rw [show t • (-X) = -(t • X) by module, mulInvariantExp_neg]
      simp only [F]
      rw [hinv, conj_mulInvariantExp]
      -- Expose the tangent-space representative so linearity of `tangentAd` can move the scalar.
      change f (mulInvariantExp (I := I) (G := G)
        (tangentAd (I := I) (γX t) (s • Y))) = _
      rw [map_smul]
    rw [hcurve] at hpartial
    have hdirection' : HasDerivAt
        (fun s : ℝ => f (mulInvariantExp (I := I) (G := G)
          (s • tangentAd (I := I) (γX t) Y))) (q (A t)) 0 := by
      apply hdirection.congr_deriv
      with_unfolding_all rfl
    exact hpartial.unique hdirection'
  -- Varying the first parameter is the infinitesimal conjugation generator `R_X - L_X` along
  -- the `Y`-line.
  have htime (s : ℝ) : timeFDeriv F 0 s =
      mvfderiv I f (γY s)
        (mulRightInvariantVectorField X (γY s) - mulInvariantVectorField X (γY s)) := by
    have hemb : HasDerivAt (fun t : ℝ => (t, s)) (1, 0) 0 :=
      (hasDerivAt_id (𝕜 := ℝ) 0).prodMk (hasDerivAt_const (x := 0) s)
    have hpartialRaw := (hF.differentiable (by norm_num) (0, s)).hasFDerivAt
      |>.comp_hasDerivAt (f := fun t : ℝ => (t, s)) 0 hemb
    have hpartial : HasDerivAt (fun t => F (t, s)) (timeFDeriv F 0 s) 0 := by
      simpa only [Function.comp_def, timeFDeriv_apply, zero_smul, one_smul] using hpartialRaw
    have hdirection := ContMDiffMap.hasDerivAt_comp_conj_mulInvariantExp_smul f X (γY s)
    have hdirection' : HasDerivAt (fun t => F (t, s))
        (mvfderiv I f (γY s)
          (mulRightInvariantVectorField X (γY s) -
            mulInvariantVectorField X (γY s))) 0 := by
      -- Only the abbreviation `F` and the association of the three group factors differ.
      convert hdirection using 1
      all_goals rfl
    exact hpartial.unique hdirection'
  have hFmin : ContDiffAt ℝ (minSmoothness ℝ 2) F (0, 0) := by
    simpa using hF.contDiffAt
  -- Clairaut symmetry identifies the derivative of the adjoint orbit with the derivative of its
  -- scalar conjugation generator along `Y`.
  have hmixed := deriv_spatialFDeriv_apply (F := F) (x := (0 : ℝ)) (w := (1 : ℝ))
    hFmin
  have hspaceFun : (fun t => spatialFDeriv F 0 t 1) =
      fun t => q (A t) := by
    funext t
    exact hspace t
  have htimeFun : timeFDeriv F 0 = fun s =>
      mvfderiv I f (γY s)
        (mulRightInvariantVectorField X (γY s) -
          mulInvariantVectorField X (γY s)) := by
    funext s
    exact htime s
  rw [hspaceFun, htimeFun, fderiv_apply_one_eq_deriv] at hmixed
  -- Unfold the canonical model-space and point-derivation identifications on both sides.
  with_unfolding_all change q (deriv A 0) = q bracketModel
  have hq : HasDerivAt (fun t => q (A t)) (q (deriv A 0)) 0 :=
    q.hasFDerivAt.comp_hasDerivAt (f := A) 0 hAder
  have hleftDeriv : deriv (fun t => q (A t)) 0 = q (deriv A 0) := by
    simpa only [q] using hq.deriv
  let RXf : C^∞⟮I, G; ℝ⟯ :=
    ⟨fun g => mvfderiv I f g (mulRightInvariantVectorField X g),
      contMDiff_mvfderiv_mulRightInvariantVectorField X f⟩
  let LXf : C^∞⟮I, G; ℝ⟯ :=
    ⟨fun g => mvfderiv I f g (mulInvariantVectorField X g),
      contMDiff_mvfderiv_mulInvariantVectorField X f⟩
  have hgeneratorSmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun g => mvfderiv I f g
        (mulRightInvariantVectorField X g - mulInvariantVectorField X g)) := by
    have hsub := RXf.contMDiff.sub LXf.contMDiff
    apply hsub.congr
    intro g
    change mvfderiv I f g (_ - _) = _ - _
    rw [map_sub]
    rfl
  let H : C^∞⟮I, G; ℝ⟯ :=
    ⟨fun g => mvfderiv I f g
      (mulRightInvariantVectorField X g - mulInvariantVectorField X g), hgeneratorSmooth⟩
  have hHmf := H.contMDiff.mdifferentiable (by simp) (1 : G) |>.hasMFDerivAt
  have hHcurve := HasMFDerivAt.hasDerivAt_comp_mulInvariantExp_smul hHmf Y
  -- The exponential-line chain rule is expressed through the same canonical `mvfderiv` map.
  with_unfolding_all change HasDerivAt (fun s => H (γY s)) (mvfderiv I H 1 Y) 0 at hHcurve
  have hrightDeriv : deriv (fun s =>
      mvfderiv I f (γY s)
        (mulRightInvariantVectorField X (γY s) -
          mulInvariantVectorField X (γY s))) 0 = q bracketModel := by
    rw [show (fun s => mvfderiv I f (γY s)
        (mulRightInvariantVectorField X (γY s) -
          mulInvariantVectorField X (γY s))) = fun s => H (γY s) by rfl]
    rw [hHcurve.deriv]
    change mvfderiv I
        (fun g => mvfderiv I f g
          (mulRightInvariantVectorField X g - mulInvariantVectorField X g)) 1 Y = _
    -- The left side is now exactly the scalar conjugation generator differentiated along `Y`.
    have hbracket := mvfderiv_conjugationGenerator_eq_bracket f X Y
    have hqBracket : q bracketModel = mvfderiv I f 1 bracketTangent := by
      with_unfolding_all rfl
    rw [hqBracket]
    exact hbracket
  rw [hleftDeriv, hrightDeriv] at hmixed
  exact hmixed

/-- The differential at the identity of the tangent adjoint action, evaluated on `X` and `Y`, is
the Lie-algebra adjoint `ad X Y`. -/
theorem mvfderiv_tangentAd_apply (X Y : GroupLieAlgebra I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    mvfderiv I
        (fun g : G => @id E (tangentAd (I := I) g Y)) 1 X =
      @id E (LieAlgebra.ad ℝ (GroupLieAlgebra I G) X Y) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let T : G → E := fun g => @id E (tangentAd (I := I) g Y)
  have hT : ContMDiff I 𝓘(ℝ, E) ∞ T := by
    have hpair : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun g : G => (g, @id E Y)) := contMDiff_id.prodMk contMDiff_const
    exact (contMDiff_tangentAd_apply (I := I) (G := G)).comp hpair
  have hTmf := hT.mdifferentiable (by simp) (1 : G) |>.hasMFDerivAt
  have hchainRaw := HasMFDerivAt.hasDerivAt_comp_mulInvariantExp_smul hTmf X
  have hchain : HasDerivAt
      (fun t : ℝ => T (mulInvariantExp (I := I) (G := G) (t • X)))
      (mvfderiv I T 1 X) 0 := by
    apply hchainRaw.congr_deriv
    with_unfolding_all rfl
  have hpath := hasDerivAt_tangentAd_mulInvariantExp_smul_apply (I := I) (G := G) X Y
  have hpathModel : HasDerivAt
      (fun t : ℝ => T (mulInvariantExp (I := I) (G := G) (t • X)))
      (@id E (LieAlgebra.ad ℝ (GroupLieAlgebra I G) X Y)) 0 := by
    with_unfolding_all simpa only [T] using hpath
  exact hchain.unique hpathModel

end TauCeti.Lie
