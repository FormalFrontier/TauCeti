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
import TauCeti.Geometry.Lie.Tangent.LieEquiv
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The infinitesimal adjoint action

This file identifies the derivative of the tangent-space adjoint action at the identity with
Mathlib's Lie-algebra adjoint map. This is the geometric prerequisite for transporting the result
to the derivation-valued group adjoint representation.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main results

* `TauCeti.Lie.hasDerivAt_tangentAd_mulInvariantExp_smul_apply_zero`: at `t = 0`, the derivative
  of the tangent adjoint action along the exponential line of `X` is the Lie bracket.
* `TauCeti.Lie.mvfderiv_tangentAd_apply_one`: the differential of the tangent adjoint action at the
  identity is the Lie-algebra adjoint action.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
* The two-parameter Clairaut argument adapts
  `TauCeti.Lie.mvfderiv_mulRightInvariantVectorField_mulInvariantVectorField_commute`; its
  mixed-partial step uses `TauCeti.Analysis.Calculus.ParametricFDeriv`, which in turn adapts
  Sébastien Gouëzel's `ContDiffAt.isSymmSndFDerivAt`.
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

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

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
  have hF : ContDiff ℝ 2 F :=
    (contDiff_comp_mulInvariantExp_mul_mulInvariantExp f.contMDiff g X (-X)).of_le
      (by simp)
  have hdiag : HasDerivAt (fun t : ℝ => F (t, t))
      (fderiv ℝ F (0, 0) (1, 1)) 0 := by
    have hemb : HasDerivAt (fun t : ℝ => (t, t)) (1, 1) 0 :=
      (hasDerivAt_id (𝕜 := ℝ) 0).prodMk (hasDerivAt_id (𝕜 := ℝ) 0)
    exact (hF.differentiable (by simp) (0, 0)).hasFDerivAt.comp_hasDerivAt
      (f := fun t : ℝ => (t, t)) 0 hemb
  have ht : fderiv ℝ F (0, 0) (1, 0) =
      mvfderiv I f g (mulRightInvariantVectorField X g) := by
    have h := timeFDeriv_mulInvariantExp_mul_mulInvariantExp f g X (-X) 0
    dsimp only at h
    rw [zero_smul, mulInvariantExp_zero, mul_one] at h
    simpa only [F, timeFDeriv_apply] using h
  have hs : fderiv ℝ F (0, 0) (0, 1) =
      mvfderiv I f g (-mulInvariantVectorField X g) := by
    have hvec : mulInvariantVectorField (-X) g = -mulInvariantVectorField X g := by
      -- Rewrite negation as scalar multiplication to use linearity of the invariant vector field.
      rw [show -X = (-1 : ℝ) • X by simp]
      exact congrFun (mulInvariantVectorField_smul (I := I) (G := G) (-1) X) g |>.trans
        (by simp)
    have h := spatialFDeriv_mulInvariantExp_mul_mulInvariantExp f g X (-X) 0
    dsimp only at h
    rw [zero_smul, mulInvariantExp_zero, one_mul, hvec] at h
    simpa only [F, spatialFDeriv_apply] using h
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

/-- The smooth scalar infinitesimal generator of conjugation by the exponential line of `X`. -/
private noncomputable def ContMDiffMap.conjugationGenerator
    (f : C^∞⟮I, G; ℝ⟯) (X : GroupLieAlgebra I G) : C^∞⟮I, G; ℝ⟯ :=
  rightInvariantDerivative (I := I) X f - tangentToLeftInvariantDerivation X f

omit [FiniteDimensional ℝ E] in
private theorem ContMDiffMap.conjugationGenerator_apply
    (f : C^∞⟮I, G; ℝ⟯) (X : GroupLieAlgebra I G) (g : G) :
    ContMDiffMap.conjugationGenerator (I := I) f X g = mvfderiv I f g
      (mulRightInvariantVectorField X g - mulInvariantVectorField X g) := by
  rw [ContMDiffMap.conjugationGenerator]
  -- Expose the bundled subtraction at `g`; the two public application lemmas then identify its
  -- summands with the corresponding invariant directional derivatives.
  change rightInvariantDerivative X f g - tangentToLeftInvariantDerivation X f g = _
  rw [rightInvariantDerivative_apply, tangentToLeftInvariantDerivation_apply]
  exact (map_sub (mvfderiv I f g) _ _).symm

/-- Differentiating the scalar conjugation generator along a left-invariant direction gives the
Lie bracket. -/
private theorem mvfderiv_conjugationGenerator_eq_bracket
    (f : C^∞⟮I, G; ℝ⟯) (X Y : GroupLieAlgebra I G) :
    mvfderiv I (ContMDiffMap.conjugationGenerator (I := I) f X) 1 Y =
      mvfderiv I f 1 ⁅X, Y⁆ := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let RXf := rightInvariantDerivative (I := I) X f
  let LXf := tangentToLeftInvariantDerivation (I := I) (G := G) X f
  let LYf := tangentToLeftInvariantDerivation (I := I) (G := G) Y f
  let H := ContMDiffMap.conjugationGenerator (I := I) f X
  have hH : (H : G → ℝ) = (RXf : G → ℝ) - (LXf : G → ℝ) :=
    ContMDiffMap.coe_sub _ _
  -- Unfold only the private bundle `H`; its underlying function is the displayed generator.
  change mvfderiv I H 1 Y = _
  rw [hH]
  rw [mvfderiv_sub
    (RXf.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (LXf.contMDiff.mdifferentiable (by simp)).mdifferentiableAt]
  simp only [sub_apply]
  have hcomm :=
    mvfderiv_mulRightInvariantVectorField_mulInvariantVectorField_commute f (1 : G) X Y
  rw [mulRightInvariantVectorField_one, mulInvariantVectorField_one] at hcomm
  rw [← hcomm]
  have hbridge := congrArg
    (fun D : LeftInvariantDerivation I G => D f 1)
    (tangentToLeftInvariantDerivation_lie (I := I) (G := G) X Y)
  simp only [tangentToLeftInvariantDerivation_apply,
    LeftInvariantDerivation.commutator_apply, ContMDiffMap.coe_sub, Pi.sub_apply,
    mulInvariantVectorField_one] at hbridge
  -- Express the evaluated derivation identity through the named smooth-map bundles `LYf` and
  -- `LXf`, whose applications the preceding simplification has exposed.
  change mvfderiv I f 1 ⁅X, Y⁆ =
    mvfderiv I LYf 1 X - mvfderiv I LXf 1 Y at hbridge
  exact hbridge.symm

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
  have hM := (contMDiff_prod_modelWithCornersSelf_iff (I' := I)).mp hMprod
  exact (f.contMDiff.comp hM).contDiff

/-- At `t = 0`, the derivative of `t ↦ tangentAd (mulInvariantExp (t • X)) Y` along the
exponential line of `X` is `⁅X, Y⁆`.

`GroupLieAlgebra I G` reduces definitionally to the model `E`; the `show E from` ascriptions expose
that model to the normed-space derivative API. -/
theorem hasDerivAt_tangentAd_mulInvariantExp_smul_apply_zero
    (X Y : GroupLieAlgebra I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    HasDerivAt
      (fun t : ℝ => show E from tangentAd (I := I)
        (mulInvariantExp (I := I) (G := G) (t • X)) Y)
      (show E from LieAlgebra.ad ℝ (GroupLieAlgebra I G) X Y) 0 := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let γX : ℝ → G := fun t => mulInvariantExp (I := I) (G := G) (t • X)
  let γY : ℝ → G := fun t => mulInvariantExp (I := I) (G := G) (t • Y)
  let A : ℝ → E := fun t => show E from tangentAd (I := I) (γX t) Y
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
  apply hAder.congr_deriv
  let derivTangent : GroupLieAlgebra I G := deriv A 0
  -- Move from the model-space derivative used by `HasDerivAt` to its canonical identity tangent
  -- space so pointed smooth functions can separate the two vectors.
  change derivTangent = bracketTangent
  apply tangentToPointDerivation_injective (I := I) (1 : G)
  ext f
  -- Evaluation of the two point derivations is definitionally `mvfderiv` on the chosen test map.
  change mvfderiv I f 1 derivTangent = mvfderiv I f 1 bracketTangent
  let q : GroupLieAlgebra I G →L[ℝ] ℝ := mvfderiv I f 1
  let F : ℝ × ℝ → ℝ := fun p =>
    f (γX p.1 * γY p.2 *
      mulInvariantExp (I := I) (G := G) (p.1 • (-X)))
  have hF : ContDiff ℝ 2 F :=
    (ContMDiffMap.contDiff_comp_conj_mulInvariantExp_mulInvariantExp f X Y).of_le
      (by simp)
  -- Varying the second parameter conjugates the `Y`-line by `γX t`, so this spatial partial
  -- evaluates the tangent adjoint orbit against the chosen test function.
  have hspace (t : ℝ) : spatialFDeriv F 0 t 1 = q (A t) := by
    have hFdiff : DifferentiableAt ℝ F (t, 0) := hF.differentiable (by norm_num) (t, 0)
    have hpartial := (hasFDerivAt_timeSlice hFdiff).hasDerivAt
    have hfOne := f.contMDiff.mdifferentiable (by simp) (1 : G) |>.hasMFDerivAt
    have hdirection := HasMFDerivAt.hasDerivAt_comp_mulInvariantExp_smul_zero hfOne
      (tangentAd (I := I) (γX t) Y)
    have hcurve : (fun s : ℝ => F (t, s)) =
        fun s => f (mulInvariantExp (I := I) (G := G)
          (s • tangentAd (I := I) (γX t) Y)) := by
      funext s
      -- Scalar negation in the Lie algebra matches inversion of the exponential curve.
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
      -- The exponential-line chain rule returns `mfderiv`; use the public bridge to the
      -- model-space directional derivative used by `q`.
      change mfderiv I 𝓘(ℝ, ℝ) (f : G → ℝ) 1 _ = mvfderiv I (f : G → ℝ) 1 _
      exact (mvfderiv_apply_eq_mfderiv_apply (I := I) (f := (f : G → ℝ)) _ _).symm
    exact hpartial.unique hdirection'
  -- Varying the first parameter is the infinitesimal conjugation generator `R_X - L_X` along
  -- the `Y`-line.
  have htime (s : ℝ) : timeFDeriv F 0 s =
      mvfderiv I f (γY s)
        (mulRightInvariantVectorField X (γY s) - mulInvariantVectorField X (γY s)) := by
    have hpartial : HasDerivAt (fun t => F (t, s)) (timeFDeriv F 0 s) 0 :=
      hasDerivAt_parameterCurve (hF.differentiable (by norm_num) (0, s))
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
  -- Restate the scalar mixed-partial identity through the tangent-space functional `q`.
  change q derivTangent = q bracketTangent
  have hq : HasDerivAt (fun t => q (A t)) (q (deriv A 0)) 0 :=
    q.hasFDerivAt.comp_hasDerivAt (f := A) 0 hAder
  have hleftDeriv : deriv (fun t => q (A t)) 0 = q (deriv A 0) := by
    simpa only [q] using hq.deriv
  let H := ContMDiffMap.conjugationGenerator (I := I) f X
  have hHmf := H.contMDiff.mdifferentiable (by simp) (1 : G) |>.hasMFDerivAt
  have hHcurve := HasMFDerivAt.hasDerivAt_comp_mulInvariantExp_smul_zero hHmf Y
  have hHcurve' : HasDerivAt (fun s => H (γY s)) (mvfderiv I H 1 Y) 0 := by
    apply hHcurve.congr_deriv
    exact (mvfderiv_apply_eq_mfderiv_apply (I := I) (f := (H : G → ℝ)) _ _).symm
  have hrightDeriv : deriv (fun s =>
      mvfderiv I f (γY s)
        (mulRightInvariantVectorField X (γY s) -
          mulInvariantVectorField X (γY s))) 0 = q bracketTangent := by
    -- `H` packages exactly the scalar generator displayed on the left.
    rw [show (fun s => mvfderiv I f (γY s)
        (mulRightInvariantVectorField X (γY s) -
          mulInvariantVectorField X (γY s))) = fun s => H (γY s) by
      funext s
      exact (ContMDiffMap.conjugationGenerator_apply f X (γY s)).symm]
    rw [hHcurve'.deriv]
    -- The left side is the bundled scalar conjugation generator differentiated along `Y`.
    have hbracket := mvfderiv_conjugationGenerator_eq_bracket f X Y
    have hqBracket : q bracketTangent = mvfderiv I f 1 bracketTangent := by
      dsimp only [q]
    rw [hqBracket]
    exact hbracket
  rw [hleftDeriv, hrightDeriv] at hmixed
  exact hmixed

/-- The derivative at `1` of `g ↦ tangentAd g Y`, in the direction `X`, is the Lie-algebra
adjoint `LieAlgebra.ad ℝ _ X Y`.

`GroupLieAlgebra I G` reduces definitionally to the model `E`; the `show E from` ascriptions expose
that model to the manifold derivative API. -/
theorem mvfderiv_tangentAd_apply_one (X Y : GroupLieAlgebra I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    mvfderiv I
        (fun g : G => show E from tangentAd (I := I) g Y) 1 X =
      (show E from LieAlgebra.ad ℝ (GroupLieAlgebra I G) X Y) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let T : G → E := fun g => show E from tangentAd (I := I) g Y
  have hT : ContMDiff I 𝓘(ℝ, E) ∞ T :=
    contMDiff_tangentAd_apply_right (I := I) (G := G) Y
  have hTmf := hT.mdifferentiable (by simp) (1 : G) |>.hasMFDerivAt
  have hchainRaw := HasMFDerivAt.hasDerivAt_comp_mulInvariantExp_smul_zero hTmf X
  have hchain : HasDerivAt
      (fun t : ℝ => T (mulInvariantExp (I := I) (G := G) (t • X)))
      (mvfderiv I T 1 X) 0 := by
    apply hchainRaw.congr_deriv
    exact (mvfderiv_apply_eq_mfderiv_apply (I := I) (f := T) _ _).symm
  have hpath := hasDerivAt_tangentAd_mulInvariantExp_smul_apply_zero
    (I := I) (G := G) X Y
  have hpathModel : HasDerivAt
      (fun t : ℝ => T (mulInvariantExp (I := I) (G := G) (t • X)))
      (show E from LieAlgebra.ad ℝ (GroupLieAlgebra I G) X Y) 0 := by
    -- Unfold only the local path abbreviation `T`; the tangent/model conversion is the explicit
    -- `show E from` boundary already present in the theorem statement.
    change HasDerivAt
      (fun t : ℝ => show E from tangentAd (I := I)
        (mulInvariantExp (I := I) (G := G) (t • X)) Y)
      (show E from LieAlgebra.ad ℝ (GroupLieAlgebra I G) X Y) 0
    exact hpath
  exact hchain.unique hpathModel

end TauCeti.Lie
