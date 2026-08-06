/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import TauCeti.Geometry.Lie.Tangent.LeftInvariantDerivation

/-!
# The Lie equivalence between derivations and the identity tangent space

The manifold Lie bracket computes the commutator of directional derivatives. Consequently, the
canonical linear equivalence between left-invariant derivations and the tangent space at the
identity is an equivalence of Lie algebras. This supplies the bracket-compatible dictionary needed
to transport the tangent adjoint action to Mathlib's roadmap-facing Lie algebra
`LeftInvariantDerivation I G`.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main results

* `mvfderiv_mlieBracket`: a scalar differential sends the manifold bracket to the commutator of
  directional derivatives.
* `tangentToLeftInvariantDerivation_lie`: the invariant derivation construction preserves brackets.
* `leftInvariantDerivationLieEquivGroupLieAlgebra`: the canonical derivation–tangent Lie
  equivalence.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The group adjoint".
-/

public section

noncomputable section

open Bundle Filter Manifold VectorField
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [CompleteSpace E] [LieGroup I ∞ G]

local instance lieGroupMinSmoothnessThree : LieGroup I (minSmoothness ℝ 3) G :=
  LieGroup.of_le (I := I) (G := G) (m := minSmoothness ℝ 3) (n := ∞)
    (by simpa using (inferInstance : ENat.LEInfty (3 : ℕ∞ω)).out)

/-- Applying a scalar function's differential to the manifold Lie bracket of two differentiable
vector fields gives the commutator of their directional derivatives. -/
theorem mvfderiv_mlieBracket {f : G → ℝ} {V W : ∀ x : G, TangentSpace I x} {x : G}
    (hf : CMDiffAt 2 f x)
    (hV : MDiffAt (fun y ↦ (V y : TangentBundle I G)) x)
    (hW : MDiffAt (fun y ↦ (W y : TangentBundle I G)) x)
    (hVf : MDiffAt (fun y ↦ mvfderiv I f y (V y)) x)
    (hWf : MDiffAt (fun y ↦ mvfderiv I f y (W y)) x) :
    mvfderiv I f x (mlieBracket I V W x) =
      mvfderiv I (fun y ↦ mvfderiv I f y (W y)) x (V x) -
        mvfderiv I (fun y ↦ mvfderiv I f y (V y)) x (W x) := by
  rw [← mlieBracketWithin_univ, mlieBracketWithin_apply]
  have hinv :
      (mfderiv% (extChartAt I x) x).inverse =
        mfderiv[Set.range I] (extChartAt I x).symm (extChartAt I x x) := by
    exact ContinuousLinearMap.inverse_eq
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
        (mem_extChartAt_source x))
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
        (mem_extChartAt_source x))
  rw [hinv]
  change (mfderiv% f x) _ = _
  have hf' : MDiffAt f x := hf.mdifferentiableAt (by norm_num)
  have hchain := mfderiv_comp_mfderivWithin_of_eq
    (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, ℝ))
    (f := (extChartAt I x).symm) (g := f) (s := Set.range I)
    hf' (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x))
    (by apply I.uniqueMDiffOn; exact Set.mem_range_self (f := I) _)
    (extChartAt_to_inv x)
  change @Eq (E →L[ℝ] ℝ) _ _ at hchain
  let Z : E := lieBracketWithin ℝ
    (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (Set.range I))
    (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm W (Set.range I))
    ((extChartAt I x).symm ⁻¹' Set.univ ∩ Set.range I) (extChartAt I x x)
  have hchain_apply := congrArg (fun L : E →L[ℝ] ℝ ↦ L Z) hchain
  change _ = (mfderiv% f x) ((mfderiv[Set.range I]
    (extChartAt I x).symm (extChartAt I x x)) Z) at hchain_apply
  change (mfderiv% f x) ((mfderiv[Set.range I]
    (extChartAt I x).symm (extChartAt I x x)) Z) = _
  rw [← hchain_apply]
  simp only [mfderivWithin_eq_fderivWithin]
  have hfcoord : ContDiffWithinAt ℝ 2 (f ∘ (extChartAt I x).symm)
      (Set.range I) (extChartAt I x x) := by
    have hsymm := contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := 2) x
    have hcomp := ContMDiffWithinAt.comp_of_eq
      (show ContMDiffWithinAt I 𝓘(ℝ, ℝ) 2 f Set.univ x from hf)
      hsymm (Set.mapsTo_univ _ _) (extChartAt_to_inv x)
    exact contMDiffWithinAt_iff_contDiffWithinAt.mp hcomp
  have hVcoord : DifferentiableWithinAt ℝ
      (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (Set.range I))
      (Set.range I) (extChartAt I x x) := by
    have hV' : MDiffAt[Set.univ] (fun y ↦ (V y : TangentBundle I G)) x :=
      hV.mdifferentiableWithinAt
    simpa using hV'.differentiableWithinAt_mpullbackWithin_vectorField
  have hWcoord : DifferentiableWithinAt ℝ
      (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm W (Set.range I))
      (Set.range I) (extChartAt I x x) := by
    have hW' : MDiffAt[Set.univ] (fun y ↦ (W y : TangentBundle I G)) x :=
      hW.mdifferentiableWithinAt
    simpa using hW'.differentiableWithinAt_mpullbackWithin_vectorField
  have hdirection (p : G → ℝ) (U : ∀ y : G, TangentSpace I y) {z : E}
      (hz : z ∈ (extChartAt I x).target)
      (hpz : MDiffAt p ((extChartAt I x).symm z)) :
      (fderivWithin ℝ (p ∘ (extChartAt I x).symm) (Set.range I) z)
          (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm U (Set.range I) z) =
        mvfderiv I p ((extChartAt I x).symm z) (U ((extChartAt I x).symm z)) := by
    rw [← mfderivWithin_eq_fderivWithin]
    change (mfderiv[Set.range I] (p ∘ (extChartAt I x).symm) z)
      ((mfderiv[Set.range I] (extChartAt I x).symm z).inverse
        (U ((extChartAt I x).symm z))) =
      (mfderiv% p ((extChartAt I x).symm z)) (U ((extChartAt I x).symm z))
    rw [mfderiv_comp_mfderivWithin
      (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, ℝ))
      (f := (extChartAt I x).symm) (g := p) (s := Set.range I) z hpz
      (mdifferentiableWithinAt_extChartAt_symm hz)
      (show UniqueMDiffAt[Set.range I] z by
        rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
        exact I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range x hz))]
    rw [ContinuousLinearMap.comp_apply]
    exact congrArg (mfderiv% p ((extChartAt I x).symm z))
      ((isInvertible_mfderivWithin_extChartAt_symm hz).self_apply_inverse _)
  have hf_eventually : ∀ᶠ y in 𝓝 x, MDiffAt f y := by
    filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by norm_num)).1 hf]
      with y hy
    exact hy.mdifferentiableAt (by norm_num)
  have hsymm_tendsto : Tendsto (extChartAt I x).symm
      (𝓝[Set.range I] (extChartAt I x x)) (𝓝 x) := by
    simpa only [extChartAt_to_inv] using
      (contMDiffWithinAt_extChartAt_symm_range_self
        (I := I) (n := 2) x).continuousWithinAt.tendsto
  have htarget : ∀ᶠ z in 𝓝[Set.range I] (extChartAt I x x),
      z ∈ (extChartAt I x).target :=
    extChartAt_target_mem_nhdsWithin x
  have hcoord_eventually (U : ∀ y : G, TangentSpace I y) :
      (fun z ↦ (fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I) z)
        (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm U (Set.range I) z)) =ᶠ[
        𝓝[Set.range I] (extChartAt I x x)]
      (fun y ↦ mvfderiv I f y (U y)) ∘ (extChartAt I x).symm := by
    filter_upwards [htarget, hsymm_tendsto hf_eventually] with z hz hfz
    exact hdirection f U hz hfz
  have hf_chart : MDiffAt f ((extChartAt I x).symm (extChartAt I x x)) := by
    simpa only [extChartAt_to_inv] using hf'
  have hcoordW := (hcoord_eventually W).fderivWithin_eq (𝕜 := ℝ)
    (by simpa only [Function.comp_apply, extChartAt_to_inv] using
      hdirection f W (mem_extChartAt_target x) hf_chart)
  have hcoordV := (hcoord_eventually V).fderivWithin_eq (𝕜 := ℝ)
    (by simpa only [Function.comp_apply, extChartAt_to_inv] using
      hdirection f V (mem_extChartAt_target x) hf_chart)
  have houterW := hdirection (fun y ↦ mvfderiv I f y (W y)) V
    (mem_extChartAt_target x) (by simpa only [extChartAt_to_inv] using hWf)
  have houterV := hdirection (fun y ↦ mvfderiv I f y (V y)) W
    (mem_extChartAt_target x) (by simpa only [extChartAt_to_inv] using hVf)
  rw [extChartAt_to_inv] at houterW houterV
  rw [show Z = lieBracketWithin ℝ
    (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (Set.range I))
    (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm W (Set.range I))
    (Set.range I) (extChartAt I x x) by
      simp only [Z, Set.preimage_univ, Set.univ_inter]]
  rw [fderivWithin_apply_lieBracket hfcoord (by norm_num) I.uniqueDiffOn
    (I.range_subset_closure_interior (Set.mem_range_self (f := I) _))
    (Set.mem_range_self (f := I) _) hWcoord hVcoord]
  rw [hcoordW, hcoordV]
  exact congrArg₂ (· - ·) houterW houterV

theorem tangentToLeftInvariantDerivation_lie (v w : GroupLieAlgebra I G) :
    tangentToLeftInvariantDerivation (I := I) (G := G) ⁅v, w⁆ =
      ⁅tangentToLeftInvariantDerivation (I := I) (G := G) v,
        tangentToLeftInvariantDerivation (I := I) (G := G) w⁆ := by
  apply LeftInvariantDerivation.evalAt_one_injective
  ext f
  let F : C^∞⟮I, G; ℝ⟯ := f
  change (tangentToLeftInvariantDerivation (I := I) (G := G) ⁅v, w⁆ F) 1 =
    (⁅tangentToLeftInvariantDerivation (I := I) (G := G) v,
      tangentToLeftInvariantDerivation (I := I) (G := G) w⁆
        F) 1
  rw [LeftInvariantDerivation.commutator_apply]
  simp only [tangentToLeftInvariantDerivation_apply,
    ContMDiffMap.coe_sub, Pi.sub_apply]
  rw [mulInvariantVectorField_one, GroupLieAlgebra.bracket_def]
  have hvfun : (⇑((tangentToLeftInvariantDerivation v) F) : G → ℝ) =
      fun y ↦ mvfderiv I F y (mulInvariantVectorField v y) := by
    funext y
    exact tangentToLeftInvariantDerivation_apply v F y
  have hwfun : (⇑((tangentToLeftInvariantDerivation w) F) : G → ℝ) =
      fun y ↦ mvfderiv I F y (mulInvariantVectorField w y) := by
    funext y
    exact tangentToLeftInvariantDerivation_apply w F y
  have hvapply := congrArg
    (fun L : E →L[ℝ] ℝ ↦ L (mulInvariantVectorField w (1 : G)))
    (mfderiv_congr (I := I) (I' := 𝓘(ℝ, ℝ)) (x := (1 : G)) hvfun)
  have hwapply := congrArg
    (fun L : E →L[ℝ] ℝ ↦ L (mulInvariantVectorField v (1 : G)))
    (mfderiv_congr (I := I) (I' := 𝓘(ℝ, ℝ)) (x := (1 : G)) hwfun)
  have hbridge :=
    mvfderiv_mlieBracket
      (f := (F : G → ℝ))
      (V := mulInvariantVectorField v)
      (W := mulInvariantVectorField w)
      (x := (1 : G))
      (F.contMDiff.contMDiffAt.of_le (show
        ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) from
          WithTop.coe_le_coe.mpr le_top))
      ((contMDiff_mulInvariantVectorField_infty v).mdifferentiable
        (by simp)).mdifferentiableAt
      ((contMDiff_mulInvariantVectorField_infty w).mdifferentiable
        (by simp)).mdifferentiableAt
      ((contMDiff_mvfderiv_mulInvariantVectorField v F).mdifferentiable
        (by simp)).mdifferentiableAt
      ((contMDiff_mvfderiv_mulInvariantVectorField w F).mdifferentiable
        (by simp)).mdifferentiableAt
  exact hbridge.trans (congrArg₂ (· - ·) hwapply.symm hvapply.symm)

/-- The tangent Lie algebra at the identity is canonically Lie-equivalent to the algebra of
left-invariant derivations. -/
private noncomputable def groupLieAlgebraLieEquivLeftInvariantDerivation
    [FiniteDimensional ℝ E] [T2Space G] (h₁ : I.IsInteriorPoint (1 : G)) :
    GroupLieAlgebra I G ≃ₗ⁅ℝ⁆ LeftInvariantDerivation I G where
  toLieHom :=
    { (leftInvariantDerivationEquivGroupLieAlgebra
        (I := I) (G := G) h₁).symm.toLinearMap with
      map_lie' := by
        intro v w
        calc
          _ = tangentToLeftInvariantDerivation ⁅v, w⁆ :=
            leftInvariantDerivationEquivGroupLieAlgebra_symm_apply h₁ ⁅v, w⁆
          _ = ⁅tangentToLeftInvariantDerivation v,
              tangentToLeftInvariantDerivation w⁆ :=
            tangentToLeftInvariantDerivation_lie v w
          _ = _ := congrArg₂ (fun X Y ↦ ⁅X, Y⁆)
            (leftInvariantDerivationEquivGroupLieAlgebra_symm_apply h₁ v).symm
            (leftInvariantDerivationEquivGroupLieAlgebra_symm_apply h₁ w).symm }
  invFun := leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G) h₁
  left_inv := (leftInvariantDerivationEquivGroupLieAlgebra
    (I := I) (G := G) h₁).apply_symm_apply
  right_inv := (leftInvariantDerivationEquivGroupLieAlgebra
    (I := I) (G := G) h₁).symm_apply_apply

/-- Evaluation at the identity identifies left-invariant derivations with the tangent Lie algebra as
Lie algebras. -/
noncomputable def leftInvariantDerivationLieEquivGroupLieAlgebra
    [FiniteDimensional ℝ E] [T2Space G] (h₁ : I.IsInteriorPoint (1 : G)) :
    LeftInvariantDerivation I G ≃ₗ⁅ℝ⁆ GroupLieAlgebra I G :=
  (groupLieAlgebraLieEquivLeftInvariantDerivation (I := I) (G := G) h₁).symm

@[simp]
theorem leftInvariantDerivationLieEquivGroupLieAlgebra_apply
    [FiniteDimensional ℝ E] [T2Space G] (h₁ : I.IsInteriorPoint (1 : G))
    (D : LeftInvariantDerivation I G) :
    leftInvariantDerivationLieEquivGroupLieAlgebra h₁ D =
      leftInvariantDerivationEquivGroupLieAlgebra h₁ D :=
  (rfl)
