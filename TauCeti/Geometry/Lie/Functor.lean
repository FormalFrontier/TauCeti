/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Tangent.LieEquiv
public import TauCeti.Geometry.Lie.Interior
public import TauCeti.Geometry.Lie.Exponential.Basic

/-!
# The Lie functor on smooth homomorphisms

The differential at the identity of a smooth Lie-group homomorphism induces a Lie-algebra
homomorphism between left-invariant derivations. The resulting map preserves identities and
composition and is natural with respect to the Lie-group exponential.

This advances Layer 3 of the Lie-groups roadmap.

## Main results

* `lieMap`: the Lie-algebra homomorphism induced by a smooth group homomorphism.
* `lieMap_id`, `lieMap_comp`: the identity and composition laws.
* `lieMap_lieExp`: naturality with respect to the Lie-group exponential.
-/

public section

noncomputable section

open Function Manifold VectorField
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [LieGroup I ∞ G] [LieGroup I' ∞ G']

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

private noncomputable def smoothMonoidHom (φ : G →* G')
    (hφ : ContMDiff I I' ∞ (φ : G → G')) :
    ContMDiffMonoidMorphism I I' ∞ G G' where
  toMonoidHom := φ
  contMDiff_toFun := hφ

private noncomputable def lieMapTangent
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') :
    GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I' G' :=
  mfderiv I I' φ 1

private theorem mfderiv_monoidHom_mulInvariantVectorField
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (g : G)
    (X : GroupLieAlgebra I G) :
    mfderiv I I' φ g (mulInvariantVectorField X g) =
      mulInvariantVectorField (mfderiv I I' φ 1 X) (φ g) := by
  simp only [mulInvariantVectorField]
  have hfun : (φ : G → G') ∘ (fun y : G ↦ g * y) =
      (fun z : G' ↦ φ g * z) ∘ φ := by
    funext y
    simp
  have h := congrArg (fun L : E →L[ℝ] E' ↦ L X)
    (mfderiv_congr (I := I) (I' := I') (x := (1 : G)) hfun)
  have hleft := mfderiv_comp (I := I) (I' := I) (I'' := I') (x := (1 : G))
    (g := (φ : G → G')) (f := fun y : G ↦ g * y)
    (φ.contMDiff_toFun.mdifferentiable (by simp)).mdifferentiableAt
    (mdifferentiableAt_mul_left (a := g))
  have hright := mfderiv_comp (I := I) (I' := I') (I'' := I') (x := (1 : G))
    (g := fun z : G' ↦ φ g * z) (f := (φ : G → G'))
    (mdifferentiableAt_mul_left (a := φ g))
    (φ.contMDiff_toFun.mdifferentiable (by simp)).mdifferentiableAt
  rw [hleft, hright] at h
  rw [mul_one, map_one] at h
  exact h

private theorem tangent_comp_monoidHom
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (g : G)
    (X : GroupLieAlgebra I G) (f : G' → ℝ) (hf : ContMDiff I' 𝓘(ℝ, ℝ) ∞ f) :
    mvfderiv I' f (φ g) (mulInvariantVectorField (lieMapTangent φ X) (φ g)) =
      mvfderiv I (f ∘ φ) g (mulInvariantVectorField X g) := by
  have hfield := mfderiv_monoidHom_mulInvariantVectorField φ g X
  -- `lieMapTangent` is the identity differential already present in `hfield`; expose that private
  -- abbreviation so the manifold chain rule can rewrite the pushed-forward direction.
  change mfderiv I I' φ g (mulInvariantVectorField X g) =
      mulInvariantVectorField (lieMapTangent φ X) (φ g) at hfield
  rw [← hfield]
  exact (mfderiv_comp_apply g
    (hf.mdifferentiable (by simp)).mdifferentiableAt
    (φ.contMDiff_toFun.mdifferentiable (by simp)).mdifferentiableAt
    (mulInvariantVectorField X g)).symm

private theorem lieMapTangent_map_lie
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G')
    (X Y : GroupLieAlgebra I G) :
    lieMapTangent φ ⁅X, Y⁆ = ⁅lieMapTangent φ X, lieMapTangent φ Y⁆ := by
  let _ : T2Space G' := t2Space_of_lieGroup (I := I') (n := ∞)
  apply tangentToPointDerivation_injective (I := I') (1 : G')
  ext f
  let F : C^∞⟮I', G'; ℝ⟯ := f
  -- The separating point derivations evaluate by `mvfderiv`; expose those applications so the
  -- bracket computation can use the public directional-derivative API.
  change mvfderiv I' F 1 (lieMapTangent φ ⁅X, Y⁆) =
    mvfderiv I' F 1 ⁅lieMapTangent φ X, lieMapTangent φ Y⁆
  rw [GroupLieAlgebra.bracket_def (v := X) (w := Y)]
  rw [GroupLieAlgebra.bracket_def
    (v := lieMapTangent φ X) (w := lieMapTangent φ Y)]
  have hsourceBracket :
      mlieBracket I (mulInvariantVectorField X) (mulInvariantVectorField Y) 1 = ⁅X, Y⁆ :=
    rfl
  rw [hsourceBracket]
  have htarget :
      mlieBracket I' (mulInvariantVectorField (lieMapTangent φ X))
          (mulInvariantVectorField (lieMapTangent φ Y)) 1 =
        mulInvariantVectorField
          (mlieBracket I' (mulInvariantVectorField (lieMapTangent φ X))
            (mulInvariantVectorField (lieMapTangent φ Y)) 1) 1 := by
    rw [mulInvariantVectorField_one]
  rw [htarget]
  have hsource := tangent_comp_monoidHom φ 1 ⁅X, Y⁆ F F.contMDiff
  rw [map_one] at hsource
  simp only [mulInvariantVectorField_one] at hsource
  -- `hsource` still presents the target direction through its invariant field at one; expose its
  -- canonical tangent representative before rewriting by the chain-rule equality.
  change mvfderiv I' F 1 (lieMapTangent φ ⁅X, Y⁆) = _ at hsource
  rw [hsource, ← hsourceBracket, mulInvariantVectorField_one]
  rw [mvfderiv_mlieBracket
    (f := (F : G' → ℝ) ∘ φ)
    (V := mulInvariantVectorField X) (W := mulInvariantVectorField Y) (x := (1 : G))
    ((F.contMDiff.comp φ.contMDiff_toFun).contMDiffAt.of_le
      (by simpa using (inferInstance : ENat.LEInfty (2 : ℕ∞ω)).out))
    (by simp)
    ((contMDiff_mulInvariantVectorField_infty X).mdifferentiable (by simp)).mdifferentiableAt
    ((contMDiff_mulInvariantVectorField_infty Y).mdifferentiable (by simp)).mdifferentiableAt]
  rw [mvfderiv_mlieBracket
    (f := (F : G' → ℝ))
    (V := mulInvariantVectorField (lieMapTangent φ X))
    (W := mulInvariantVectorField (lieMapTangent φ Y)) (x := (1 : G'))
    (F.contMDiff.contMDiffAt.of_le
      (by simpa using (inferInstance : ENat.LEInfty (2 : ℕ∞ω)).out))
    (by simp)
    ((contMDiff_mulInvariantVectorField_infty (lieMapTangent φ X)).mdifferentiable
      (by simp)).mdifferentiableAt
    ((contMDiff_mulInvariantVectorField_infty (lieMapTangent φ Y)).mdifferentiable
      (by simp)).mdifferentiableAt]
  let FY : G' → ℝ := fun y ↦
    mvfderiv I' F y (mulInvariantVectorField (lieMapTangent φ Y) y)
  let FX : G' → ℝ := fun y ↦
    mvfderiv I' F y (mulInvariantVectorField (lieMapTangent φ X) y)
  have hFY : ContMDiff I' 𝓘(ℝ, ℝ) ∞ FY :=
    contMDiff_mvfderiv_mulInvariantVectorField (lieMapTangent φ Y) F
  have hFX : ContMDiff I' 𝓘(ℝ, ℝ) ∞ FX :=
    contMDiff_mvfderiv_mulInvariantVectorField (lieMapTangent φ X) F
  have hYfun : FY ∘ φ = fun y ↦
      mvfderiv I (F ∘ φ) y (mulInvariantVectorField Y y) := by
    funext g
    exact tangent_comp_monoidHom φ g Y F F.contMDiff
  have hXfun : FX ∘ φ = fun y ↦
      mvfderiv I (F ∘ φ) y (mulInvariantVectorField X y) := by
    funext g
    exact tangent_comp_monoidHom φ g X F F.contMDiff
  have houterY := tangent_comp_monoidHom φ 1 X FY hFY
  have houterX := tangent_comp_monoidHom φ 1 Y FX hFX
  rw [map_one, hYfun] at houterY
  rw [map_one, hXfun] at houterX
  exact congrArg₂ (· - ·) houterY.symm houterX.symm

/-- The Lie functor on morphisms: the differential at the identity of a smooth homomorphism. -/
noncomputable def lieMap [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : G →* G') (hφ : ContMDiff I I' ∞ (φ : G → G')) :
    LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G' :=
  let φ' := smoothMonoidHom φ hφ
  let tangentMap : GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra I' G' :=
    { toLinearMap := lieMapTangent φ'
      map_lie' := by
        intro X Y
        exact lieMapTangent_map_lie φ' X Y }
  (leftInvariantDerivationLieEquivGroupLieAlgebra
      (I := I') (G := G') (ContMDiffMul.isInteriorPoint (n := ∞) (by simp) 1)).symm.toLieHom.comp
    (tangentMap.comp
      (leftInvariantDerivationLieEquivGroupLieAlgebra
        (I := I) (G := G) (ContMDiffMul.isInteriorPoint (n := ∞) (by simp) 1)).toLieHom)

/-- Under evaluation at the identity, `lieMap` is the manifold differential of the homomorphism. -/
@[simp]
theorem leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : G →* G') (hφ : ContMDiff I I' ∞ (φ : G → G'))
    (D : LeftInvariantDerivation I G) :
    leftInvariantDerivationLieEquivGroupLieAlgebra
        (ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G'))
        (lieMap φ hφ D) =
      mfderiv I I' φ 1
        (leftInvariantDerivationLieEquivGroupLieAlgebra
          (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)) D) := by
  let hG := ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)
  let hG' := ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G')
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra hG
  let e' := leftInvariantDerivationLieEquivGroupLieAlgebra hG'
  -- Unfold the transported `LieHom` application once to expose the two canonical Lie
  -- equivalences; their inverse law then characterizes `lieMap` without exposing its body publicly.
  change e' (e'.symm (lieMapTangent (smoothMonoidHom φ hφ) (e D))) = _
  rw [e'.apply_symm_apply]
  rfl

/-- The Lie map of the identity homomorphism is the identity Lie-algebra homomorphism. -/
@[simp]
theorem lieMap_id [FiniteDimensional ℝ E] :
    lieMap (MonoidHom.id G) (contMDiff_id : ContMDiff I I ∞ (id : G → G)) = 1 := by
  apply LieHom.ext
  intro D
  let hG := ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra hG
  apply e.injective
  calc
    e (lieMap (MonoidHom.id G) (contMDiff_id : ContMDiff I I ∞ (id : G → G)) D) =
        mfderiv I I (MonoidHom.id G) 1 (e D) :=
      leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap _ _ _
    _ = e D := by simp
    _ = e ((1 : LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I G) D) := by
      rw [LieHom.one_apply]

/-- The Lie map of a composite is the composite of the two Lie maps. -/
theorem lieMap_comp
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Group G'']
    [LieGroup I'' ∞ G''] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [FiniteDimensional ℝ E'']
    (φ : G →* G') (hφ : ContMDiff I I' ∞ (φ : G → G'))
    (ψ : G' →* G'') (hψ : ContMDiff I' I'' ∞ (ψ : G' → G'')) :
    lieMap (ψ.comp φ) (hψ.comp hφ) = (lieMap ψ hψ).comp (lieMap φ hφ) := by
  apply LieHom.ext
  intro D
  let hG := ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)
  let hG' := ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G')
  let hG'' := ContMDiffMul.isInteriorPoint (I := I'') (n := ∞) (by simp) (1 : G'')
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra hG
  let e' := leftInvariantDerivationLieEquivGroupLieAlgebra hG'
  let e'' := leftInvariantDerivationLieEquivGroupLieAlgebra hG''
  apply e''.injective
  have hleft : e'' (lieMap (ψ.comp φ) (hψ.comp hφ) D) =
      mfderiv I I'' (ψ.comp φ) 1 (e D) :=
    leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap _ _ _
  have hφD : e' (lieMap φ hφ D) = mfderiv I I' φ 1 (e D) :=
    leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap _ _ _
  have hψD : e'' (lieMap ψ hψ (lieMap φ hφ D)) =
      mfderiv I' I'' ψ 1 (e' (lieMap φ hφ D)) :=
    leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap _ _ _
  have hchain := mfderiv_comp_apply (I := I) (I' := I') (I'' := I'') (x := (1 : G))
    (g := (ψ : G' → G'')) (f := (φ : G → G'))
    (hψ.mdifferentiable (by simp)).mdifferentiableAt
    (hφ.mdifferentiable (by simp)).mdifferentiableAt (e D)
  have hchain' : mfderiv I I'' (ψ.comp φ) 1 (e D) =
      mfderiv I' I'' ψ 1 (mfderiv I I' φ 1 (e D)) := by
    simpa only [MonoidHom.coe_comp, map_one] using
      hchain.trans (by rw [map_one])
  have hright : mfderiv I' I'' ψ 1 (mfderiv I I' φ 1 (e D)) =
      e'' (lieMap ψ hψ (lieMap φ hφ D)) := by
    rw [← hφD, ← hψD]
  rw [LieHom.comp_apply]
  exact hleft.trans (hchain'.trans hright)

private theorem monoidHom_mulInvariantExp
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : G →* G') (hφ : ContMDiff I I' ∞ (φ : G → G')) (X : GroupLieAlgebra I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    let _ : T2Space G' := t2Space_of_lieGroup (I := I') (n := ∞)
    φ (mulInvariantExp (I := I) (G := G) X) =
      mulInvariantExp (I := I') (G := G')
        (lieMapTangent (smoothMonoidHom φ hφ) X) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let _ : T2Space G' := t2Space_of_lieGroup (I := I') (n := ∞)
  dsimp only
  let φ' := smoothMonoidHom φ hφ
  let Y := lieMapTangent φ' X
  let γ := mulInvariantIntegralCurve (I := I) (G := G) X 1
  have hcurve : IsMIntegralCurve (φ ∘ γ)
      (mulInvariantVectorField (I := I') (G := G') Y) := by
    rw [isMIntegralCurve_iff_isMIntegralCurveOn]
    exact IsMIntegralCurveOn.map_of_mfderiv_eq (I := I) (I' := I')
      (M := G) (M' := G') (f := (φ : G → G'))
      (V := mulInvariantVectorField (I := I) (G := G) X)
      (W := mulInvariantVectorField (I := I') (G := G') Y)
      (γ := γ) (s := Set.univ)
      (fun t _ => hφ.mdifferentiable (by simp) (γ t))
      (fun t _ => mfderiv_monoidHom_mulInvariantVectorField
        (I := I) (I' := I') φ' (γ t) X)
      ((isMIntegralCurve_mulInvariantIntegralCurve
        (I := I) (G := G) X 1).isMIntegralCurveOn Set.univ)
  have hzero : (φ ∘ γ) 0 = (1 : G') := by simp [γ]
  have heq : φ ∘ γ =
      mulInvariantIntegralCurve (I := I') (G := G') Y 1 :=
    eq_mulInvariantIntegralCurve (I := I') (G := G') Y 1 hzero hcurve
  rw [mulInvariantExp_eq_mulInvariantIntegralCurve]
  rw [mulInvariantExp_eq_mulInvariantIntegralCurve]
  exact congrFun heq 1

/-- A smooth group homomorphism intertwines the Lie-group exponentials through its Lie map. -/
theorem lieMap_lieExp [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : G →* G') (hφ : ContMDiff I I' ∞ (φ : G → G'))
    (X : LeftInvariantDerivation I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    let _ : T2Space G' := t2Space_of_lieGroup (I := I') (n := ∞)
    φ (lieExp X) = lieExp (lieMap φ hφ X) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let _ : T2Space G' := t2Space_of_lieGroup (I := I') (n := ∞)
  dsimp only
  rw [lieExp_eq_mulInvariantExp, lieExp_eq_mulInvariantExp]
  rw [monoidHom_mulInvariantExp (I := I) (I' := I') φ hφ]
  congr 1
  rw [← leftInvariantDerivationLieEquivGroupLieAlgebra_apply,
    ← leftInvariantDerivationLieEquivGroupLieAlgebra_apply]
  exact (leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap
    (I := I) (I' := I') φ hφ X).symm
