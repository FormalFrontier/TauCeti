/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Degree

/-!
# Pushforward of scheme-theoretic Weil divisors

This file defines the pushforward of a finite scheme-theoretic Weil divisor along a
quasicompact morphism. It is the codimension-one, finite-support restriction of Mathlib's
`AlgebraicCycle.map`: a point contributes its residue degree when its image still has
codimension one, and contributes zero otherwise.

The construction supplies the geometric pushforward anticipated by the abstract
`WeilDivisor.pushforward` API. Unlike that unweighted pushforward of formal point sums, this
one uses the residue-field factor required for algebraic cycles. The comparison theorem
`toAlgebraicCycle_pushforward` characterizes the construction without exposing its
finite-support packaging.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, “Divisors on a curve:
Weil divisors `⊕_x ℤ`” and “Degree”, by connecting scheme-theoretic Weil divisors to the
residue-degree-weighted cycle pushforward. The convention and construction reuse Mathlib's
`AlgebraicCycle.map`, following the Stacks Project, Tag 02R3.
-/

public section

open CategoryTheory AlgebraicGeometry Order

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X Y Z : Scheme.{u}}

noncomputable section

/-- Mathlib's algebraic-cycle pushforward of a finite codimension-one cycle again has finite
support contained in codimension one. -/
private def mapFiniteCodimensionOneCycle (f : X ⟶ Y) [QuasiCompact f]
    (D : SchemeWeilDivisor X) : finiteCodimensionOneCycles Y := by
  let w : X → ℤ :=
    fun x ↦
      (AlgebraicCycle.mapCoeff f (fun x : X ↦ coheight x)
        (fun y : Y ↦ coheight y) x : ℤ)
  let C : AlgebraicCycle Y ℤ :=
    AlgebraicCycle.map f (fun x : X ↦ coheight x) (fun y : Y ↦ coheight y)
      (toAlgebraicCycle D)
  refine ⟨C, mem_finiteCodimensionOneCycles_iff.mpr ⟨?_, ?_⟩⟩
  · refine ((finite_support_toAlgebraicCycle D).image f).subset ?_
    simpa only [C, AlgebraicCycle.map] using
      Function.locallyFinsupp.support_map_subset_of_forall_mem f.isSpectralMap w
        (toAlgebraicCycle D) (toAlgebraicCycle D).support
        (f '' (toAlgebraicCycle D).support) (fun _ hx ↦ hx)
        (fun x hx _ ↦ ⟨x, hx, rfl⟩)
  · intro y hy
    have hsub :
        C.support ⊆ {y : Y | coheight y = 1} := by
      simpa only [C, AlgebraicCycle.map] using
        Function.locallyFinsupp.support_map_subset_of_forall_mem f.isSpectralMap w
          (toAlgebraicCycle D) (toAlgebraicCycle D).support
          {y : Y | coheight y = 1} (fun _ hx ↦ hx) (by
            intro x hx hw
            have hx₁ := coheight_eq_one_of_mem_support_toAlgebraicCycle D hx
            have hxy : coheight x = coheight (f x) := by
              by_contra hne
              exact hw (by simp [w, AlgebraicCycle.mapCoeff, hne])
            exact hxy.symm.trans hx₁)
    exact hsub hy

private lemma mapFiniteCodimensionOneCycle_zero (f : X ⟶ Y) [QuasiCompact f] :
    mapFiniteCodimensionOneCycle f (0 : SchemeWeilDivisor X) = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  simp [mapFiniteCodimensionOneCycle, AlgebraicCycle.map]

private lemma mapFiniteCodimensionOneCycle_add (f : X ⟶ Y) [QuasiCompact f]
    (D E : SchemeWeilDivisor X) :
    mapFiniteCodimensionOneCycle f (D + E) =
      mapFiniteCodimensionOneCycle f D + mapFiniteCodimensionOneCycle f E := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  -- Unwrap the finite-cycle subtype; its coercion has no additive simp lemma.
  change
    AlgebraicCycle.map f (fun x : X ↦ coheight x) (fun y : Y ↦ coheight y)
        (toAlgebraicCycle (D + E)) y =
      (AlgebraicCycle.map f (fun x : X ↦ coheight x) (fun y : Y ↦ coheight y)
          (toAlgebraicCycle D) +
        AlgebraicCycle.map f (fun x : X ↦ coheight x) (fun y : Y ↦ coheight y)
          (toAlgebraicCycle E)) y
  rw [(toAlgebraicCycle : SchemeWeilDivisor X →+ AlgebraicCycle X ℤ).map_add]
  simp only [AlgebraicCycle.map, Function.locallyFinsupp.map_apply,
    Function.locallyFinsuppWithin.coe_add, Pi.add_apply, add_mul]
  apply finsum_mem_add_distrib'
  · refine (finite_support_toAlgebraicCycle D).subset ?_
    rintro x ⟨_, hx⟩
    exact fun hzero ↦ hx (by simp [hzero])
  · refine (finite_support_toAlgebraicCycle E).subset ?_
    rintro x ⟨_, hx⟩
    exact fun hzero ↦ hx (by simp [hzero])

/-- Push forward a scheme-theoretic Weil divisor along a quasicompact morphism.

This is the finite codimension-one part of `AlgebraicCycle.map f coheight coheight`: points
whose image does not have codimension one receive weight zero, while the remaining points are
weighted by their residue degree. -/
def pushforward (f : X ⟶ Y) [QuasiCompact f] :
    SchemeWeilDivisor X →+ SchemeWeilDivisor Y :=
  (equivFiniteCodimensionOneCycles (X := Y)).symm.toAddMonoidHom.comp
    { toFun := mapFiniteCodimensionOneCycle f
      map_zero' := mapFiniteCodimensionOneCycle_zero f
      map_add' := mapFiniteCodimensionOneCycle_add f }

/-- Viewing the pushforward as an algebraic cycle recovers Mathlib's algebraic-cycle
pushforward. This is the characteristic equation for `SchemeWeilDivisor.pushforward`. -/
lemma toAlgebraicCycle_pushforward (f : X ⟶ Y) [QuasiCompact f]
    (D : SchemeWeilDivisor X) :
    toAlgebraicCycle (pushforward f D) =
      AlgebraicCycle.map f (fun x : X ↦ coheight x) (fun y : Y ↦ coheight y)
        (toAlgebraicCycle D) := by
  rw [← coe_equivFiniteCodimensionOneCycles_apply]
  simp only [pushforward, AddMonoidHom.comp_apply]
  -- Expose the additive-equivalence round trip hidden by `toAddMonoidHom`.
  change
    ((equivFiniteCodimensionOneCycles (X := Y)
      ((equivFiniteCodimensionOneCycles (X := Y)).symm
        (mapFiniteCodimensionOneCycle f D)) : finiteCodimensionOneCycles Y) :
        AlgebraicCycle Y ℤ) =
      AlgebraicCycle.map f (fun x : X ↦ coheight x) (fun y : Y ↦ coheight y)
        (toAlgebraicCycle D)
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- The coefficient of the pushed-forward divisor at a codimension-one point is the
corresponding coefficient of Mathlib's algebraic-cycle pushforward. -/
lemma pushforward_apply (f : X ⟶ Y) [QuasiCompact f] (D : SchemeWeilDivisor X)
    (y : CodimensionOnePoint Y) :
    pushforward f D y =
      AlgebraicCycle.map f (fun x : X ↦ coheight x) (fun y : Y ↦ coheight y)
        (toAlgebraicCycle D) y := by
  rw [← toAlgebraicCycle_apply (pushforward f D) y, toAlgebraicCycle_pushforward]

private lemma toAlgebraicCycle_ofPoint_apply_of_eq (x : CodimensionOnePoint X) {z : X}
    (hz : z = x) : toAlgebraicCycle (WeilDivisor.ofPoint x) z = 1 := by
  subst z
  exact (toAlgebraicCycle_apply (WeilDivisor.ofPoint x) x).trans
    (WeilDivisor.coeff_ofPoint_self x)

private lemma toAlgebraicCycle_ofPoint_apply_of_ne (x : CodimensionOnePoint X) {z : X}
    (hz : z ≠ x) : toAlgebraicCycle (WeilDivisor.ofPoint x) z = 0 := by
  by_cases hz₁ : coheight z = 1
  · let z' : CodimensionOnePoint X := ⟨z, hz₁⟩
    have hzx : z' ≠ x := fun h ↦ hz (congrArg Subtype.val h)
    exact (toAlgebraicCycle_apply (WeilDivisor.ofPoint x) z').trans
      (WeilDivisor.coeff_ofPoint_of_ne hzx)
  · exact toAlgebraicCycle_apply_of_coheight_ne_one _ _ hz₁

/-- A codimension-one point pushes forward to its residue degree times its image when that
image has codimension one, and to zero otherwise. -/
@[simp]
lemma pushforward_ofPoint (f : X ⟶ Y) [QuasiCompact f] (x : CodimensionOnePoint X) :
    pushforward f (WeilDivisor.ofPoint x) =
      if h : coheight (f x) = 1 then
        (f.residueDegree x : ℤ) • WeilDivisor.ofPoint (⟨f x, h⟩ : CodimensionOnePoint Y)
      else 0 := by
  classical
  split_ifs with hfx
  · apply toAlgebraicCycle_injective
    rw [(toAlgebraicCycle : SchemeWeilDivisor Y →+ AlgebraicCycle Y ℤ).map_zsmul]
    apply Function.locallyFinsuppWithin.ext
    intro y
    rw [toAlgebraicCycle_pushforward]
    simp only [AlgebraicCycle.map, Function.locallyFinsupp.map_apply]
    rw [finsum_eq_single _ (x : X)]
    · by_cases hy : f x = y
      · subst y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, toAlgebraicCycle_apply,
          finsum_true, natCast_zsmul, Function.locallyFinsuppWithin.coe_nsmul,
          Pi.smul_apply, Int.nsmul_eq_mul]
        have hxcoeff : (WeilDivisor.ofPoint x) x = 1 :=
          WeilDivisor.coeff_ofPoint_self x
        rw [hxcoeff, one_mul]
        have himage :
            toAlgebraicCycle
                (WeilDivisor.ofPoint (⟨f x, hfx⟩ : CodimensionOnePoint Y)) (f x) = 1 :=
          toAlgebraicCycle_ofPoint_apply_of_eq _ rfl
        rw [himage, mul_one]
        simp [AlgebraicCycle.mapCoeff, x.property, hfx]
      · have hzero :
            toAlgebraicCycle (WeilDivisor.ofPoint (⟨f x, hfx⟩ : CodimensionOnePoint Y)) y = 0 :=
          toAlgebraicCycle_ofPoint_apply_of_ne _ (Ne.symm hy)
        -- Evaluate the pointwise scalar action on a locally supported function.
        change _ =
          (f.residueDegree x : ℤ) •
            toAlgebraicCycle
              (WeilDivisor.ofPoint (⟨f x, hfx⟩ : CodimensionOnePoint Y)) y
        rw [hzero, smul_zero]
        simp [hy]
    · intro z hz
      simp [toAlgebraicCycle_ofPoint_apply_of_ne x hz]
  · apply toAlgebraicCycle_injective
    apply Function.locallyFinsuppWithin.ext
    intro y
    rw [toAlgebraicCycle_pushforward]
    simp only [AlgebraicCycle.map, Function.locallyFinsupp.map_apply]
    rw [finsum_eq_single _ (x : X)]
    · have hfx' : 1 ≠ coheight (f x) := fun h ↦ hfx h.symm
      simp [AlgebraicCycle.mapCoeff, x.property, hfx']
    · intro z hz
      simp [toAlgebraicCycle_ofPoint_apply_of_ne x hz]

/-- Pushforward is functorial when the intermediate and composite images of each
codimension-one point still have codimension one.

The hypotheses exclude the dimension-drop obstruction built into `AlgebraicCycle.mapCoeff`.
Residue-degree multiplicities compose by the tower law `residueDegree_comp`. -/
lemma pushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    (hf : ∀ x : CodimensionOnePoint X, coheight (f x) = 1)
    (hgf : ∀ x : CodimensionOnePoint X, coheight (g (f x)) = 1) :
    pushforward (f ≫ g) = (pushforward g).comp (pushforward f) := by
  apply Finsupp.addHom_ext
  intro x n
  rw [WeilDivisor.single_eq_zsmul_ofPoint, map_zsmul, map_zsmul]
  have hfg : coheight ((f ≫ g) x) = 1 := by simpa using hgf x
  simp only [AddMonoidHom.comp_apply]
  rw [pushforward_ofPoint, dif_pos hfg, pushforward_ofPoint, dif_pos (hf x), map_zsmul,
    pushforward_ofPoint, dif_pos (hgf x)]
  simp only [residueDegree_comp, Nat.cast_mul, smul_smul]
  congr 1
  · ac_rfl

/-- Relative degree commutes with pushforward when the first morphism preserves
codimension-one points. This is the scheme-theoretic formula
`deg_g(f_* D) = deg_{g ∘ f}(D)`. -/
lemma relativeDegree_pushforward (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f]
    (hf : ∀ x : CodimensionOnePoint X, coheight (f x) = 1)
    (D : SchemeWeilDivisor X) :
    relativeDegree g (pushforward f D) = relativeDegree (f ≫ g) D := by
  suffices (relativeDegree g).comp (pushforward f) = relativeDegree (f ≫ g) by
    exact DFunLike.congr_fun this D
  apply Finsupp.addHom_ext
  intro x n
  rw [WeilDivisor.single_eq_zsmul_ofPoint, map_zsmul, map_zsmul]
  simp only [AddMonoidHom.comp_apply]
  rw [pushforward_ofPoint, dif_pos (hf x),
    map_zsmul, relativeDegree_ofPoint, relativeDegree_ofPoint, residueDegree_comp, Nat.cast_mul,
    smul_eq_mul]
  ac_rfl

/-- Pushforward along the identity morphism is the identity on scheme-theoretic Weil
divisors. -/
@[simp]
lemma pushforward_id :
    pushforward (𝟙 X) = AddMonoidHom.id (SchemeWeilDivisor X) := by
  apply AddMonoidHom.ext
  intro D
  apply toAlgebraicCycle_injective
  rw [toAlgebraicCycle_pushforward]
  exact AlgebraicCycle.map_id (fun x : X ↦ coheight x) (toAlgebraicCycle D)

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
