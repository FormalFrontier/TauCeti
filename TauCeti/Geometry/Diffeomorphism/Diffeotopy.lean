/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Topology.Homotopy.Isotopy.Basic

/-!
# Diffeotopies

A diffeotopy of a smooth manifold `M` is a smooth one-parameter family of self-diffeomorphisms
starting at the identity.  The smoothness required here is joint smoothness of the family and its
inverse: equivalently, the level-preserving map `[0, 1] × M → [0, 1] × M` is a
diffeomorphism.  Encoding the family by that diffeomorphism makes pointwise composition and
inversion immediate and avoids imposing compactness on `M`.

This is the smooth specialization of `TauCeti.AmbientIsotopy` requested by the geometric-topology
roadmap's general isotopy convention.  It is also the family notion used by the roadmap's
diffeomorphism-group layer: every diffeotopy forgets to a continuous ambient isotopy and each time
slice is a self-diffeomorphism.

The definition follows M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8,
where an isotopy is a smooth map whose time slices are embeddings and an ambient isotopy has
diffeomorphic time slices.  Requiring the inverse family to be jointly smooth is the standard
parametrized form appropriate for diffeotopies.

## Main definitions

* `TauCeti.Diffeotopy I n M`: a level-preserving diffeomorphism of `[0, 1] × M` fixing the
  time-zero slice.
* `TauCeti.Diffeotopy.slice`: the self-diffeomorphism at a given time.
* `TauCeti.Diffeotopy.final`: the time-one self-diffeomorphism.
* `TauCeti.Diffeotopy.toAmbientIsotopy`: forget smoothness to obtain a continuous ambient isotopy.
* `TauCeti.Diffeotopy.refl`, `trans`, and `symm`: the identity, pointwise composition, and
  pointwise inverse of diffeotopies.
-/

public section

noncomputable section

namespace TauCeti

open Set unitInterval
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- A **diffeotopy** of `M` is a diffeomorphism of the cylinder `[0, 1] × M` that preserves
the time coordinate and restricts to the identity on the time-zero slice.

The inverse cylinder diffeomorphism automatically preserves time as well, so this packages a
jointly smooth family of self-diffeomorphisms together with its jointly smooth inverse. -/
structure Diffeotopy (J : ModelWithCorners ℝ E H) (n : ℕ∞ω) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] where
  /-- The level-preserving diffeomorphism of the cylinder. -/
  toDiffeomorph :
    (I × M) ≃ₘ^n⟮(𝓡∂ 1).prod J, (𝓡∂ 1).prod J⟯ (I × M)
  /-- The cylinder diffeomorphism preserves the time coordinate. -/
  fst_toDiffeomorph : ∀ p, (toDiffeomorph p).1 = p.1
  /-- The family starts at the identity. -/
  snd_toDiffeomorph_zero : ∀ x, (toDiffeomorph (0, x)).2 = x

namespace Diffeotopy

variable (Phi : Diffeotopy J n M)

instance instFunLike : FunLike (Diffeotopy J n M) (I × M) M where
  coe Phi p := (Phi.toDiffeomorph p).2
  coe_injective Phi Psi h := by
    cases Phi with
    | mk Phi hPhi0 hPhi1 =>
      cases Psi with
      | mk Psi hPsi0 hPsi1 =>
        congr
        apply _root_.Diffeomorph.ext
        intro p
        exact Prod.ext (hPhi0 p |>.trans (hPsi0 p).symm) (congr_fun h p)

/-- Two diffeotopies are equal when their underlying smooth families agree pointwise. -/
@[ext]
theorem ext {Phi Psi : Diffeotopy J n M} (h : ∀ p, Phi p = Psi p) : Phi = Psi :=
  DFunLike.ext Phi Psi h

@[simp]
theorem apply_eq_snd_toDiffeomorph (p : I × M) : Phi p = (Phi.toDiffeomorph p).2 :=
  rfl

/-- A diffeotopy's cylinder diffeomorphism is the level-preserving total map of its family. -/
theorem toDiffeomorph_apply (p : I × M) : Phi.toDiffeomorph p = (p.1, Phi p) :=
  Prod.ext (Phi.fst_toDiffeomorph p) rfl

/-- The inverse cylinder diffeomorphism also preserves the time coordinate. -/
theorem fst_toDiffeomorph_symm (p : I × M) : (Phi.toDiffeomorph.symm p).1 = p.1 := by
  calc
    (Phi.toDiffeomorph.symm p).1 =
        (Phi.toDiffeomorph (Phi.toDiffeomorph.symm p)).1 :=
      (Phi.fst_toDiffeomorph (Phi.toDiffeomorph.symm p)).symm
    _ = p.1 := congrArg Prod.fst (Phi.toDiffeomorph.apply_symm_apply p)

/-- The self-diffeomorphism of `M` at time `t`. -/
def slice [IsManifold J n M] (t : I) : Diff J M n where
  toFun x := Phi (t, x)
  invFun x := (Phi.toDiffeomorph.symm (t, x)).2
  left_inv x := by
    have htotal : (t, Phi (t, x)) = Phi.toDiffeomorph (t, x) :=
      (Phi.toDiffeomorph_apply (t, x)).symm
    exact congrArg Prod.snd (htotal ▸ Phi.toDiffeomorph.symm_apply_apply (t, x))
  right_inv x := by
    have htotal : (t, (Phi.toDiffeomorph.symm (t, x)).2) =
        Phi.toDiffeomorph.symm (t, x) :=
      Prod.ext (Phi.fst_toDiffeomorph_symm (t, x)).symm rfl
    exact congrArg Prod.snd (htotal ▸ Phi.toDiffeomorph.apply_symm_apply (t, x))
  contMDiff_toFun :=
    contMDiff_snd.comp
      (Phi.toDiffeomorph.contMDiff.comp (contMDiff_const.prodMk contMDiff_id))
  contMDiff_invFun :=
    contMDiff_snd.comp
      (Phi.toDiffeomorph.symm.contMDiff.comp (contMDiff_const.prodMk contMDiff_id))

@[simp]
theorem slice_apply [IsManifold J n M] (t : I) (x : M) : Phi.slice t x = Phi (t, x) :=
  by
    rw [slice.eq_def]
    rfl

@[simp]
theorem slice_symm_apply [IsManifold J n M] (t : I) (x : M) :
    (Phi.slice t).symm x = (Phi.toDiffeomorph.symm (t, x)).2 :=
  by
    rw [slice.eq_def]
    rfl

/-- A diffeotopy's time-zero slice is the identity diffeomorphism. -/
@[simp]
theorem slice_zero [IsManifold J n M] : Phi.slice 0 = _root_.Diffeomorph.refl J M n := by
  apply _root_.Diffeomorph.ext
  exact Phi.snd_toDiffeomorph_zero

/-- The final self-diffeomorphism of a diffeotopy. -/
def final [IsManifold J n M] : Diff J M n :=
  Phi.slice 1

@[simp]
theorem final_apply [IsManifold J n M] (x : M) : Phi.final x = Phi (1, x) :=
  by
    rw [final.eq_def, slice_apply]

/-- Forgetting smoothness turns a diffeotopy into a continuous ambient isotopy. -/
def toAmbientIsotopy : AmbientIsotopy M where
  toFun := Phi
  continuous_toFun := Phi.toDiffeomorph.contMDiff.snd.continuous
  isHomeomorph_total' := by
    convert Phi.toDiffeomorph.toHomeomorph.isHomeomorph using 1
    exact (funext Phi.toDiffeomorph_apply).symm
  map_zero_left' := Phi.snd_toDiffeomorph_zero

@[simp]
theorem toAmbientIsotopy_apply (p : I × M) :
    Phi.toAmbientIsotopy.toContinuousMap p = Phi p :=
  by
    rw [toAmbientIsotopy.eq_def]
    rfl

@[simp]
theorem toAmbientIsotopy_final [IsManifold J n M] :
    Phi.toAmbientIsotopy.final = _root_.toContinuousMap Phi.final.toHomeomorph := by
  ext x
  rfl

/-- The constant diffeotopy. -/
def refl [IsManifold J n M] : Diffeotopy J n M where
  toDiffeomorph := _root_.Diffeomorph.refl ((𝓡∂ 1).prod J) (I × M) n
  fst_toDiffeomorph _ := rfl
  snd_toDiffeomorph_zero _ := rfl

@[simp]
theorem refl_apply [IsManifold J n M] (p : I × M) :
    ((refl (J := J) (n := n) (M := M)).toDiffeomorph p).2 = p.2 :=
  by
    rw [refl.eq_def]
    rfl

/-- Pointwise composition of diffeotopies.  At time `t`, `Phi.trans Psi` first applies `Phi t`
and then `Psi t`. -/
def trans [IsManifold J n M] (Psi : Diffeotopy J n M) : Diffeotopy J n M where
  toDiffeomorph := Phi.toDiffeomorph.trans Psi.toDiffeomorph
  fst_toDiffeomorph p := by
    exact (Psi.fst_toDiffeomorph (Phi.toDiffeomorph p)).trans
      (Phi.fst_toDiffeomorph p)
  snd_toDiffeomorph_zero x := by
    have hPhi : Phi.toDiffeomorph (0, x) = (0, x) :=
      Prod.ext (Phi.fst_toDiffeomorph (0, x)) (Phi.snd_toDiffeomorph_zero x)
    -- `Diffeomorph.trans` computes by function composition, which exposes the intermediate point.
    change (Psi.toDiffeomorph (Phi.toDiffeomorph (0, x))).2 = x
    rw [hPhi]
    exact Psi.snd_toDiffeomorph_zero x

@[simp]
theorem trans_apply [IsManifold J n M] (Psi : Diffeotopy J n M) (p : I × M) :
    ((Phi.trans Psi).toDiffeomorph p).2 = Psi (p.1, Phi p) := by
  rw [trans.eq_def]
  exact congrArg (fun q => (Psi.toDiffeomorph q).2) (Phi.toDiffeomorph_apply p)

/-- Taking a time slice commutes with pointwise composition of diffeotopies. -/
@[simp]
theorem slice_trans [IsManifold J n M] (Psi : Diffeotopy J n M) (t : I) :
    (Phi.trans Psi).slice t = (Phi.slice t).trans (Psi.slice t) := by
  apply _root_.Diffeomorph.ext
  intro x
  have hcomp := congrFun (_root_.Diffeomorph.coe_trans (Phi.slice t) (Psi.slice t)) x
  rw [slice_apply, apply_eq_snd_toDiffeomorph, trans_apply, hcomp, Function.comp_apply,
    slice_apply, slice_apply]

/-- Taking the final diffeomorphism commutes with pointwise composition. -/
@[simp]
theorem final_trans [IsManifold J n M] (Psi : Diffeotopy J n M) :
    (Phi.trans Psi).final = Phi.final.trans Psi.final :=
  Phi.slice_trans Psi 1

/-- Pointwise inverse of a diffeotopy. -/
def symm [IsManifold J n M] : Diffeotopy J n M where
  toDiffeomorph := Phi.toDiffeomorph.symm
  fst_toDiffeomorph := Phi.fst_toDiffeomorph_symm
  snd_toDiffeomorph_zero x := by
    have hzero : Phi.toDiffeomorph (0, x) = (0, x) := by
      exact Prod.ext (Phi.fst_toDiffeomorph (0, x)) (Phi.snd_toDiffeomorph_zero x)
    exact congrArg Prod.snd (hzero ▸ Phi.toDiffeomorph.symm_apply_apply (0, x))

@[simp]
theorem symm_apply [IsManifold J n M] (p : I × M) :
    (Phi.symm.toDiffeomorph p).2 = (Phi.toDiffeomorph.symm p).2 :=
  by
    rw [symm.eq_def]

/-- Taking a time slice commutes with pointwise inversion of a diffeotopy. -/
@[simp]
theorem slice_symm [IsManifold J n M] (t : I) :
    Phi.symm.slice t = (Phi.slice t).symm := by
  apply _root_.Diffeomorph.ext
  intro x
  rw [slice_apply, apply_eq_snd_toDiffeomorph, symm_apply, slice_symm_apply]

/-- The final diffeomorphism of the inverse diffeotopy is the inverse final diffeomorphism. -/
@[simp]
theorem final_symm [IsManifold J n M] : Phi.symm.final = Phi.final.symm :=
  Phi.slice_symm 1

theorem toAmbientIsotopy_refl_apply [IsManifold J n M] (p : I × M) :
    (refl (J := J) (n := n) (M := M)).toAmbientIsotopy.toContinuousMap p = p.2 :=
  refl_apply p

theorem toAmbientIsotopy_trans_apply [IsManifold J n M] (Psi : Diffeotopy J n M) (p : I × M) :
    (Phi.trans Psi).toAmbientIsotopy.toContinuousMap p =
      (Phi.toAmbientIsotopy.trans Psi.toAmbientIsotopy).toContinuousMap p := by
  rw [toAmbientIsotopy_apply, apply_eq_snd_toDiffeomorph, trans_apply,
    AmbientIsotopy.trans_apply,
    toAmbientIsotopy_apply, toAmbientIsotopy_apply]

theorem toAmbientIsotopy_symm_apply [IsManifold J n M] (p : I × M) :
    Phi.symm.toAmbientIsotopy.toContinuousMap p =
      Phi.toAmbientIsotopy.symm.toContinuousMap p := by
  rw [toAmbientIsotopy_apply, apply_eq_snd_toDiffeomorph, symm_apply,
    AmbientIsotopy.symm_apply]
  have htotal : Phi.toAmbientIsotopy.totalHomeomorph = Phi.toDiffeomorph.toHomeomorph := by
    apply Homeomorph.ext
    intro q
    rw [Phi.toAmbientIsotopy.totalHomeomorph_apply]
    exact (Phi.toDiffeomorph_apply q).symm
  rw [htotal]
  rfl

end Diffeotopy

end TauCeti
