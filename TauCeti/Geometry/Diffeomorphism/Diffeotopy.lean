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

* `TauCeti.Diffeotopy J M`: a level-preserving smooth diffeomorphism of `[0, 1] × M` fixing the
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
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A **diffeotopy** of `M` is a diffeomorphism of the cylinder `[0, 1] × M` that preserves
the time coordinate and restricts to the identity on the time-zero slice.

The inverse cylinder diffeomorphism automatically preserves time as well, so this packages a
jointly smooth family of self-diffeomorphisms together with its jointly smooth inverse. -/
structure Diffeotopy (J : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] where
  /-- The level-preserving diffeomorphism of the cylinder. -/
  toDiffeomorph :
    (I × M) ≃ₘ^∞⟮(𝓡∂ 1).prod J, (𝓡∂ 1).prod J⟯ (I × M)
  /-- The cylinder diffeomorphism preserves the time coordinate. -/
  fst_toDiffeomorph : ∀ p, (toDiffeomorph p).1 = p.1
  /-- The family starts at the identity. -/
  snd_toDiffeomorph_zero : ∀ x, (toDiffeomorph (0, x)).2 = x

namespace Diffeotopy

variable (Phi : Diffeotopy J M)

/-- A diffeotopy coerces to its time-dependent family `(t, x) ↦ Φₜ(x)`, obtained as the
second component of its cylinder diffeomorphism. -/
instance instFunLike : FunLike (Diffeotopy J M) (I × M) M where
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
theorem ext {Phi Psi : Diffeotopy J M} (h : ∀ p, Phi p = Psi p) : Phi = Psi :=
  DFunLike.ext Phi Psi h

private theorem apply_eq_snd_toDiffeomorph (p : I × M) : Phi p = (Phi.toDiffeomorph p).2 :=
  rfl

/-- A diffeotopy starts at the identity. -/
@[simp]
theorem apply_zero (x : M) : Phi (0, x) = x :=
  Phi.snd_toDiffeomorph_zero x

/-- A diffeotopy's cylinder diffeomorphism is the level-preserving total map of its family. -/
@[simp]
theorem toDiffeomorph_apply (p : I × M) : Phi.toDiffeomorph p = (p.1, Phi p) :=
  Prod.ext (Phi.fst_toDiffeomorph p) rfl

/-- The inverse cylinder diffeomorphism also preserves the time coordinate. -/
@[simp]
theorem fst_toDiffeomorph_symm (p : I × M) : (Phi.toDiffeomorph.symm p).1 = p.1 := by
  calc
    (Phi.toDiffeomorph.symm p).1 =
        (Phi.toDiffeomorph (Phi.toDiffeomorph.symm p)).1 :=
      (Phi.fst_toDiffeomorph (Phi.toDiffeomorph.symm p)).symm
    _ = p.1 := congrArg Prod.fst (Phi.toDiffeomorph.apply_symm_apply p)

/-- The self-diffeomorphism of `M` at time `t`. -/
def slice [IsManifold J ∞ M] (t : I) : Diff J M ∞ where
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
theorem slice_apply [IsManifold J ∞ M] (t : I) (x : M) : Phi.slice t x = Phi (t, x) :=
  by
    rw [slice.eq_def]
    rfl

@[simp]
theorem slice_symm_apply [IsManifold J ∞ M] (t : I) (x : M) :
    (Phi.slice t).symm x = (Phi.toDiffeomorph.symm (t, x)).2 :=
  by
    rw [slice.eq_def]
    rfl

/-- A diffeotopy's time-zero slice is the identity diffeomorphism. -/
@[simp]
theorem slice_zero [IsManifold J ∞ M] : Phi.slice 0 = _root_.Diffeomorph.refl J M ∞ := by
  apply _root_.Diffeomorph.ext
  exact Phi.snd_toDiffeomorph_zero

/-- The final self-diffeomorphism of a diffeotopy. -/
def final [IsManifold J ∞ M] : Diff J M ∞ :=
  Phi.slice 1

@[simp]
theorem final_apply [IsManifold J ∞ M] (x : M) : Phi.final x = Phi (1, x) :=
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
theorem toAmbientIsotopy_final [IsManifold J ∞ M] :
    Phi.toAmbientIsotopy.final = _root_.toContinuousMap Phi.final.toHomeomorph := by
  ext x
  rfl

/-- The constant diffeotopy. -/
def refl [IsManifold J ∞ M] : Diffeotopy J M where
  toDiffeomorph := _root_.Diffeomorph.refl ((𝓡∂ 1).prod J) (I × M) ∞
  fst_toDiffeomorph _ := rfl
  snd_toDiffeomorph_zero _ := rfl

@[simp]
theorem refl_apply [IsManifold J ∞ M] (p : I × M) :
    (refl (J := J) (M := M)) p = p.2 :=
  by
    rw [refl.eq_def]
    rfl

/-- Every time slice of the constant diffeotopy is the identity diffeomorphism. -/
@[simp]
theorem slice_refl [IsManifold J ∞ M] (t : I) :
    (refl (J := J) (M := M)).slice t = _root_.Diffeomorph.refl J M ∞ := by
  apply _root_.Diffeomorph.ext
  intro x
  rw [slice_apply, refl_apply]
  rfl

/-- The final diffeomorphism of the constant diffeotopy is the identity. -/
@[simp]
theorem final_refl [IsManifold J ∞ M] :
    (refl (J := J) (M := M)).final = _root_.Diffeomorph.refl J M ∞ :=
  slice_refl 1

/-- Pointwise composition of diffeotopies.  At time `t`, `Phi.trans Psi` first applies `Phi t`
and then `Psi t`. -/
def trans [IsManifold J ∞ M] (Psi : Diffeotopy J M) : Diffeotopy J M where
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
theorem trans_apply [IsManifold J ∞ M] (Psi : Diffeotopy J M) (p : I × M) :
    (Phi.trans Psi) p = Psi (p.1, Phi p) := by
  rw [trans.eq_def]
  exact congrArg (fun q => (Psi.toDiffeomorph q).2) (Phi.toDiffeomorph_apply p)

/-- Taking a time slice commutes with pointwise composition of diffeotopies. -/
@[simp]
theorem slice_trans [IsManifold J ∞ M] (Psi : Diffeotopy J M) (t : I) :
    (Phi.trans Psi).slice t = (Phi.slice t).trans (Psi.slice t) := by
  apply _root_.Diffeomorph.ext
  intro x
  have hcomp := congrFun (_root_.Diffeomorph.coe_trans (Phi.slice t) (Psi.slice t)) x
  rw [slice_apply, trans_apply, hcomp, Function.comp_apply, slice_apply, slice_apply]

/-- Taking the final diffeomorphism commutes with pointwise composition. -/
@[simp]
theorem final_trans [IsManifold J ∞ M] (Psi : Diffeotopy J M) :
    (Phi.trans Psi).final = Phi.final.trans Psi.final :=
  Phi.slice_trans Psi 1

/-- Pointwise inverse of a diffeotopy. -/
def symm : Diffeotopy J M where
  toDiffeomorph := Phi.toDiffeomorph.symm
  fst_toDiffeomorph := Phi.fst_toDiffeomorph_symm
  snd_toDiffeomorph_zero x := by
    have hzero : Phi.toDiffeomorph (0, x) = (0, x) := by
      exact Prod.ext (Phi.fst_toDiffeomorph (0, x)) (Phi.snd_toDiffeomorph_zero x)
    exact congrArg Prod.snd (hzero ▸ Phi.toDiffeomorph.symm_apply_apply (0, x))

@[simp]
theorem symm_apply (p : I × M) :
    Phi.symm p = (Phi.toDiffeomorph.symm p).2 :=
  by
    rw [symm.eq_def]
    rfl

/-- Composing a diffeotopy with the constant diffeotopy on the right changes nothing. -/
@[simp]
theorem trans_refl [IsManifold J ∞ M] : Phi.trans (refl (J := J) (M := M)) = Phi := by
  apply ext
  intro p
  rw [trans_apply, refl_apply]

/-- Composing the constant diffeotopy with a diffeotopy on the right changes nothing. -/
@[simp]
theorem refl_trans [IsManifold J ∞ M] : (refl (J := J) (M := M)).trans Phi = Phi := by
  apply ext
  intro p
  simp only [trans_apply, refl_apply]

/-- Pointwise composition of diffeotopies is associative. -/
theorem trans_assoc [IsManifold J ∞ M] (Psi Xi : Diffeotopy J M) :
    (Phi.trans Psi).trans Xi = Phi.trans (Psi.trans Xi) := by
  apply ext
  intro p
  simp only [trans_apply]

/-- A diffeotopy followed by its pointwise inverse is the constant diffeotopy. -/
@[simp]
theorem self_trans_symm [IsManifold J ∞ M] : Phi.trans Phi.symm = refl (J := J) (M := M) := by
  apply ext
  intro p
  simp only [trans_apply, symm_apply, refl_apply]
  rw [← Phi.toDiffeomorph_apply, Phi.toDiffeomorph.symm_apply_apply]

/-- A diffeotopy's pointwise inverse followed by the original is the constant diffeotopy. -/
@[simp]
theorem symm_trans_self [IsManifold J ∞ M] : Phi.symm.trans Phi = refl (J := J) (M := M) := by
  apply ext
  intro p
  simp only [trans_apply, symm_apply, refl_apply]
  have hpair : (p.1, (Phi.toDiffeomorph.symm p).2) = Phi.toDiffeomorph.symm p :=
    Prod.ext (Phi.fst_toDiffeomorph_symm p).symm rfl
  rw [hpair]
  exact congrArg Prod.snd (Phi.toDiffeomorph.apply_symm_apply p)

/-- The pointwise inverse of the constant diffeotopy is constant. -/
@[simp]
theorem symm_refl [IsManifold J ∞ M] :
    (refl (J := J) (M := M)).symm = refl (J := J) (M := M) := by
  apply ext
  intro p
  rw [apply_eq_snd_toDiffeomorph, apply_eq_snd_toDiffeomorph]
  exact congrArg
    (fun f : (I × M) ≃ₘ^∞⟮(𝓡∂ 1).prod J, (𝓡∂ 1).prod J⟯ (I × M) => (f p).2)
    _root_.Diffeomorph.symm_refl

/-- Taking pointwise inverses twice returns the original diffeotopy. -/
@[simp]
theorem symm_symm : Phi.symm.symm = Phi := by
  apply ext
  intro p
  rw [apply_eq_snd_toDiffeomorph, apply_eq_snd_toDiffeomorph]
  exact congrArg Prod.snd (Equiv.symm_symm_apply Phi.toDiffeomorph.toEquiv p)

/-- The pointwise inverse of a composite reverses the order of composition. -/
@[simp]
theorem symm_trans' [IsManifold J ∞ M] (Psi : Diffeotopy J M) :
    (Phi.trans Psi).symm = Psi.symm.trans Phi.symm := by
  apply ext
  intro p
  rw [apply_eq_snd_toDiffeomorph, apply_eq_snd_toDiffeomorph]
  exact congrArg (fun f => (f p).2)
    (_root_.Diffeomorph.symm_trans' Phi.toDiffeomorph Psi.toDiffeomorph)

/-- Taking a time slice commutes with pointwise inversion of a diffeotopy. -/
@[simp]
theorem slice_symm [IsManifold J ∞ M] (t : I) :
    Phi.symm.slice t = (Phi.slice t).symm := by
  apply _root_.Diffeomorph.ext
  intro x
  rw [slice_apply, symm_apply, slice_symm_apply]

/-- The final diffeomorphism of the inverse diffeotopy is the inverse final diffeomorphism. -/
@[simp]
theorem final_symm [IsManifold J ∞ M] : Phi.symm.final = Phi.final.symm :=
  Phi.slice_symm 1

/-- Forgetting the constant diffeotopy gives the constant ambient isotopy pointwise. -/
private theorem toAmbientIsotopy_refl_apply [IsManifold J ∞ M] (p : I × M) :
    (refl (J := J) (M := M)).toAmbientIsotopy.toContinuousMap p = p.2 :=
  refl_apply p

/-- Forgetting pointwise composition of diffeotopies preserves composition pointwise. -/
private theorem toAmbientIsotopy_trans_apply [IsManifold J ∞ M] (Psi : Diffeotopy J M) (p : I × M) :
    (Phi.trans Psi).toAmbientIsotopy.toContinuousMap p =
      (Phi.toAmbientIsotopy.trans Psi.toAmbientIsotopy).toContinuousMap p := by
  rw [toAmbientIsotopy_apply, trans_apply, AmbientIsotopy.trans_apply,
    toAmbientIsotopy_apply, toAmbientIsotopy_apply]

/-- Forgetting pointwise inversion of a diffeotopy preserves inversion pointwise. -/
private theorem toAmbientIsotopy_symm_apply (p : I × M) :
    Phi.symm.toAmbientIsotopy.toContinuousMap p =
      Phi.toAmbientIsotopy.symm.toContinuousMap p := by
  rw [toAmbientIsotopy_apply, symm_apply, AmbientIsotopy.symm_apply]
  have htotal : Phi.toAmbientIsotopy.totalHomeomorph = Phi.toDiffeomorph.toHomeomorph := by
    apply Homeomorph.ext
    intro q
    rw [Phi.toAmbientIsotopy.totalHomeomorph_apply]
    exact (Phi.toDiffeomorph_apply q).symm
  rw [htotal]
  rfl

/-- Forgetting the constant diffeotopy gives the constant ambient isotopy. -/
@[simp]
theorem toAmbientIsotopy_refl [IsManifold J ∞ M] :
    (refl (J := J) (M := M)).toAmbientIsotopy = AmbientIsotopy.refl M := by
  rfl

/-- Forgetting pointwise composition of diffeotopies preserves composition. -/
@[simp]
theorem toAmbientIsotopy_trans [IsManifold J ∞ M] (Psi : Diffeotopy J M) :
    (Phi.trans Psi).toAmbientIsotopy = Phi.toAmbientIsotopy.trans Psi.toAmbientIsotopy := by
  rw [toAmbientIsotopy.eq_def, AmbientIsotopy.trans.eq_def, AmbientIsotopy.mk.injEq]
  ext p
  exact Phi.toAmbientIsotopy_trans_apply Psi p

/-- Forgetting pointwise inversion of a diffeotopy preserves inversion. -/
@[simp]
theorem toAmbientIsotopy_symm : Phi.symm.toAmbientIsotopy = Phi.toAmbientIsotopy.symm := by
  rw [toAmbientIsotopy.eq_def, AmbientIsotopy.symm.eq_def, AmbientIsotopy.mk.injEq]
  ext p
  exact Phi.toAmbientIsotopy_symm_apply p

end Diffeotopy

end TauCeti
