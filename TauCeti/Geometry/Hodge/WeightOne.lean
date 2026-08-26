/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.Geometry.Hodge.WeilOperator
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.Complex.Conjugation

/-!
# Effective Hodge structures of weight one

An effective pure Hodge structure of weight one has only the two Hodge components
`H^{1,0}` and `H^{0,1}`. Its Weil operator acts on them by `i` and `-i`, respectively, and
therefore descends to an almost complex structure on the real form fixed by conjugation.

This file constructs that real almost complex structure. It then proves that its scalar extension
to `ℂ` is the Weil operator under the canonical equivalence from the complexification of the real
form, and identifies the resulting `i`- and `-i`-eigenspaces with `H^{1,0}` and `H^{0,1}`.
Effectivity is needed only for the weight-one eigenspace identifications: the Weil operator gives an
almost complex structure on the real form in every odd weight. In weight one without effectivity,
its two eigenspaces aggregate all Hodge components according to their first index modulo two.

The real form and its structure map are the generic constructions `TauCeti.realPoints` and
`TauCeti.realPointsLift`; `TauCeti.realPointsEquiv` identifies its complexification with the
original complex vector space. The almost-complex structure reuses
`TauCeti.AlmostComplexStructure`, rather than introducing a Hodge-specific copy of that notion.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.realAlmostComplexStructure`: the Weil operator restricted to the
  real form of an odd-weight Hodge structure.
* `TauCeti.Hodge.HodgeStructureOn.realPointsEquiv_baseChange_realAlmostComplexStructure`: after
  scalar extension, that almost complex structure is the Weil operator; the corresponding identity
  of linear maps is
  `TauCeti.Hodge.HodgeStructureOn.realPointsEquiv_comp_baseChange_realAlmostComplexStructure`.
* `TauCeti.Hodge.HodgeStructureOn.eigenspace_weilOperator_I` and
  `TauCeti.Hodge.HodgeStructureOn.eigenspace_weilOperator_neg_I`: for an effective structure, the
  two eigenspaces of the Weil operator are the two Hodge components.
* `TauCeti.Hodge.HodgeStructureOn.eigenspace_baseChange_realAlmostComplexStructure_I` and
  `TauCeti.Hodge.HodgeStructureOn.eigenspace_baseChange_realAlmostComplexStructure_neg_I`: the same
  comparison on the literal complexification of the real form.

This is the effective weight-one instance bridge in Layer L0 of the Hodge structures roadmap. The
construction and conventions follow Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §6,
and Peters--Steenbrink, *Mixed Hodge Structures*, §2.
-/

public section

namespace TauCeti.Hodge

universe u

namespace HodgeStructureOn

variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable {ω : Conjugation W}

/-- The Weil operator of an odd-weight Hodge structure, restricted to the real form fixed by its
conjugation. It squares to `-1`, so it is an almost complex structure on that real vector space. -/
noncomputable def realAlmostComplexStructure {n : ℤ} (hs : HodgeStructureOn W ω n) (hn : Odd n) :
    AlmostComplexStructure (realPoints ω.toEquiv.toLinearMap) where
  toLinearMap :=
    (hs.weilOperator.restrictScalars ℝ).restrict fun x hx ↦ by
      rw [mem_realPoints] at hx ⊢
      calc
        ω.toEquiv ((hs.weilOperator.restrictScalars ℝ) x) =
            ω.toEquiv (hs.weilOperator x) := (rfl)
        _ = hs.weilOperator (ω.toEquiv x) := hs.conj_weilOperator x
        _ = hs.weilOperator x := congrArg hs.weilOperator hx
        _ = (hs.weilOperator.restrictScalars ℝ) x := (rfl)
  square_neg := by
    ext x
    have h := LinearMap.congr_fun (hs.weilOperator_comp_weilOperator_of_odd hn) (x : W)
    simpa only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply,
      LinearMap.restrict_apply, LinearMap.restrictScalars_apply, Submodule.coe_neg] using h

/-- The almost complex structure on the real form acts by the ambient Weil operator. -/
@[simp]
theorem coe_realAlmostComplexStructure_apply {n : ℤ} (hs : HodgeStructureOn W ω n) (hn : Odd n)
    (x : realPoints ω.toEquiv.toLinearMap) :
    (hs.realAlmostComplexStructure hn x : W) = hs.weilOperator x :=
  (rfl)

/-- **The real almost complex structure complexifies to the Weil operator.** Under the canonical
equivalence `ℂ ⊗[ℝ] V_ℝ ≃ₗ[ℂ] W`, extending `J` from the real form sends the same vectors to the
same place as the Weil operator on `W`. -/
@[simp]
theorem realPointsEquiv_baseChange_realAlmostComplexStructure {n : ℤ}
    (hs : HodgeStructureOn W ω n) (hn : Odd n)
    (x : TensorProduct ℝ ℂ (realPoints ω.toEquiv.toLinearMap)) :
    realPointsEquiv ω.involutive
        ((LinearMap.baseChange ℂ (hs.realAlmostComplexStructure hn).toLinearMap) x) =
      hs.weilOperator (realPointsEquiv ω.involutive x) := by
  induction x with
  | zero => simp
  | tmul c x =>
      rw [LinearMap.baseChange_tmul, realPointsEquiv_tmul, realPointsEquiv_tmul,
        coe_realAlmostComplexStructure_apply, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The complexification comparison as an identity of complex-linear maps. -/
theorem realPointsEquiv_comp_baseChange_realAlmostComplexStructure
    {n : ℤ} (hs : HodgeStructureOn W ω n) (hn : Odd n) :
    (realPointsEquiv ω.involutive).toLinearMap ∘ₗ
        LinearMap.baseChange ℂ (hs.realAlmostComplexStructure hn).toLinearMap =
      hs.weilOperator ∘ₗ (realPointsEquiv ω.involutive).toLinearMap :=
  LinearMap.ext (hs.realPointsEquiv_baseChange_realAlmostComplexStructure hn)

/-- If an endomorphism acts by two distinct scalars on a pair of complementary subspaces, its
eigenspace for the first scalar is the first subspace. -/
private theorem eigenspace_eq_of_isCompl {f : W →ₗ[ℂ] W} {A B : Submodule ℂ W} {μ ν : ℂ}
    (hAB : IsCompl A B) (hA : ∀ x ∈ A, f x = μ • x) (hB : ∀ x ∈ B, f x = ν • x)
    (hνμ : ν ≠ μ) : Module.End.eigenspace f μ = A := by
  apply le_antisymm
  · intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx
    have htop : x ∈ A ⊔ B := by rw [hAB.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop
    have hscalar : ν • b = μ • b := by
      apply add_left_cancel (a := μ • a)
      calc
        μ • a + ν • b = f (a + b) := by rw [map_add, hA a ha, hB b hb]
        _ = f x := congrArg f hab
        _ = μ • x := hx
        _ = μ • (a + b) := congrArg (fun y : W ↦ μ • y) hab.symm
        _ = μ • a + μ • b := smul_add μ a b
    have hbzero : (b : W) = 0 := by
      have hsmul : (ν - μ) • (b : W) = 0 := by rw [sub_smul, hscalar, sub_self]
      exact (smul_eq_zero.mp hsmul).resolve_left (sub_ne_zero.mpr hνμ)
    rw [← hab, hbzero, add_zero]
    exact ha
  · intro x hx
    rw [Module.End.mem_eigenspace_iff]
    exact hA x hx

/-- In an effective weight-one Hodge structure, `H^{1,0}` and `H^{0,1}` are complementary. -/
private theorem isCompl_piece_one_piece_zero (hs : HodgeStructureOn W ω 1)
    (heff : hs.IsEffective) : IsCompl (hs.piece 1) (hs.piece 0) := by
  have hFzero : hs.F 0 = ⊤ := heff.F_eq_top_of_nonpos (by norm_num)
  have hconjFzero : hs.conjF 0 = ⊤ := by
    apply top_unique
    intro x _
    rw [hs.mem_conjF_iff, hFzero]
    exact Submodule.mem_top
  have hone : hs.piece 1 = hs.F 1 := by
    rw [hs.piece_def, show (1 : ℤ) - 1 = 0 by omega, hconjFzero, inf_top_eq]
  have hzero : hs.piece 0 = hs.conjF 1 := by
    rw [hs.piece_def, show (1 : ℤ) - 0 = 1 by omega, hFzero, top_inf_eq]
  rw [hone, hzero]
  simpa only [show (1 : ℤ) + 1 - 1 = 1 by omega] using hs.isCompl_F_conjF 1

/-- For an effective weight-one Hodge structure, the `i`-eigenspace of the Weil operator is
exactly the Hodge component `H^{1,0}`. -/
theorem eigenspace_weilOperator_I (hs : HodgeStructureOn W ω 1) (heff : hs.IsEffective) :
    Module.End.eigenspace hs.weilOperator Complex.I = hs.piece 1 := by
  refine eigenspace_eq_of_isCompl (μ := Complex.I) (ν := -Complex.I)
    (hs.isCompl_piece_one_piece_zero heff)
    (fun x hx ↦ hs.weilOperator_apply_of_mem_piece_one hx)
    (fun x hx ↦ by simpa only [neg_smul] using hs.weilOperator_apply_of_mem_piece_zero hx) ?_
  exact neg_ne_self.mpr Complex.I_ne_zero

/-- For an effective weight-one Hodge structure, the `-i`-eigenspace of the Weil operator is
exactly the conjugate Hodge component `H^{0,1}`. -/
theorem eigenspace_weilOperator_neg_I (hs : HodgeStructureOn W ω 1) (heff : hs.IsEffective) :
    Module.End.eigenspace hs.weilOperator (-Complex.I) = hs.piece 0 := by
  refine eigenspace_eq_of_isCompl (μ := -Complex.I) (ν := Complex.I)
    (hs.isCompl_piece_one_piece_zero heff).symm
    (fun x hx ↦ by simpa only [neg_smul] using hs.weilOperator_apply_of_mem_piece_zero hx)
    (fun x hx ↦ hs.weilOperator_apply_of_mem_piece_one hx) ?_
  exact (neg_ne_self.mpr Complex.I_ne_zero).symm

/-- An intertwining linear equivalence identifies the eigenspaces of the two endomorphisms. -/
private theorem eigenspace_eq_comap_of_intertwine {U : Type*} [AddCommGroup U] [Module ℂ U]
    (e : U ≃ₗ[ℂ] W) (f : U →ₗ[ℂ] U) (g : W →ₗ[ℂ] W)
    (h : ∀ x, e (f x) = g (e x)) (μ : ℂ) :
    Module.End.eigenspace f μ = (Module.End.eigenspace g μ).comap e.toLinearMap := by
  ext x
  simp only [Module.End.mem_eigenspace_iff, Submodule.mem_comap]
  constructor
  · intro hx
    calc
      g (e x) = e (f x) := (h x).symm
      _ = e (μ • x) := congrArg e hx
      _ = μ • e x := map_smul e μ x
  · intro hx
    apply e.injective
    calc
      e (f x) = g (e x) := h x
      _ = μ • e x := hx
      _ = e (μ • x) := (map_smul e μ x).symm

/-- On the literal complexification `ℂ ⊗[ℝ] V_ℝ`, the `i`-eigenspace of the scalar extension of
the real almost complex structure corresponds to `H^{1,0}` under `realPointsEquiv`. -/
theorem eigenspace_baseChange_realAlmostComplexStructure_I
    (hs : HodgeStructureOn W ω 1) (heff : hs.IsEffective) :
    Module.End.eigenspace
        (LinearMap.baseChange ℂ (hs.realAlmostComplexStructure (by norm_num)).toLinearMap)
          Complex.I =
      (hs.piece 1).comap (realPointsEquiv ω.involutive).toLinearMap := by
  rw [eigenspace_eq_comap_of_intertwine (realPointsEquiv ω.involutive)
    (LinearMap.baseChange ℂ (hs.realAlmostComplexStructure (by norm_num)).toLinearMap)
    hs.weilOperator (hs.realPointsEquiv_baseChange_realAlmostComplexStructure (by norm_num))
    Complex.I,
    hs.eigenspace_weilOperator_I heff]

/-- On the literal complexification `ℂ ⊗[ℝ] V_ℝ`, the `-i`-eigenspace of the scalar extension of
the real almost complex structure corresponds to `H^{0,1}` under `realPointsEquiv`. -/
theorem eigenspace_baseChange_realAlmostComplexStructure_neg_I
    (hs : HodgeStructureOn W ω 1) (heff : hs.IsEffective) :
    Module.End.eigenspace
        (LinearMap.baseChange ℂ (hs.realAlmostComplexStructure (by norm_num)).toLinearMap)
          (-Complex.I) =
      (hs.piece 0).comap (realPointsEquiv ω.involutive).toLinearMap := by
  rw [eigenspace_eq_comap_of_intertwine (realPointsEquiv ω.involutive)
    (LinearMap.baseChange ℂ (hs.realAlmostComplexStructure (by norm_num)).toLinearMap)
    hs.weilOperator (hs.realPointsEquiv_baseChange_realAlmostComplexStructure (by norm_num))
    (-Complex.I),
    hs.eigenspace_weilOperator_neg_I heff]

end HodgeStructureOn

end TauCeti.Hodge
