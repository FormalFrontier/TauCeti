/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Decomposition
public import TauCeti.Geometry.Hodge.Morphism
public import TauCeti.Geometry.Hodge.Tate

/-!
# The Weil operator of a pure Hodge structure

The Weil operator `C` of a pure Hodge structure of weight `n` is the complex-linear automorphism
acting on the Hodge component `H^{p,q}` by the scalar `i^{p-q}`. Since `q = n - p` on the
component `piece p`, that scalar is `i^{2p-n}`, and the Hodge decomposition
`TauCeti.Hodge.HodgeStructureOn.isInternal_piece` extends it to the whole ambient space.

Two identities make `C` the carrier of the Hermitian theory. It squares to the weight sign,
`C ∘ C = (-1)^n`, so `C` is an automorphism, and is a complex structure in odd weight.
And it commutes with the conjugation, so it is defined over the real form: this is what allows a
symmetric bilinear form `Q` to be turned into the Hermitian form `h(u, v) = Q(C u, conj v)` on all
of the ambient space, rather than only on homogeneous vectors where `i^{p-q}` makes sense.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.weilOperator`: the Weil operator `C`.
* `TauCeti.Hodge.HodgeStructureOn.weilOperator_apply_of_mem`: `C` acts on `H^{p,n-p}` by
  `i^{2p-n}`.
* `TauCeti.Hodge.HodgeStructureOn.weilOperator_unique`: that action characterizes `C`.
* `TauCeti.Hodge.HodgeStructureOn.weilOperator_piece`, `…_F`, `…_conjF`: `C` preserves the Hodge
  components and both filtrations.
* `TauCeti.Hodge.HodgeStructureOn.weilOperator_comp_weilOperator`: `C ∘ C = (-1)^n`.
* `TauCeti.Hodge.HodgeStructureOn.weilOperatorEquiv`: `C` bundled as a linear automorphism.
* `TauCeti.Hodge.HodgeStructureOn.conj_weilOperator`: `C` commutes with the conjugation.
* `TauCeti.Hodge.IsPolarization.isOrthogonal_weilOperator`: `C` is an isometry of a complexified
  polarizing form.
* `TauCeti.Hodge.HodgeStructure.Hom.commutes_weilOperator`: morphisms commute with `C`.
* `TauCeti.Hodge.tate_weilOperator`: the Weil operator of `ℤ(m)` is the identity.

This supplies the Weil operator targeted in Layer L1 of
`TauCetiRoadmap/HodgeStructures/README.md`. The sign conventions are those of Voisin, *Hodge
Theory and Complex Algebraic Geometry I*, §7.1.2, and Peters–Steenbrink, *Mixed Hodge
Structures*, §2.
-/

public section

namespace TauCeti.Hodge

universe u v

namespace HodgeStructureOn

variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable {ω : Conjugation W} {n : ℤ}

/-- The square of a power of `i` is the corresponding power of `-1`. -/
private theorem I_zpow_mul_self (k : ℤ) :
    Complex.I ^ k * Complex.I ^ k = (-1 : ℂ) ^ k := by
  rw [← zpow_add₀ Complex.I_ne_zero, ← two_mul, zpow_mul]
  norm_num

/-- An even shift does not change a power of `-1`. -/
private theorem negOne_zpow_two_mul_sub (p k : ℤ) :
    (-1 : ℂ) ^ (2 * p - k) = (-1 : ℂ) ^ k := by
  have hne : (-1 : ℂ) ≠ 0 := by norm_num
  have hkey : ∀ m : ℤ, (-1 : ℂ) ^ (2 * m) = 1 := fun m ↦ by
    rw [zpow_mul]
    norm_num
  have hp : 2 * p - k + k = 2 * p := by ring
  have hk : k + k = 2 * k := by ring
  refine mul_right_cancel₀ (b := (-1 : ℂ) ^ k) (zpow_ne_zero _ hne) ?_
  rw [← zpow_add₀ hne, ← zpow_add₀ hne, hp, hk, hkey, hkey]

/-- **The Weil operator** of a pure Hodge structure of weight `n`: the complex-linear map acting
on the Hodge component `H^{p,q}` by `i^{p-q} = i^{2p-n}`. -/
noncomputable def weilOperator (hs : HodgeStructureOn W ω n) : W →ₗ[ℂ] W :=
  (DirectSum.toModule ℂ ℤ W fun p ↦ Complex.I ^ (2 * p - n) • (hs.piece p).subtype) ∘ₗ
    hs.decomposition.toLinearMap

/-- The Weil operator acts on the Hodge component `H^{p,n-p}` by the scalar `i^{2p-n}`. -/
theorem weilOperator_apply_of_mem (hs : HodgeStructureOn W ω n) {p : ℤ} {x : W}
    (hx : x ∈ hs.piece p) : hs.weilOperator x = Complex.I ^ (2 * p - n) • x := by
  rw [weilOperator, LinearMap.comp_apply, LinearEquiv.coe_coe,
    hs.decomposition_apply_of_mem hx, DirectSum.toModule_lof]
  rfl

/-- The Weil operator is the only complex-linear map acting on each Hodge component `H^{p,n-p}`
by `i^{2p-n}`. -/
theorem weilOperator_unique (hs : HodgeStructureOn W ω n) (f : W →ₗ[ℂ] W)
    (hf : ∀ p : ℤ, ∀ x ∈ hs.piece p, f x = Complex.I ^ (2 * p - n) • x) :
    f = hs.weilOperator :=
  hs.linearMap_ext_of_piece fun p x hx ↦ by
    rw [hf p x hx, hs.weilOperator_apply_of_mem hx]

/-- The Weil operator preserves every Hodge component. -/
theorem weilOperator_mem_piece (hs : HodgeStructureOn W ω n) {p : ℤ} {x : W}
    (hx : x ∈ hs.piece p) : hs.weilOperator x ∈ hs.piece p := by
  rw [hs.weilOperator_apply_of_mem hx]
  exact Submodule.smul_mem _ _ hx

/-- The Weil operator restricts to an automorphism of every Hodge component. -/
@[simp]
theorem weilOperator_piece (hs : HodgeStructureOn W ω n) (p : ℤ) :
    (hs.piece p).map hs.weilOperator = hs.piece p := by
  refine le_antisymm ?_ fun y hy ↦ ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact hs.weilOperator_mem_piece hy
  · refine ⟨(Complex.I ^ (2 * p - n))⁻¹ • y, Submodule.smul_mem _ _ hy, ?_⟩
    rw [hs.weilOperator_apply_of_mem (Submodule.smul_mem _ _ hy), smul_smul,
      mul_inv_cancel₀ (zpow_ne_zero _ Complex.I_ne_zero), one_smul]

/-- The Weil operator preserves every step of the Hodge filtration. -/
@[simp]
theorem weilOperator_F (hs : HodgeStructureOn W ω n) (p : ℤ) :
    (hs.F p).map hs.weilOperator = hs.F p := by
  rw [hs.F_eq_iSup_piece p]
  simp only [Submodule.map_iSup, hs.weilOperator_piece]

/-- The Weil operator preserves every step of the conjugate Hodge filtration. -/
@[simp]
theorem weilOperator_conjF (hs : HodgeStructureOn W ω n) (p : ℤ) :
    (hs.conjF p).map hs.weilOperator = hs.conjF p := by
  rw [hs.conjF_eq_iSup_piece p]
  simp only [Submodule.map_iSup, hs.weilOperator_piece]

/-- Elementwise form of preservation of the Hodge filtration. -/
theorem weilOperator_mem_F (hs : HodgeStructureOn W ω n) {p : ℤ} {x : W} (hx : x ∈ hs.F p) :
    hs.weilOperator x ∈ hs.F p :=
  (hs.weilOperator_F p).le ⟨x, hx, rfl⟩

/-- Elementwise form of preservation of the conjugate Hodge filtration. -/
theorem weilOperator_mem_conjF (hs : HodgeStructureOn W ω n) {p : ℤ} {x : W}
    (hx : x ∈ hs.conjF p) : hs.weilOperator x ∈ hs.conjF p :=
  (hs.weilOperator_conjF p).le ⟨x, hx, rfl⟩

/-- **The Weil operator squares to the weight sign:** `C ∘ C = (-1)^n`. -/
theorem weilOperator_comp_weilOperator (hs : HodgeStructureOn W ω n) :
    hs.weilOperator ∘ₗ hs.weilOperator = ((-1 : ℂ) ^ n) • LinearMap.id :=
  hs.linearMap_ext_of_piece fun p x hx ↦ by
    rw [LinearMap.comp_apply, hs.weilOperator_apply_of_mem hx, map_smul,
      hs.weilOperator_apply_of_mem hx, smul_smul, I_zpow_mul_self,
      negOne_zpow_two_mul_sub, LinearMap.smul_apply, LinearMap.id_apply]

/-- The Weil operator squares to `-1` in odd weight, where it is therefore a complex structure. -/
theorem weilOperator_comp_weilOperator_of_odd (hs : HodgeStructureOn W ω n) (hn : Odd n) :
    hs.weilOperator ∘ₗ hs.weilOperator = -LinearMap.id := by
  rw [hs.weilOperator_comp_weilOperator, hn.neg_one_zpow, neg_one_smul]

/-- The Weil operator is an involution in even weight. -/
theorem weilOperator_comp_weilOperator_of_even (hs : HodgeStructureOn W ω n) (hn : Even n) :
    hs.weilOperator ∘ₗ hs.weilOperator = LinearMap.id := by
  rw [hs.weilOperator_comp_weilOperator, hn.neg_one_zpow, one_smul]

/-- Doubling a power of `-1` gives one. -/
private theorem negOne_zpow_mul_self (k : ℤ) : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← two_mul, zpow_mul]
  norm_num

/-- The Weil operator is inverted by `(-1)^n` times itself, on the right. -/
theorem weilOperator_comp_smul_weilOperator (hs : HodgeStructureOn W ω n) :
    hs.weilOperator ∘ₗ (((-1 : ℂ) ^ n) • hs.weilOperator) = LinearMap.id := by
  rw [LinearMap.comp_smul, hs.weilOperator_comp_weilOperator, smul_smul,
    negOne_zpow_mul_self, one_smul]

/-- The Weil operator is inverted by `(-1)^n` times itself, on the left. -/
theorem smul_weilOperator_comp_weilOperator (hs : HodgeStructureOn W ω n) :
    (((-1 : ℂ) ^ n) • hs.weilOperator) ∘ₗ hs.weilOperator = LinearMap.id := by
  rw [LinearMap.smul_comp, hs.weilOperator_comp_weilOperator, smul_smul,
    negOne_zpow_mul_self, one_smul]

/-- The Weil operator, bundled as a complex-linear automorphism of the ambient space. -/
noncomputable def weilOperatorEquiv (hs : HodgeStructureOn W ω n) : W ≃ₗ[ℂ] W :=
  LinearEquiv.ofLinearMap hs.weilOperator (((-1 : ℂ) ^ n) • hs.weilOperator)
    hs.weilOperator_comp_smul_weilOperator hs.smul_weilOperator_comp_weilOperator

/-- The bundled Weil operator acts as the Weil operator. -/
@[simp]
theorem weilOperatorEquiv_apply (hs : HodgeStructureOn W ω n) (x : W) :
    hs.weilOperatorEquiv x = hs.weilOperator x := by
  simp [weilOperatorEquiv]

/-- The inverse of the bundled Weil operator is `(-1)^n` times the Weil operator. -/
@[simp]
theorem weilOperatorEquiv_symm_apply (hs : HodgeStructureOn W ω n) (x : W) :
    hs.weilOperatorEquiv.symm x = ((-1 : ℂ) ^ n) • hs.weilOperator x := by
  simp [weilOperatorEquiv]

/-- The Weil operator is bijective. -/
theorem weilOperator_bijective (hs : HodgeStructureOn W ω n) :
    Function.Bijective hs.weilOperator :=
  hs.weilOperatorEquiv.bijective

/-- In weight one the Weil operator acts on `H^{1,0}` by `i`. Together with the next lemma this
identifies it with the complex structure of an effective weight-one Hodge structure. -/
theorem weilOperator_apply_of_mem_piece_one {hs : HodgeStructureOn W ω 1} {x : W}
    (hx : x ∈ hs.piece 1) : hs.weilOperator x = Complex.I • x := by
  rw [hs.weilOperator_apply_of_mem hx]
  norm_num

/-- In weight one the Weil operator acts on `H^{0,1}` by `-i`. -/
theorem weilOperator_apply_of_mem_piece_zero {hs : HodgeStructureOn W ω 1} {x : W}
    (hx : x ∈ hs.piece 0) : hs.weilOperator x = -(Complex.I • x) := by
  have h_exp : 2 * (0 : ℤ) - 1 = -1 := by ring
  rw [hs.weilOperator_apply_of_mem hx, h_exp, zpow_neg, zpow_one, Complex.inv_I, neg_smul]

/-- **The Weil operator is real:** it commutes with the conjugation of the Hodge structure. This
is what lets the Hermitian form `Q(C u, conj v)` be assembled from the scalars `i^{p-q}`. -/
@[simp]
theorem conj_weilOperator (hs : HodgeStructureOn W ω n) (x : W) :
    ω.toEquiv (hs.weilOperator x) = hs.weilOperator (ω.toEquiv x) := by
  refine hs.piece_induction_on
    (motive := fun w ↦ ω.toEquiv (hs.weilOperator w) = hs.weilOperator (ω.toEquiv w)) x
    (fun p y hy ↦ ?_) (by simp) fun y z hy hz ↦ by simp [map_add, hy, hz]
  have hconj : ω.toEquiv y ∈ hs.piece (n - p) := by
    rw [← hs.conj_piece p]
    exact ⟨y, hy, rfl⟩
  rw [hs.weilOperator_apply_of_mem hy, map_smulₛₗ, hs.weilOperator_apply_of_mem hconj]
  congr 1
  have h_exp : 2 * (n - p) - n = -(2 * p - n) := by ring
  rw [map_zpow₀, Complex.conj_I, h_exp, zpow_neg, ← inv_zpow, Complex.inv_I]

end HodgeStructureOn

/-! ### Compatibility with polarizing forms -/

section PolarizingForm

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ} {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ}
variable {hs : HodgeStructure hℂ n}

namespace IsPolarization

variable {Q : LinearMap.BilinForm ℤ V}

/-- **The Weil operator is an isometry of the polarizing form.** Two Hodge components pair to
zero unless their degrees add up to the weight, and on a pair of components that do, the two
scalars `i^(2p-n)` and `i^(2p'-n)` by which the Weil operator acts are inverse to each other. -/
theorem isOrthogonal_weilOperator (h : IsPolarization hℂ hs Q) :
    (integralFormToComplex hℂ Q).IsOrthogonal hs.weilOperator := by
  have key : ((integralFormToComplex hℂ Q) ∘ₗ hs.weilOperator).compl₂ hs.weilOperator =
      integralFormToComplex hℂ Q := by
    refine hs.linearMap_ext_of_piece fun p x hx ↦ hs.linearMap_ext_of_piece fun p' y hy ↦ ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply]
    by_cases hpp : p + p' = n
    · rw [hs.weilOperator_apply_of_mem hx, hs.weilOperator_apply_of_mem hy]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      have hexp : 2 * p' - n + (2 * p - n) = 0 := by omega
      rw [← mul_assoc, ← zpow_add₀ Complex.I_ne_zero, hexp, zpow_zero, one_mul]
    · rw [h.orthogonal_piece hpp (hs.weilOperator_mem_piece hx) (hs.weilOperator_mem_piece hy),
        h.orthogonal_piece hpp hx hy]
  intro x y
  simpa using DFunLike.congr_fun (DFunLike.congr_fun key x) y

end IsPolarization

namespace Polarization

/-- The Weil operator is an isometry of the complex form of a polarization. -/
@[simp]
theorem Q_weilOperator (P : Polarization hℂ hs) (x y : Vℂ) :
    P.Q (hs.weilOperator x) (hs.weilOperator y) = P.Q x y := by
  rw [P.Q_def]
  exact P.isPolarization.isOrthogonal_weilOperator x y

end Polarization

end PolarizingForm

namespace HodgeStructure.Hom

universe u₁ v₁ u₂ v₂

variable {V₁ : Type u₁} {V₂ : Type u₂} {W₁ : Type v₁} {W₂ : Type v₂}
variable [AddCommGroup V₁] [AddCommGroup V₂]
variable [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
variable {ι₁ : V₁ →ₗ[ℤ] W₁} {ι₂ : V₂ →ₗ[ℤ] W₂}
variable {h₁ : IsBaseChange ℂ ι₁} {h₂ : IsBaseChange ℂ ι₂} {n : ℤ}
variable {source : HodgeStructure h₁ n} {target : HodgeStructure h₂ n}

/-- A morphism of pure Hodge structures commutes with the Weil operators: it preserves every
Hodge component, on which both operators are the same scalar. -/
@[simp]
theorem commutes_weilOperator (f : Hom source target) (x : W₁) :
    f (source.weilOperator x) = target.weilOperator (f x) := by
  refine source.piece_induction_on
    (motive := fun w ↦ f (source.weilOperator w) = target.weilOperator (f w)) x
    (fun p y hy ↦ ?_) (by simp) fun y z hy hz ↦ by simp [map_add, hy, hz]
  rw [source.weilOperator_apply_of_mem hy, map_smul,
    target.weilOperator_apply_of_mem (f.map_mem_piece p hy)]

end HodgeStructure.Hom

/-- The Weil operator of the Tate structure `ℤ(m)` is the identity: its single Hodge component
has `p = q = -m`, where the scalar `i^{p-q}` is one. -/
@[simp]
theorem tate_weilOperator (m : ℤ) : (tate m).weilOperator = LinearMap.id := by
  refine LinearMap.ext fun x ↦ ?_
  have hx : x ∈ (tate m).piece (-m) := by
    rw [tate_piece]
    simp
  have h_exp : 2 * -m - -2 * m = (0 : ℤ) := by ring
  rw [(tate m).weilOperator_apply_of_mem hx, h_exp]
  simp

end TauCeti.Hodge
