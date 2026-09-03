/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Dimension
public import TauCeti.Geometry.Hodge.Morphism
public import TauCeti.Geometry.Hodge.Polarization

/-!
# Tate twists of pure Hodge structures

The `m`-th Tate twist of a pure Hodge structure of weight `n` has weight `n - 2m` and
filtration `F^p(V(m)) = F^{p+m}(V)`. The underlying lattice and complex vector space are unchanged:
this presents `V ⊗ ℤ(m)` through the canonical identifications `V ⊗_ℤ ℤ ≃ V` and
`V_ℂ ⊗_ℂ ℂ ≃ V_ℂ`. Thus the construction works directly with the abstract base-change
interface and introduces no choice of tensor-product equivalence.

The shift carries Hodge components and Hodge numbers by the same translation. It also acts on
morphisms. A polarizing form for `V` polarizes `V(m)` unchanged: subtracting the even integer `2m`
does not change the symmetry sign, while both the filtration indices and the exponent in the
Hodge–Riemann positivity relation shift compatibly.

This is the Tate-twist companion in Layer L0 of
`TauCetiRoadmap/HodgeStructures/README.md`. The convention follows Voisin,
*Hodge Theory and Complex Algebraic Geometry I*, §§7.1–7.2.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.tateTwist`: the Tate twist of a pure Hodge structure.
* `TauCeti.Hodge.HodgeStructureOn.tateTwist_piece`: its component in degree `p` is the original
  component in degree `p + m`.
* `TauCeti.Hodge.HodgeStructure.Hom.tateTwist`: the induced operation on Hodge morphisms.
* `TauCeti.Hodge.IsPolarization.tateTwist`: a polarizing form remains polarizing after twisting.
* `TauCeti.Hodge.Polarization.tateTwist`: the corresponding bundled polarization.
-/

public section

namespace TauCeti.Hodge

open scoped ComplexOrder

universe u v u₁ v₁ u₂ v₂ u₃ v₃

namespace HodgeStructureOn

variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable {ω : Conjugation W} {n : ℤ}

/-- The `m`-th Tate twist of a pure Hodge structure of weight `n`.

Its weight is `n - 2m`, and its filtration is shifted by `m`. The unchanged underlying vector
space is the canonical presentation of tensoring with the one-dimensional Tate structure. -/
def tateTwist (hs : HodgeStructureOn W ω n) (m : ℤ) :
    HodgeStructureOn W ω (n - 2 * m) where
  F p := hs.F (p + m)
  F_antitone _ _ hpq := hs.F_antitone (by omega)
  F_top := by
    obtain ⟨p, hp⟩ := hs.F_top
    exact ⟨p - m, by simpa only [sub_add_cancel] using hp⟩
  opposed p := by
    have hindex : n - 2 * m + 1 - p + m = n + 1 - (p + m) := by ring
    simpa only [hindex] using hs.opposed (p + m)

/-- Weight normalization: a cast between Hodge structures whose weights are propositionally equal
is determined by the filtrations.

Weights that are equal only propositionally give *different* types `HodgeStructureOn W ω a` and
`HodgeStructureOn W ω b`, so a normalization law such as `tateTwist_zero` or `tateTwist_add` can
only be stated after transporting one side along the type equality `h`. Once the weights are
identified by `hab`, definitional proof irrelevance makes `h` interchangeable with `rfl`, so no
hypothesis relating `h` to `hab` is needed and the cast disappears. -/
private theorem cast_eq_of_F {a b : ℤ} (hab : a = b)
    (h : HodgeStructureOn W ω a = HodgeStructureOn W ω b)
    (hs : HodgeStructureOn W ω a) (hs' : HodgeStructureOn W ω b)
    (hF : ∀ p, hs.F p = hs'.F p) : cast h hs = hs' := by
  subst hab
  exact HodgeStructureOn.ext (funext hF)

/-- Twisting by zero leaves a Hodge structure unchanged. -/
@[simp]
theorem tateTwist_zero (hs : HodgeStructureOn W ω n)
    {h : HodgeStructureOn W ω (n - 2 * 0) = HodgeStructureOn W ω n} :
    cast h (hs.tateTwist 0) = hs :=
  cast_eq_of_F (by ring) h _ _ fun p => by
    simp only [tateTwist, add_zero]

/-- Two successive Tate twists combine by adding their indices. -/
@[simp]
theorem tateTwist_add (hs : HodgeStructureOn W ω n) (m k : ℤ)
    {h : HodgeStructureOn W ω (n - 2 * m - 2 * k) =
      HodgeStructureOn W ω (n - 2 * (m + k))} :
    cast h ((hs.tateTwist m).tateTwist k) = hs.tateTwist (m + k) :=
  cast_eq_of_F (by ring) h _ _ fun p => by
    simp only [tateTwist]
    congr 1
    ring

/-- The Hodge filtration of a Tate twist is the translated original filtration. -/
@[simp]
theorem tateTwist_F (hs : HodgeStructureOn W ω n) (m p : ℤ) :
    (hs.tateTwist m).F p = hs.F (p + m) :=
  (rfl)

/-- The conjugate filtration of a Tate twist is translated by the same amount. -/
@[simp]
theorem tateTwist_conjF (hs : HodgeStructureOn W ω n) (m p : ℤ) :
    (hs.tateTwist m).conjF p = hs.conjF (p + m) := by
  rw [conjF_def, conjF_def, tateTwist_F]

/-- The `p`-th Hodge component of `V(m)` is the `(p+m)`-th component of `V`. -/
@[simp]
theorem tateTwist_piece (hs : HodgeStructureOn W ω n) (m p : ℤ) :
    (hs.tateTwist m).piece p = hs.piece (p + m) := by
  rw [piece_def, piece_def, tateTwist_F, tateTwist_conjF]
  congr 2
  ring

/-- The Hodge numbers of a Tate twist are translated by `m`. -/
@[simp]
theorem tateTwist_hodgeNumber (hs : HodgeStructureOn W ω n) (m p : ℤ) :
    (hs.tateTwist m).hodgeNumber p = hs.hodgeNumber (p + m) := by
  rw [hodgeNumber_def, hodgeNumber_def, tateTwist_piece]

/-- A Tate twist is effective exactly when its translated zeroth filtration step is the whole
space. This is not a `simp` lemma: with `HodgeStructureOn.isEffective_iff` and
`HodgeStructureOn.tateTwist_F` tagged, `simp` already normalizes the left-hand side. -/
theorem isEffective_tateTwist_iff (hs : HodgeStructureOn W ω n) (m : ℤ) :
    (hs.tateTwist m).IsEffective ↔ hs.F m = ⊤ := by
  rw [isEffective_iff, tateTwist_F, zero_add]

/-- Equivalently, a Tate twist is effective exactly when the translated filtration vanishes one
step above its new weight. -/
theorem isEffective_tateTwist_iff_F_eq_bot (hs : HodgeStructureOn W ω n) (m : ℤ) :
    (hs.tateTwist m).IsEffective ↔ hs.F (n + 1 - m) = ⊥ := by
  rw [isEffective_iff_F_eq_bot, tateTwist_F]
  have hindex : n - 2 * m + 1 + m = n + 1 - m := by ring
  rw [hindex]

end HodgeStructureOn

namespace HodgeStructure.Hom

variable {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃}
variable {W₁ : Type v₁} {W₂ : Type v₂} {W₃ : Type v₃}
variable [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃]
variable [AddCommGroup W₁] [Module ℂ W₁]
variable [AddCommGroup W₂] [Module ℂ W₂]
variable [AddCommGroup W₃] [Module ℂ W₃]
variable {ι₁ : V₁ →ₗ[ℤ] W₁} {ι₂ : V₂ →ₗ[ℤ] W₂} {ι₃ : V₃ →ₗ[ℤ] W₃}
variable {h₁ : IsBaseChange ℂ ι₁} {h₂ : IsBaseChange ℂ ι₂} {h₃ : IsBaseChange ℂ ι₃}
variable {n : ℤ}
variable {source : HodgeStructure h₁ n} {target : HodgeStructure h₂ n}
variable {third : HodgeStructure h₃ n}

/-- A Hodge morphism induces a morphism between the same Tate twists of its source and target. -/
noncomputable def tateTwist (f : Hom source target) (m : ℤ) :
    Hom (source.tateTwist m) (target.tateTwist m) where
  toIntLinearMap := f.toIntLinearMap
  map_mem_F p x hx := f.map_mem_F (p + m) x hx

/-- Twisting a morphism does not change its underlying integral linear map. -/
@[simp]
theorem tateTwist_toIntLinearMap (f : Hom source target) (m : ℤ) :
    (f.tateTwist m).toIntLinearMap = f.toIntLinearMap :=
  (rfl)

/-- Twisting a morphism does not change its action on the complexification. -/
@[simp]
theorem tateTwist_apply (f : Hom source target) (m : ℤ) (x : W₁) :
    f.tateTwist m x = f x := by
  have hmaps : (f.tateTwist m).toLinearMap = f.toLinearMap := by
    apply h₁.algHom_ext
    intro y
    simp
  exact LinearMap.congr_fun hmaps x

/-- Tate twist preserves identity morphisms. -/
@[simp]
theorem tateTwist_id (source : HodgeStructure h₁ n) (m : ℤ) :
    (id source).tateTwist m = id (source.tateTwist m) := by
  ext x
  simp

/-- Tate twist preserves composition of Hodge morphisms. -/
@[simp]
theorem tateTwist_comp (g : Hom target third) (f : Hom source target) (m : ℤ) :
    (g.comp f).tateTwist m = (g.tateTwist m).comp (f.tateTwist m) := by
  ext x
  simp

end HodgeStructure.Hom

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ} {hℂ : IsBaseChange ℂ ιℂ}
variable {n : ℤ} {hs : HodgeStructure hℂ n}
variable {Q : LinearMap.BilinForm ℤ V}

namespace IsPolarization

/-- A form polarizing a pure Hodge structure also polarizes each of its Tate twists. -/
theorem tateTwist (hQ : IsPolarization hℂ hs Q) (m : ℤ) :
    IsPolarization hℂ (hs.tateTwist m) Q where
  symm_weight x y := by
    have hsign : (n - 2 * m).negOnePow = n.negOnePow := by
      rw [Int.negOnePow_sub, Int.negOnePow_two_mul, mul_one]
    rw [hsign]
    exact hQ.symm_weight x y
  nondegenerate := hQ.nondegenerate
  orthogonal p x hx y hy := by
    refine hQ.orthogonal (p + m) x hx y ?_
    have hindex : n - 2 * m + 1 - p + m = n + 1 - (p + m) := by ring
    simpa only [HodgeStructureOn.tateTwist_F, hindex] using hy
  positive p x hx hx0 := by
    have hx' : x ∈ hs.piece (p + m) := by simpa using hx
    have hexp : 2 * p - (n - 2 * m) = 2 * (p + m) - n := by ring
    rw [hexp]
    exact hQ.positive (p + m) x hx' hx0

end IsPolarization

namespace Polarization

/-- The polarization of a Tate twist obtained from a polarization of the original structure. -/
def tateTwist (P : Polarization hℂ hs) (m : ℤ) : Polarization hℂ (hs.tateTwist m) where
  Qint := P.Qint
  isPolarization := P.isPolarization.tateTwist m

/-- Tate twisting a polarization leaves its integral form unchanged. -/
@[simp]
theorem tateTwist_Qint (P : Polarization hℂ hs) (m : ℤ) :
    (P.tateTwist m).Qint = P.Qint :=
  (rfl)

/-- Tate twisting a polarization leaves its complex form unchanged. -/
@[simp]
theorem tateTwist_Q (P : Polarization hℂ hs) (m : ℤ) :
    (P.tateTwist m).Q = P.Q :=
  by rw [Q_def, Q_def, tateTwist_Qint]

end Polarization

/-- Every Tate twist of a polarizable Hodge structure is polarizable. -/
theorem IsPolarizable.tateTwist (h : IsPolarizable hℂ hs) (m : ℤ) :
    IsPolarizable hℂ (hs.tateTwist m) := by
  rw [isPolarizable_iff_nonempty] at h ⊢
  obtain ⟨P⟩ := h
  exact ⟨P.tateTwist m⟩

end TauCeti.Hodge
