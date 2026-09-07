/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Dual
public import TauCeti.Geometry.Hodge.TensorProduct
public import TauCeti.LinearAlgebra.Contraction

/-!
# Internal homs of pure Hodge structures

For pure Hodge structures `V` and `W`, the complex vector space `Hom_ℂ(V, W)` carries a pure
Hodge structure of weight `weight W - weight V`. Its conjugation sends a map `f` to
`x ↦ conj (f (conj x))`, and its degree-`r` component consists of the maps carrying the degree-`p`
component of `V` into the degree-`p+r` component of `W`.

Those degree-shifting subspaces are the construction: since a Hodge decomposition has only
finitely many nonzero components, every linear map is the finite sum of the compositions
`proj_W^q ∘ f ∘ proj_V^p`, so the degree-shifting subspaces decompose `Hom_ℂ(V, W)`. Conjugation
exchanges them in complementary degrees, and they vanish in low degrees, so they form a Hodge
decomposition in the sense of `TauCeti.Hodge.IsHodgeDecomposition`. No finiteness hypothesis on
`V` or `W` is needed.

When `V` is finite-dimensional the construction agrees with the transport of the tensor product of
the dual Hodge structure on `V^*` and the Hodge structure on `W` along Mathlib's contraction
equivalence `V^* ⊗ W ≃ₗ[ℂ] Hom_ℂ(V, W)`; that comparison is
`TauCeti.Hodge.HodgeStructureOn.internalHom_piece_eq_comap`.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.internalHomPiece`: the maps shifting Hodge degree by a fixed
  amount, shown to be a Hodge decomposition by
  `TauCeti.Hodge.HodgeStructureOn.isHodgeDecomposition_internalHomPiece`.
* `TauCeti.Hodge.HodgeStructureOn.internalHom`: the internal hom Hodge structure, of weight
  `n₂ - n₁`, with `TauCeti.Hodge.HodgeStructureOn.internalHom_piece` its components.
* `TauCeti.Hodge.HodgeStructureOn.map_mem_piece_of_mem_internalHom_piece`: a degree-`r` map sends
  the degree-`p` component into the degree-`p+r` component, and
  `TauCeti.Hodge.HodgeStructureOn.mem_internalHom_piece_iff` says this characterizes the
  components.
* `TauCeti.Hodge.HodgeStructureOn.map_mem_F_of_mem_internalHom_F`: a map in filtration degree
  at least `r` sends `F^p V` into `F^{p+r} W`, and
  `TauCeti.Hodge.HodgeStructureOn.mem_internalHom_F_iff` says this characterizes the filtration.
* `TauCeti.Hodge.HodgeStructureOn.id_mem_internalHom_piece` and
  `TauCeti.Hodge.HodgeStructureOn.comp_mem_internalHom_piece`: the identity has internal-hom
  degree `0`, and composing maps adds internal-hom degrees.
* `TauCeti.Hodge.HodgeStructureOn.internalHom_piece_eq_comap` and
  `TauCeti.Hodge.HodgeStructureOn.internalHom_F_eq_comap`: over a finite-dimensional source, the
  internal-hom components and filtration are the pullbacks of those of `V^* ⊗ W` along the
  contraction equivalence.

This is the internal-hom companion to duals and tensor products for pure Hodge structures;
the convention follows Peters--Steenbrink, *Mixed Hodge Structures*, §2.1.
-/

public section

open scoped TensorProduct

namespace TauCeti.Hodge

universe u v w

variable {W₁ : Type u} {W₂ : Type v}
variable [AddCommGroup W₁] [Module ℂ W₁]
variable [AddCommGroup W₂] [Module ℂ W₂]

namespace Conjugation

/-- The contraction `V^* ⊗ W → Hom_ℂ(V, W)` intertwines tensor-product conjugation with the
intrinsic conjugation on the space of linear maps. -/
theorem dualTensorHom_map_tensorProduct_conj (ω₁ : Conjugation W₁) (ω₂ : Conjugation W₂)
    (z : Module.Dual ℂ W₁ ⊗[ℂ] W₂) :
    dualTensorHom ℂ W₁ W₂ ((ω₁.dual.tensorProduct ω₂).toEquiv z) =
      (ω₁.internalHom ω₂).toEquiv (dualTensorHom ℂ W₁ W₂ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul φ y =>
      ext x
      simpa only [Conjugation.tensorProduct_toEquiv_tmul, Conjugation.dual_toEquiv_apply,
        dualTensorHom_apply, Conjugation.internalHom_toEquiv_apply_apply, starRingEnd_apply] using
          (ω₂.toEquiv.map_smulₛₗ (φ (ω₁.toEquiv x)) y).symm
  | add x y hx hy => simp [hx, hy]

/-- The inverse of the finite-dimensional contraction equivalence intertwines internal-hom
conjugation with tensor-product conjugation. -/
theorem dualTensorHomEquiv_symm_map_internalHom_conj [FiniteDimensional ℂ W₁]
    (ω₁ : Conjugation W₁) (ω₂ : Conjugation W₂) (f : W₁ →ₗ[ℂ] W₂) :
    (dualTensorHomEquiv ℂ W₁ W₂).symm ((ω₁.internalHom ω₂).toEquiv f) =
      (ω₁.dual.tensorProduct ω₂).toEquiv ((dualTensorHomEquiv ℂ W₁ W₂).symm f) := by
  apply (dualTensorHomEquiv ℂ W₁ W₂).injective
  rw [LinearEquiv.apply_symm_apply, dualTensorHomEquiv_apply,
    ω₁.dualTensorHom_map_tensorProduct_conj ω₂, ← dualTensorHomEquiv_apply,
    LinearEquiv.apply_symm_apply]

end Conjugation

namespace HodgeStructureOn

variable {ω₁ : Conjugation W₁} {ω₂ : Conjugation W₂} {n₁ n₂ : ℤ}

/-- The complex-linear maps shifting Hodge degree by exactly `r`: those carrying the degree-`a`
component of the source into the degree-`a + r` component of the target. These subspaces are the
Hodge components of the internal hom, by
`TauCeti.Hodge.HodgeStructureOn.internalHom_piece`. -/
def internalHomPiece (hs₁ : HodgeStructureOn W₁ ω₁ n₁) (hs₂ : HodgeStructureOn W₂ ω₂ n₂)
    (r : ℤ) : Submodule ℂ (W₁ →ₗ[ℂ] W₂) where
  carrier := {f | ∀ a, ∀ x ∈ hs₁.piece a, f x ∈ hs₂.piece (a + r)}
  add_mem' := fun hf hg a x hx ↦ by
    simpa using Submodule.add_mem _ (hf a x hx) (hg a x hx)
  zero_mem' := fun a x _ ↦ by simp
  smul_mem' := fun c f hf a x hx ↦ by
    simpa using Submodule.smul_mem _ c (hf a x hx)

/-- A map shifts Hodge degree by `r` exactly when it carries every source component of degree `a`
into the target component of degree `a + r`. -/
theorem mem_internalHomPiece_iff (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {r : ℤ} {f : W₁ →ₗ[ℂ] W₂} :
    f ∈ hs₁.internalHomPiece hs₂ r ↔ ∀ a, ∀ x ∈ hs₁.piece a, f x ∈ hs₂.piece (a + r) :=
  Iff.rfl

/-- Conjugating a map shifting Hodge degree by `r` gives one shifting Hodge degree by the
complementary amount `n₂ - n₁ - r`. -/
theorem conj_mem_internalHomPiece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {r : ℤ} {f : W₁ →ₗ[ℂ] W₂}
    (hf : f ∈ hs₁.internalHomPiece hs₂ r) :
    (ω₁.internalHom ω₂).toEquiv f ∈ hs₁.internalHomPiece hs₂ (n₂ - n₁ - r) := by
  simp only [mem_internalHomPiece_iff] at hf ⊢
  intro a x hx
  have hidx : a + (n₂ - n₁ - r) = n₂ - (n₁ - a + r) := by ring
  rw [Conjugation.internalHom_toEquiv_apply_apply, hidx]
  exact hs₂.conj_mem_piece (hf _ _ (hs₁.conj_mem_piece hx))

/-- Maps shifting Hodge degree by different amounts are independent. -/
theorem internalHomPiece_iSupIndep (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) : iSupIndep (hs₁.internalHomPiece hs₂) := by
  intro r
  rw [Submodule.disjoint_def]
  intro f hf hf'
  refine hs₁.linearMap_ext_of_piece (g := 0) fun a x hx ↦ ?_
  have hmem : f x ∈ ⨆ b, ⨆ (_ : b ≠ a + r), hs₂.piece b := by
    refine Submodule.iSup_induction
      (motive := fun g ↦ g x ∈ ⨆ b, ⨆ (_ : b ≠ a + r), hs₂.piece b) _ hf'
      (fun s g hg ↦ ?_) (by simp) (fun g h hg hh ↦ by simpa using Submodule.add_mem _ hg hh)
    refine Submodule.iSup_induction
      (motive := fun g ↦ g x ∈ ⨆ b, ⨆ (_ : b ≠ a + r), hs₂.piece b) _ hg
      (fun hsr g hg ↦ ?_) (by simp) (fun g h hg hh ↦ by simpa using Submodule.add_mem _ hg hh)
    have hle : hs₂.piece (a + s) ≤ ⨆ b, ⨆ (_ : b ≠ a + r), hs₂.piece b :=
      le_iSup₂_of_le (a + s) (by omega) le_rfl
    exact hle (hg a x hx)
  simpa using Submodule.disjoint_def.1 (hs₂.piece_iSupIndep (a + r)) _ (hf a x hx) hmem

/-- The maps shifting Hodge degree span the whole space of linear maps: a map is the finite sum of
its components `proj^b ∘ f ∘ proj^a`. -/
theorem iSup_internalHomPiece_eq_top (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) : ⨆ r, hs₁.internalHomPiece hs₂ r = ⊤ := by
  classical
  refine top_unique fun f _ ↦ ?_
  -- Only finitely many components are nonzero on either side.
  obtain ⟨S₁, hS₁⟩ : ∃ S : Finset ℤ, ∀ a ∉ S, hs₁.piece a = ⊥ :=
    ⟨hs₁.finite_setOf_piece_ne_bot.toFinset, fun a ha ↦ by simpa using ha⟩
  obtain ⟨S₂, hS₂⟩ : ∃ S : Finset ℤ, ∀ b ∉ S, hs₂.piece b = ⊥ :=
    ⟨hs₂.finite_setOf_piece_ne_bot.toFinset, fun b hb ↦ by simpa using hb⟩
  have hf : f = ∑ a ∈ S₁, ∑ b ∈ S₂, (hs₂.proj b).comp (f.comp (hs₁.proj a)) := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    calc f x
        = f (∑ a ∈ S₁, hs₁.proj a x) := by rw [hs₁.sum_proj_eq hS₁ x]
      _ = ∑ a ∈ S₁, f (hs₁.proj a x) := map_sum f _ _
      _ = ∑ a ∈ S₁, ∑ b ∈ S₂, hs₂.proj b (f (hs₁.proj a x)) :=
          Finset.sum_congr rfl fun a _ ↦ (hs₂.sum_proj_eq hS₂ _).symm
  rw [hf]
  refine Submodule.sum_mem _ fun a _ ↦ Submodule.sum_mem _ fun b _ ↦ ?_
  refine Submodule.mem_iSup_of_mem (b - a) ?_
  simp only [mem_internalHomPiece_iff, LinearMap.comp_apply]
  intro c x hx
  by_cases hca : a = c
  · subst hca
    have hidx : a + (b - a) = b := by ring
    rw [hs₁.proj_apply_of_mem hx, hidx]
    exact hs₂.proj_mem b (f x)
  · rw [hs₁.proj_apply_eq_zero_of_mem_of_ne hx (Ne.symm hca), map_zero, map_zero]
    exact Submodule.zero_mem _

/-- **The Hodge decomposition of an internal hom.** The maps shifting Hodge degree by a fixed
amount decompose the space of complex-linear maps, are exchanged by the internal-hom conjugation
in complementary degrees, and vanish in low degrees. -/
theorem isHodgeDecomposition_internalHomPiece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) :
    IsHodgeDecomposition (ω₁.internalHom ω₂) (n₂ - n₁) (hs₁.internalHomPiece hs₂) where
  isInternal := by
    classical
    exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (hs₁.internalHomPiece_iSupIndep hs₂) (hs₁.iSup_internalHomPiece_eq_top hs₂)
  map_conj r := by
    refine le_antisymm ?_ fun f hf ↦ ?_
    · rintro _ ⟨g, hg, rfl⟩
      exact hs₁.conj_mem_internalHomPiece hs₂ hg
    · refine ⟨(ω₁.internalHom ω₂).toEquiv f, ?_, (ω₁.internalHom ω₂).apply_apply f⟩
      have hidx : n₂ - n₁ - (n₂ - n₁ - r) = r := by ring
      have h := hs₁.conj_mem_internalHomPiece hs₂ hf
      rwa [hidx] at h
  exists_forall_lt_eq_bot := by
    obtain ⟨a₂, ha₂⟩ := hs₂.F_top
    obtain ⟨b₁, hb₁⟩ := hs₁.F_bot
    refine ⟨a₂ - b₁, fun r hr ↦ (Submodule.eq_bot_iff _).2 fun f hf ↦ ?_⟩
    refine hs₁.linearMap_ext_of_piece (g := 0) fun a x hx ↦ ?_
    by_cases hab : b₁ ≤ a
    · rw [hs₁.piece_eq_bot_of_F_eq_bot hb₁ hab] at hx
      rw [(Submodule.mem_bot ℂ).1 hx]
      simp
    · have hbot : hs₂.piece (a + r) = ⊥ := hs₂.piece_eq_bot_of_F_eq_top ha₂ (by omega)
      have hzero := hf a x hx
      rw [hbot] at hzero
      simpa using hzero

/-- **The internal hom** of a pure Hodge structure of weight `n₁` and one of weight `n₂`, as a
pure Hodge structure of weight `n₂ - n₁` on the space of complex-linear maps.

Its components are the maps shifting Hodge degree by a fixed amount. -/
noncomputable def internalHom (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) :
    HodgeStructureOn (W₁ →ₗ[ℂ] W₂) (ω₁.internalHom ω₂) (n₂ - n₁) :=
  ofDecomposition (hs₁.isHodgeDecomposition_internalHomPiece hs₂)

/-- The degree-`r` component of the internal hom is the space of maps shifting Hodge degree
by `r`. -/
@[simp]
theorem internalHom_piece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (r : ℤ) :
    (hs₁.internalHom hs₂).piece r = hs₁.internalHomPiece hs₂ r :=
  ofDecomposition_piece _ r

/-- The internal-hom filtration is the sum of the components shifting Hodge degree by at
least `p`. -/
@[simp]
theorem internalHom_F (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.internalHom hs₂).F p = ⨆ r, ⨆ (_ : p ≤ r), hs₁.internalHomPiece hs₂ r :=
  ofDecomposition_F _ p

/-- The conjugate internal-hom filtration is the sum of the components shifting Hodge degree by
less than the complementary index. -/
@[simp]
theorem internalHom_conjF (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.internalHom hs₂).conjF p =
      ⨆ r, ⨆ (_ : r < n₂ - n₁ + 1 - p), hs₁.internalHomPiece hs₂ r :=
  ofDecomposition_conjF _ p

/-- A map of internal-hom Hodge degree `p` carries the source component of degree `a` into the
target component of degree `a + p`. -/
theorem map_mem_piece_of_mem_internalHom_piece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p a : ℤ} {f : W₁ →ₗ[ℂ] W₂}
    (hf : f ∈ (hs₁.internalHom hs₂).piece p) {x : W₁} (hx : x ∈ hs₁.piece a) :
    f x ∈ hs₂.piece (a + p) := by
  rw [internalHom_piece, mem_internalHomPiece_iff] at hf
  exact hf a x hx

/-- A map lies in the degree-`p` internal-hom component exactly when it carries every source
component of degree `a` into the target component of degree `a + p`. -/
theorem mem_internalHom_piece_iff (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p : ℤ} (f : W₁ →ₗ[ℂ] W₂) :
    f ∈ (hs₁.internalHom hs₂).piece p ↔ ∀ a, ∀ x ∈ hs₁.piece a, f x ∈ hs₂.piece (a + p) := by
  rw [internalHom_piece, mem_internalHomPiece_iff]

/-- The identity map has internal-hom degree `0`. -/
theorem id_mem_internalHom_piece (hs : HodgeStructureOn W₁ ω₁ n₁) :
    LinearMap.id ∈ (hs.internalHom hs).piece 0 := by
  rw [mem_internalHom_piece_iff]
  intro a x hx
  simpa using hx

/-- Composing a map of internal-hom degree `p` with one of internal-hom degree `q` gives a map of
internal-hom degree `p + q`. -/
theorem comp_mem_internalHom_piece {W₃ : Type w} [AddCommGroup W₃] [Module ℂ W₃]
    {ω₃ : Conjugation W₃} {n₃ : ℤ} (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (hs₃ : HodgeStructureOn W₃ ω₃ n₃) {p q : ℤ}
    {f : W₁ →ₗ[ℂ] W₂} {g : W₂ →ₗ[ℂ] W₃} (hf : f ∈ (hs₁.internalHom hs₂).piece p)
    (hg : g ∈ (hs₂.internalHom hs₃).piece q) :
    g ∘ₗ f ∈ (hs₁.internalHom hs₃).piece (p + q) := by
  rw [mem_internalHom_piece_iff]
  intro a x hx
  have hidx : a + p + q = a + (p + q) := by ring
  rw [LinearMap.comp_apply, ← hidx]
  exact hs₂.map_mem_piece_of_mem_internalHom_piece hs₃ hg
    (hs₁.map_mem_piece_of_mem_internalHom_piece hs₂ hf hx)

/-- A rank-one map made from a dual vector of degree `p` and a target vector of degree `q` has
internal-hom degree `p + q`. -/
theorem dualTensorHom_mem_internalHom_piece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p q : ℤ} {φ : Module.Dual ℂ W₁} {y : W₂}
    (hφ : φ ∈ (hs₁.dual).piece p) (hy : y ∈ hs₂.piece q) :
    dualTensorHom ℂ W₁ W₂ (φ ⊗ₜ[ℂ] y) ∈ (hs₁.internalHom hs₂).piece (p + q) := by
  rw [mem_internalHom_piece_iff]
  intro a x hx
  rw [dualTensorHom_apply]
  by_cases hap : a = -p
  · subst hap
    have hidx : -p + (p + q) = q := by ring
    rw [hidx]
    exact Submodule.smul_mem _ _ hy
  · rw [hs₁.apply_eq_zero_of_mem_piece_of_ne hx hφ hap, zero_smul]
    exact Submodule.zero_mem _

/-- The degree-`r` internal-hom component of a map, evaluated at a vector of Hodge degree `a`,
is the degree-`a + r` component of the value. -/
theorem internalHom_proj_apply_apply (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {r a : ℤ} (f : W₁ →ₗ[ℂ] W₂) {x : W₁}
    (hx : x ∈ hs₁.piece a) :
    (hs₁.internalHom hs₂).proj r f x = hs₂.proj (a + r) (f x) := by
  have hext : LinearMap.applyₗ (R := ℂ) x ∘ₗ (hs₁.internalHom hs₂).proj r =
      hs₂.proj (a + r) ∘ₗ LinearMap.applyₗ (R := ℂ) x := by
    refine (hs₁.internalHom hs₂).linearMap_ext_of_piece fun s g hg ↦ ?_
    have hgx : g x ∈ hs₂.piece (a + s) := hs₁.map_mem_piece_of_mem_internalHom_piece hs₂ hg hx
    rcases eq_or_ne s r with rfl | hsr
    · simp only [LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
        (hs₁.internalHom hs₂).proj_apply_of_mem hg, hs₂.proj_apply_of_mem hgx]
    · simp only [LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
        (hs₁.internalHom hs₂).proj_apply_eq_zero_of_mem_of_ne hg hsr, LinearMap.zero_apply,
        hs₂.proj_apply_eq_zero_of_mem_of_ne hgx (by omega : a + s ≠ a + r)]
  exact congrArg (fun L ↦ L f) hext

/-- A map in the `p`-th step of the internal-hom filtration sends the `q`-th step of the source
filtration into the `(p+q)`-th step of the target filtration. -/
theorem map_mem_F_of_mem_internalHom_F (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p q : ℤ} {f : W₁ →ₗ[ℂ] W₂}
    (hf : f ∈ (hs₁.internalHom hs₂).F p) {x : W₁} (hx : x ∈ hs₁.F q) :
    f x ∈ hs₂.F (p + q) := by
  rw [(hs₁.internalHom hs₂).F_eq_iSup_piece p] at hf
  refine Submodule.iSup_induction (motive := fun g ↦ g x ∈ hs₂.F (p + q)) _ hf
    (fun r g hg ↦ ?_) (by simp) (fun g h hg hh ↦ by simpa using Submodule.add_mem _ hg hh)
  refine Submodule.iSup_induction (motive := fun g ↦ g x ∈ hs₂.F (p + q)) _ hg
    (fun hr g hg ↦ ?_) (by simp) (fun g h hg hh ↦ by simpa using Submodule.add_mem _ hg hh)
  rw [hs₁.F_eq_iSup_piece q] at hx
  refine Submodule.iSup_induction (motive := fun y ↦ g y ∈ hs₂.F (p + q)) _ hx
    (fun a y hy ↦ ?_) (by simp) (fun y z hy hz ↦ by simpa using Submodule.add_mem _ hy hz)
  refine Submodule.iSup_induction (motive := fun y ↦ g y ∈ hs₂.F (p + q)) _ hy
    (fun ha y hy ↦ ?_) (by simp) (fun y z hy hz ↦ by simpa using Submodule.add_mem _ hy hz)
  exact ((hs₂.piece_le_F (a + r)).trans (hs₂.F_antitone (by omega)))
    (hs₁.map_mem_piece_of_mem_internalHom_piece hs₂ hg hy)

/-- A map lies in the `p`-th step of the internal-hom filtration exactly when it sends every
step `F^q` of the source filtration into the step `F^{p+q}` of the target filtration. -/
theorem mem_internalHom_F_iff (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p : ℤ} (f : W₁ →ₗ[ℂ] W₂) :
    f ∈ (hs₁.internalHom hs₂).F p ↔ ∀ q, ∀ x ∈ hs₁.F q, f x ∈ hs₂.F (p + q) := by
  refine ⟨fun hf q x hx ↦ hs₁.map_mem_F_of_mem_internalHom_F hs₂ hf hx, fun hf ↦ ?_⟩
  refine (hs₁.internalHom hs₂).mem_of_proj_mem fun r ↦ ?_
  rcases lt_or_ge r p with hrp | hpr
  · have hzero : (hs₁.internalHom hs₂).proj r f = 0 :=
      hs₁.linearMap_ext_of_piece fun a x hx ↦ by
        rw [hs₁.internalHom_proj_apply_apply hs₂ f hx,
          hs₂.proj_eq_zero_of_mem_F_of_lt (hf a x (hs₁.piece_le_F a hx)) (by omega),
          LinearMap.zero_apply]
    rw [hzero]
    exact Submodule.zero_mem _
  · exact ((hs₁.internalHom hs₂).piece_le_F r).trans ((hs₁.internalHom hs₂).F_antitone hpr)
      ((hs₁.internalHom hs₂).proj_mem r f)

section Contraction

variable [FiniteDimensional ℂ W₁]

/-- **The tensor presentation of the internal hom.** Over a finite-dimensional source, the
degree-`p` internal-hom component is the pullback of the degree-`p` component of the tensor
product `V^* ⊗ W` along Mathlib's contraction equivalence.

The two families decompose the same space, so it is enough that a tensor of degree `p` acts as a
map shifting Hodge degree by `p`. -/
theorem internalHom_piece_eq_comap (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.internalHom hs₂).piece p =
      ((hs₁.dual.tensorProduct hs₂).piece p).comap
        (dualTensorHomEquiv ℂ W₁ W₂).symm.toLinearMap := by
  have hpiece : ∀ q, ((hs₁.dual.tensorProduct hs₂).comap (dualTensorHomEquiv ℂ W₁ W₂).symm
      (ω₁.dualTensorHomEquiv_symm_map_internalHom_conj ω₂)).piece q ≤
        (hs₁.internalHom hs₂).piece q := by
    intro q f hf
    rw [comap_piece, Submodule.mem_comap, LinearEquiv.coe_coe] at hf
    rw [internalHom_piece, mem_internalHomPiece_iff]
    intro a x hx
    -- A tensor of total degree `q` sends the degree-`a` component into the degree-`a + q` one.
    have hle : (hs₁.dual.tensorProduct hs₂).piece q ≤
        (hs₂.piece (a + q)).comap ((LinearMap.applyₗ (R := ℂ) x) ∘ₗ dualTensorHom ℂ W₁ W₂) := by
      rw [tensorProduct_piece_eq_iSup]
      refine iSup_le fun r ↦ Submodule.map₂_le.mpr fun φ hφ y hy ↦ ?_
      simp only [Submodule.mem_comap, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
        dualTensorHom_apply, TensorProduct.mk_apply]
      by_cases har : a = -r
      · have hidx : a + q = q - r := by omega
        rw [hidx]
        exact Submodule.smul_mem _ _ hy
      · rw [hs₁.apply_eq_zero_of_mem_piece_of_ne hx hφ har, zero_smul]
        exact Submodule.zero_mem _
    have he : dualTensorHom ℂ W₁ W₂ ((dualTensorHomEquiv ℂ W₁ W₂).symm f) = f :=
      (dualTensorHomEquiv ℂ W₁ W₂).apply_symm_apply f
    have hmem := hle hf
    rw [Submodule.mem_comap, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, he] at hmem
    exact hmem
  rw [← piece_eq_of_piece_le hpiece p, comap_piece]

/-- In the tensor presentation, the internal-hom filtration is the pullback of the tensor-product
filtration on `V^* ⊗ W`. -/
theorem internalHom_F_eq_comap (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.internalHom hs₂).F p =
      ((hs₁.dual.tensorProduct hs₂).F p).comap
        (dualTensorHomEquiv ℂ W₁ W₂).symm.toLinearMap := by
  rw [(hs₁.internalHom hs₂).F_eq_iSup_piece p, (hs₁.dual.tensorProduct hs₂).F_eq_iSup_piece p,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm, Submodule.map_iSup]
  refine iSup_congr fun q ↦ ?_
  rw [Submodule.map_iSup]
  refine iSup_congr fun _ ↦ ?_
  rw [hs₁.internalHom_piece_eq_comap hs₂ q, Submodule.comap_equiv_eq_map_symm,
    LinearEquiv.symm_symm]

end Contraction

end HodgeStructureOn

end TauCeti.Hodge
