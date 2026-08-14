/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib

/-!
# Pure Hodge Structures and the Hodge Decomposition

This module defines pure Hodge structures of weight `n` and proves the fundamental
Hodge decomposition theorem (the L0 milestone of the `HodgeStructures` roadmap).

## Main Definitions

* `TauCeti.Geometry.Hodge.Complexification`: The canonical complexification `ℂ ⊗[ℤ] V` of an
  integral lattice `V`.
* `TauCeti.Geometry.Hodge.Conjugation`: Structure packaging a conjugate-linear automorphism
  whose square is the identity.
* `TauCeti.Geometry.Hodge.concreteLatticeConj`: The canonical conjugate-linear involution on
  `ℂ ⊗[ℤ] V`.
* `TauCeti.Geometry.Hodge.latticeConj`: The abstract conjugate-linear involution on a `ℂ`-vector
  space `Vℂ` exhibiting base change `IsBaseChange ℂ ιℂ`.
* `TauCeti.Geometry.Hodge.HodgeStructureOn`: Pure Hodge structure of weight `n` on a complex
  vector space `W` equipped with a conjugation `ω`.
* `TauCeti.Geometry.Hodge.HodgeStructure`: Pure Hodge structure on the
  complexification of an integral lattice `V`.
* `TauCeti.Geometry.Hodge.HodgeStructureOn.piece`: The `(p, q)`-piece
  $H^{p,q} = F^p \cap \overline{F^{n-p}}$.
* `TauCeti.Geometry.Hodge.HodgeStructureOn.IsEffective`: Predicate stating that the Hodge numbers
  are supported in $[0, n]$.
* `TauCeti.Geometry.Hodge.tate`: The Tate Hodge structure $\mathbb{Z}(m)$ of weight $-2m$.

## Main Theorems

* `TauCeti.Geometry.Hodge.HodgeStructureOn.isInternal_piece`: **(L0 Milestone)** The `(p, q)`-pieces
  of a pure Hodge structure form an internal direct sum $W = \bigoplus_p H^{p,q}$.
* `TauCeti.Geometry.Hodge.HodgeStructureOn.isEffective_iff_piece_eq_bot`: Characterization of
  effective Hodge structures in terms of their vanishing pieces outside $[0, n]$.
* `TauCeti.Geometry.Hodge.latticeConj_unique`: Uniqueness of the lattice-induced conjugation.
* `TauCeti.Geometry.Hodge.concreteLatticeConj_eq_latticeConj`: Identification of the concrete
  and abstract lattice conjugations on `ℂ ⊗[ℤ] V`.

## References

* Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Section 6.
* Deligne, *Théorie de Hodge II*, Section 1.2.1.
-/

namespace TauCeti.Geometry.Hodge

public section

open Complex

/-- The canonical complexification `ℂ ⊗[ℤ] V` of an integral lattice `V`. -/
abbrev Complexification (V : Type*) [AddCommGroup V] [Module ℤ V] : Type _ :=
  TensorProduct ℤ ℂ V

variable {V : Type*} [AddCommGroup V] [Module ℤ V]

/-- A conjugation on a `ℂ`-vector space `W`: a conjugate-linear automorphism
whose square is the identity. -/
structure Conjugation (W : Type*) [AddCommGroup W] [Module ℂ W] where
  /-- The underlying conjugate-linear equivalence. -/
  toEquiv : W ≃ₛₗ[starRingEnd ℂ] W
  involutive : Function.Involutive toEquiv

namespace Conjugation

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (ω : Conjugation W)

/-- The image of `⊤` under a conjugation automorphism is `⊤`. -/
theorem map_top : (⊤ : Submodule ℂ W).map ω.toEquiv.toLinearMap = ⊤ := by
  rw [Submodule.map_top]
  exact LinearEquiv.range _

@[simp]
theorem map_map (p : Submodule ℂ W) :
    (p.map ω.toEquiv.toLinearMap).map ω.toEquiv.toLinearMap = p := by
  ext x
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have h : (ω.toEquiv.toLinearMap (ω.toEquiv.toLinearMap z) : W) = z := ω.involutive z
    rw [h]
    exact hz
  · intro hx
    exact ⟨ω.toEquiv x, ⟨x, hx, rfl⟩, ω.involutive x⟩

end Conjugation

/-- The underlying `ℤ`-linear map for lattice-induced complex conjugation on
`ℂ ⊗[ℤ] V`. -/
def concreteLatticeConjIntLinear : Complexification V →ₗ[ℤ] Complexification V :=
  TensorProduct.map (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap (LinearMap.id : V →ₗ[ℤ] V)

/-- Lattice-induced complex conjugation on `ℂ ⊗[ℤ] V`. On pure tensors it is
`z ⊗ v ↦ z̄ ⊗ v`. -/
def concreteLatticeConj : Complexification V →ₛₗ[starRingEnd ℂ] Complexification V where
  toFun := concreteLatticeConjIntLinear
  map_add' := concreteLatticeConjIntLinear.map_add
  map_smul' c x := by
    change concreteLatticeConjIntLinear (c • x) =
      (starRingEnd ℂ) c • concreteLatticeConjIntLinear x
    refine TensorProduct.induction_on x ?hz ?ht ?ha
    · rw [smul_zero, map_zero, smul_zero]
    · intro z v
      change (TensorProduct.map (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap
          (LinearMap.id : V →ₗ[ℤ] V)) (c • (z ⊗ₜ[ℤ] v : Complexification V)) =
        (starRingEnd ℂ) c •
          (TensorProduct.map (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap
            (LinearMap.id : V →ₗ[ℤ] V)) (z ⊗ₜ[ℤ] v)
      rw [TensorProduct.smul_tmul']
      rw [TensorProduct.map_tmul]
      rw [TensorProduct.map_tmul]
      simp only [LinearMap.id_coe, id_eq]
      rw [Algebra.smul_def]
      change (starRingEnd ℂ) (c * z) ⊗ₜ[ℤ] v =
        (starRingEnd ℂ) c • ((starRingEnd ℂ) z ⊗ₜ[ℤ] v : Complexification V)
      rw [map_mul]
      rw [TensorProduct.smul_tmul']
      rw [Algebra.smul_def]
      rfl
    · intro x y hx hy
      calc
        concreteLatticeConjIntLinear (c • (x + y)) =
            concreteLatticeConjIntLinear (c • x + c • y) := by
          rw [smul_add]
        _ = concreteLatticeConjIntLinear (c • x) + concreteLatticeConjIntLinear (c • y) := by
          rw [map_add]
        _ = (starRingEnd ℂ) c • concreteLatticeConjIntLinear x +
            (starRingEnd ℂ) c • concreteLatticeConjIntLinear y := by
          rw [hx, hy]
        _ = (starRingEnd ℂ) c •
            (concreteLatticeConjIntLinear x + concreteLatticeConjIntLinear y) := by
          rw [smul_add]
        _ = (starRingEnd ℂ) c • concreteLatticeConjIntLinear (x + y) := by
          rw [map_add]

theorem concreteLatticeConj_tmul (z : ℂ) (v : V) :
    concreteLatticeConj (V := V) (z ⊗ₜ[ℤ] v) = (starRingEnd ℂ z) ⊗ₜ[ℤ] v :=
  TensorProduct.map_tmul _ _ z v

theorem concreteLatticeConjIntLinear_comp_self :
    (concreteLatticeConjIntLinear (V := V)).comp concreteLatticeConjIntLinear = LinearMap.id := by
  change (TensorProduct.map (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap
      (LinearMap.id : V →ₗ[ℤ] V)).comp
    (TensorProduct.map (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap
      (LinearMap.id : V →ₗ[ℤ] V)) = LinearMap.id
  rw [← TensorProduct.map_comp]
  have h_conj : (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap.comp
      (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap = LinearMap.id := by
    ext z
    simp
  have h_id : (LinearMap.id : V →ₗ[ℤ] V).comp LinearMap.id = LinearMap.id := LinearMap.id_comp _
  rw [h_conj, h_id, TensorProduct.map_id]

theorem concreteLatticeConj_involutive :
    Function.Involutive (concreteLatticeConj (V := V)) := by
  intro x
  change ((concreteLatticeConjIntLinear (V := V)).comp concreteLatticeConjIntLinear) x = x
  rw [concreteLatticeConjIntLinear_comp_self, LinearMap.id_apply]

variable {Vℂ : Type*} [AddCommGroup Vℂ] [Module ℂ Vℂ]
  {ιℂ : V →ₗ[ℤ] Vℂ}
variable {hℂ : IsBaseChange ℂ ιℂ}

/-- Abstract lattice-induced conjugation, transported from the canonical tensor model through
an `IsBaseChange` equivalence. -/
noncomputable def latticeConj (hℂ : IsBaseChange ℂ ιℂ) :
    Vℂ →ₛₗ[starRingEnd ℂ] Vℂ where
  toFun x := hℂ.equiv (concreteLatticeConj (hℂ.equiv.symm x))
  map_add' x y := by
    rw [map_add, map_add, map_add]
  map_smul' c x := by
    have h_symm : hℂ.equiv.symm (c • x) = c • hℂ.equiv.symm x := map_smul _ _ _
    rw [h_symm]
    have h_conj : concreteLatticeConj (c • hℂ.equiv.symm x) =
        (starRingEnd ℂ c) • concreteLatticeConj (hℂ.equiv.symm x) :=
      concreteLatticeConj.map_smulₛₗ c _
    rw [h_conj]
    exact map_smul _ _ _

theorem latticeConj_ι (hℂ : IsBaseChange ℂ ιℂ) (v : V) :
    latticeConj hℂ (ιℂ v) = ιℂ v := by
  have hιv : hℂ.equiv.symm (ιℂ v) = (1 : ℂ) ⊗ₜ[ℤ] v := by
    apply hℂ.equiv.injective
    rw [LinearEquiv.apply_symm_apply]
    have h_eq := hℂ.equiv_tmul 1 v
    rw [one_smul] at h_eq
    exact h_eq.symm
  change hℂ.equiv (concreteLatticeConj (hℂ.equiv.symm (ιℂ v))) = ιℂ v
  rw [hιv, concreteLatticeConj_tmul, map_one]
  have h_eq := hℂ.equiv_tmul 1 v
  rw [one_smul] at h_eq
  exact h_eq

theorem latticeConj_involutive (hℂ : IsBaseChange ℂ ιℂ) :
    Function.Involutive (latticeConj hℂ) := by
  intro x
  change hℂ.equiv
    (concreteLatticeConj
      (hℂ.equiv.symm (hℂ.equiv (concreteLatticeConj (hℂ.equiv.symm x))))) = x
  rw [LinearEquiv.symm_apply_apply]
  rw [concreteLatticeConj_involutive]
  exact hℂ.equiv.apply_symm_apply x

/-- Abstract conjugation equivalence on `Vℂ`. -/
noncomputable def latticeConjEquiv (hℂ : IsBaseChange ℂ ιℂ) :
    Vℂ ≃ₛₗ[starRingEnd ℂ] Vℂ :=
  { latticeConj hℂ with
    invFun := latticeConj hℂ
    left_inv := latticeConj_involutive hℂ
    right_inv := latticeConj_involutive hℂ }

/-- Abstract conjugation structure on `Vℂ`. -/
noncomputable def latticeConjugation (hℂ : IsBaseChange ℂ ιℂ) : Conjugation Vℂ where
  toEquiv := latticeConjEquiv hℂ
  involutive := latticeConj_involutive hℂ

/-- Companion uniqueness theorem: any conjugate-linear endomorphism fixing `ιℂ V` is
identically equal to `latticeConj hℂ`. -/
theorem latticeConj_unique (f : Vℂ →ₛₗ[starRingEnd ℂ] Vℂ)
    (hf : ∀ v, f (ιℂ v) = ιℂ v) : f = latticeConj hℂ := by
  ext x
  have h_eq : x = hℂ.equiv (hℂ.equiv.symm x) := (hℂ.equiv.apply_symm_apply x).symm
  rw [h_eq]
  generalize hℂ.equiv.symm x = y
  refine TensorProduct.induction_on y ?hz ?ht ?ha
  · simp
  · intro z v
    have hz_smul : (z ⊗ₜ[ℤ] v : Complexification V) = z • ((1 : ℂ) ⊗ₜ[ℤ] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h_one : hℂ.equiv ((1 : ℂ) ⊗ₜ[ℤ] v) = ιℂ v := by
      have h_eq' := hℂ.equiv_tmul 1 v
      rw [one_smul] at h_eq'
      exact h_eq'
    have h_smul : hℂ.equiv (z ⊗ₜ[ℤ] v) = z • ιℂ v := by
      rw [hz_smul, LinearEquiv.map_smul, h_one]
    have h1 : f (hℂ.equiv (z ⊗ₜ[ℤ] v)) = (starRingEnd ℂ z) • ιℂ v := by
      rw [h_smul, f.map_smulₛₗ, hf v]
    have h2 : (latticeConj hℂ) (hℂ.equiv (z ⊗ₜ[ℤ] v)) = (starRingEnd ℂ z) • ιℂ v := by
      rw [h_smul, (latticeConj hℂ).map_smulₛₗ, latticeConj_ι]
    rw [h1, h2]
  · intro u w hu hw
    simp only [map_add] at hu hw ⊢
    rw [hu, hw]

/-- The concrete conjugation on `ℂ ⊗[ℤ] V` agrees with the abstract base-change conjugation. -/
theorem concreteLatticeConj_eq_latticeConj :
    concreteLatticeConj (V := V) = latticeConj (TensorProduct.isBaseChange ℤ V ℂ) :=
  latticeConj_unique (hℂ := TensorProduct.isBaseChange ℤ V ℂ) concreteLatticeConj (fun v => by
    change concreteLatticeConj ((1 : ℂ) ⊗ₜ[ℤ] v) = (1 : ℂ) ⊗ₜ[ℤ] v
    rw [concreteLatticeConj_tmul, map_one])

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Pure Hodge structure of weight `n` on a complex vector space `W` equipped with a
conjugation `ω`. The primary datum is a decreasing, bounded filtration `F` which is
`n`-opposed: `F^p ⊕ ω(F^{n+1-p}) = W`. -/
structure HodgeStructureOn (W : Type*) [AddCommGroup W] [Module ℂ W]
    (ω : Conjugation W) (n : ℤ) where
  /-- The decreasing Hodge filtration. -/
  F : ℤ → Submodule ℂ W
  F_antitone : Antitone F
  F_top : ∃ p, F p = ⊤
  F_bot : ∃ p, F p = ⊥
  opposed : ∀ p, IsCompl (F p) ((F (n + 1 - p)).map ω.toEquiv.toLinearMap)

/-- Pure Hodge structure of weight `n` on the complexification `Vℂ` of an integral lattice `V`. -/
structure HodgeStructure (hℂ : IsBaseChange ℂ ιℂ) (n : ℤ)
    extends HodgeStructureOn Vℂ (latticeConjugation hℂ) n where
  /-- The underlying lattice is a free `ℤ`-module. -/
  free : Module.Free ℤ V := by infer_instance
  /-- The underlying lattice is a finitely generated `ℤ`-module. -/
  finite : Module.Finite ℤ V := by infer_instance

namespace HodgeStructureOn

variable (ω : Conjugation W) {n : ℤ} (hs : HodgeStructureOn W ω n)

/-- The `(p, q)`-piece $H^{p,q} = F^p \cap \overline{F^{n-p}}$ of a pure Hodge structure. -/
noncomputable def piece (p : ℤ) : Submodule ℂ W :=
  hs.F p ⊓ (hs.F (n - p)).map ω.toEquiv.toLinearMap

/-- A weight-`n` Hodge structure is **effective** when its Hodge numbers are supported in
`[0, n]`. -/
def IsEffective : Prop :=
  hs.F 0 = ⊤ ∧ hs.F (n + 1) = ⊥

theorem piece_le_F (p : ℤ) : hs.piece ω p ≤ hs.F p :=
  inf_le_left

theorem piece_le_conj_F (p : ℤ) :
    hs.piece ω p ≤ (hs.F (n - p)).map ω.toEquiv.toLinearMap :=
  inf_le_right

theorem map_conj_piece (p : ℤ) :
    (hs.piece ω p).map ω.toEquiv.toLinearMap = hs.piece ω (n - p) := by
  dsimp [piece]
  rw [Submodule.map_inf _ ω.toEquiv.injective, ω.map_map, inf_comm]
  have h_sub : n - (n - p) = p := by ring
  rw [h_sub]

/-- Opposition shifted by one: `F^{p+1}` is complementary to `ω(F^{n-p})`. -/
theorem opposed_add_one (p : ℤ) :
    IsCompl (hs.F (p + 1)) ((hs.F (n - p)).map ω.toEquiv.toLinearMap) := by
  have h_sub : n + 1 - (p + 1) = n - p := by ring
  rw [← h_sub]
  exact hs.opposed (p + 1)

theorem F_eq_F_add_one_sup_piece (p : ℤ) :
    hs.F p = hs.F (p + 1) ⊔ hs.piece ω p := by
  have h_opp := hs.opposed_add_one ω p
  have h_le : hs.F (p + 1) ≤ hs.F p := hs.F_antitone (by omega)
  have h_mod := sup_inf_assoc_of_le ((hs.F (n - p)).map ω.toEquiv.toLinearMap) h_le
  rw [h_opp.codisjoint.eq_top, top_inf_eq, inf_comm] at h_mod
  exact h_mod

theorem F_le_iSup_piece (p : ℤ) :
    hs.F p ≤ ⨆ q, hs.piece ω q := by
  rcases hs.F_bot with ⟨p_bot, hp_bot⟩
  have h_bot (k : ℤ) (hk : p_bot ≤ k) : hs.F k = ⊥ :=
    le_bot_iff.mp (hp_bot ▸ hs.F_antitone hk)
  by_cases hp : p_bot ≤ p
  · rw [h_bot p hp]
    exact bot_le
  · have hp_le : p ≤ p_bot := le_of_not_ge hp
    refine Int.leInductionDown (motive := fun n _ => hs.F n ≤ ⨆ q, hs.piece ω q) ?base ?pred p hp_le
    · rw [hp_bot]
      exact bot_le
    · intro k _ ih
      rw [hs.F_eq_F_add_one_sup_piece ω (k - 1)]
      have : k - 1 + 1 = k := by ring
      rw [this]
      exact sup_le ih (le_iSup (hs.piece ω) (k - 1))

theorem iSup_piece_eq_top : ⨆ q, hs.piece ω q = ⊤ := by
  rcases hs.F_top with ⟨p_top, hp_top⟩
  refine top_unique ?_
  rw [← hp_top]
  exact hs.F_le_iSup_piece ω p_top

theorem iSupIndep_piece : iSupIndep (hs.piece ω) := by
  intro p
  rw [disjoint_iff]
  have h_le_sup : (⨆ (q) (_ : q ≠ p), hs.piece ω q) ≤
      hs.F (p + 1) ⊔ (hs.F (n + 1 - p)).map ω.toEquiv.toLinearMap := by
    refine iSup₂_le ?_
    intro q hqp
    rcases lt_or_gt_of_ne hqp with hqp_lt | hqp_gt
    · have h1 : hs.piece ω q ≤ (hs.F (n - q)).map ω.toEquiv.toLinearMap := inf_le_right
      have h2 : n + 1 - p ≤ n - q := by linarith
      have h3 : hs.F (n - q) ≤ hs.F (n + 1 - p) := hs.F_antitone h2
      have h4 : (hs.F (n - q)).map ω.toEquiv.toLinearMap ≤
          (hs.F (n + 1 - p)).map ω.toEquiv.toLinearMap := Submodule.map_mono h3
      exact le_trans (le_trans h1 h4) le_sup_right
    · have h1 : hs.piece ω q ≤ hs.F q := inf_le_left
      have h2 : p + 1 ≤ q := by linarith
      have h3 : hs.F q ≤ hs.F (p + 1) := hs.F_antitone h2
      exact le_trans (le_trans h1 h3) le_sup_left
  have h_disj :
      hs.piece ω p ⊓
          (hs.F (p + 1) ⊔ (hs.F (n + 1 - p)).map ω.toEquiv.toLinearMap) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx_piece, hx_sup⟩
    rcases (Submodule.mem_sup).mp hx_sup with ⟨a, ha, b, hb, rfl⟩
    have hx_Fp : a + b ∈ hs.F p := hx_piece.1
    have ha_Fp : a ∈ hs.F p := hs.F_antitone (by omega) ha
    have hb_Fp : b ∈ hs.F p := by
      have : b = (a + b) - a := by abel
      rw [this]
      exact Submodule.sub_mem _ hx_Fp ha_Fp
    have hb_disj : b ∈ hs.F p ⊓ (hs.F (n + 1 - p)).map ω.toEquiv.toLinearMap := ⟨hb_Fp, hb⟩
    have h_opp_p := (hs.opposed p).disjoint.eq_bot
    have hb_zero : b = 0 := by rw [h_opp_p] at hb_disj; exact hb_disj
    subst hb_zero
    rw [add_zero] at hx_piece ⊢
    have ha_conj : a ∈ (hs.F (n - p)).map ω.toEquiv.toLinearMap := hx_piece.2
    have ha_disj : a ∈ hs.F (p + 1) ⊓ (hs.F (n - p)).map ω.toEquiv.toLinearMap := ⟨ha, ha_conj⟩
    have h_opp_p1 := hs.opposed_add_one ω p
    have h_opp_p1_disj := h_opp_p1.disjoint.eq_bot
    rw [h_opp_p1_disj] at ha_disj
    exact ha_disj
  exact le_bot_iff.mp (le_trans (inf_le_inf_left _ h_le_sup) (le_of_eq h_disj))

/-- **L0 milestone -- the Hodge decomposition.** The `(p, q)`-pieces of a pure Hodge structure
give an internal direct sum $W = \bigoplus_p H^{p,q}$. -/
theorem isInternal_piece : DirectSum.IsInternal (hs.piece ω) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨hs.iSupIndep_piece ω, hs.iSup_piece_eq_top ω⟩

theorem piece_eq_bot_of_lt_zero (h : hs.IsEffective) {p : ℤ} (hp : p < 0) :
    hs.piece ω p = ⊥ := by
  dsimp [piece]
  have hp' : n + 1 ≤ n - p := by omega
  have hF : hs.F (n - p) = ⊥ := le_bot_iff.mp (h.2 ▸ hs.F_antitone hp')
  rw [hF, Submodule.map_bot, inf_bot_eq]

theorem piece_eq_bot_of_gt_weight (h : hs.IsEffective) {p : ℤ} (hp : n < p) :
    hs.piece ω p = ⊥ := by
  dsimp [piece]
  have hp' : n + 1 ≤ p := by omega
  have hF : hs.F p = ⊥ := le_bot_iff.mp (h.2 ▸ hs.F_antitone hp')
  rw [hF, bot_inf_eq]

theorem piece_eq_bot_of_not_mem_interval (h : hs.IsEffective) {p : ℤ}
    (hp : p < 0 ∨ n < p) : hs.piece ω p = ⊥ := by
  rcases hp with hp_lt | hp_gt
  · exact hs.piece_eq_bot_of_lt_zero ω h hp_lt
  · exact hs.piece_eq_bot_of_gt_weight ω h hp_gt

/-- Characterization of effective Hodge structures in terms of vanishing pieces outside `[0, n]`. -/
theorem isEffective_iff_piece_eq_bot :
    hs.IsEffective ↔ ∀ p : ℤ, p < 0 ∨ n < p → hs.piece ω p = ⊥ := by
  constructor
  · intro h p hp
    exact hs.piece_eq_bot_of_not_mem_interval ω h hp
  · intro hp_bot
    have h_bot : hs.F (n + 1) = ⊥ := by
      rcases hs.F_bot with ⟨p_bot, hp_bot'⟩
      by_cases hp_le : p_bot ≤ n + 1
      · exact le_bot_iff.mp (hp_bot' ▸ hs.F_antitone hp_le)
      · have hle : n + 1 ≤ p_bot := le_of_not_ge hp_le
        refine (Int.leInductionDown (motive := fun k _ => n + 1 ≤ k → hs.F k = ⊥)
          ?base ?pred (n + 1) hle) le_rfl
        · intro _
          exact hp_bot'
        · intro k _ ih h_le
          have hk : n + 1 ≤ k := by omega
          have hFk : hs.F k = ⊥ := ih hk
          rw [hs.F_eq_F_add_one_sup_piece ω (k - 1)]
          have : k - 1 + 1 = k := by ring
          rw [this, hFk, hp_bot (k - 1) (Or.inr (by omega)), bot_sup_eq]
    have h_top : hs.F 0 = ⊤ := by
      have h_opp := hs.opposed 0
      have h_sub : n + 1 - 0 = n + 1 := by ring
      rw [h_sub, h_bot, Submodule.map_bot] at h_opp
      exact eq_top_of_isCompl_bot h_opp
    exact ⟨h_top, h_bot⟩

end HodgeStructureOn

/-- The Tate Hodge structure $\mathbb{Z}(m)$ of weight $-2m$ on $V = \mathbb{Z}$. -/
def tate (m : ℤ) : HodgeStructure (TensorProduct.isBaseChange ℤ ℤ ℂ) (-2 * m) where
  F p := if p ≤ -m then ⊤ else ⊥
  F_antitone := by
    intro p q hpq
    dsimp
    split_ifs with h1 h2 h3
    · exact le_rfl
    · exfalso; linarith
    · exact bot_le
    · exact le_rfl
  F_top := ⟨-m, by exact ite_eq_left (by linarith)⟩
  F_bot := ⟨-m + 1, by exact ite_eq_right (by linarith)⟩
  opposed p := by
    have h_eval : -2 * m + 1 - p = 1 - 2 * m - p := by ring
    rw [h_eval]
    by_cases hp : p ≤ -m
    · have h1 :
          (if p ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) = ⊤ := by
        exact ite_eq_left hp
      have h2 :
          (if 1 - 2 * m - p ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) =
            ⊥ := by
        exact ite_eq_right (by linarith)
      rw [h1, h2, Submodule.map_bot]
      exact isCompl_top_bot
    · have h1 :
          (if p ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) = ⊥ := by
        exact ite_eq_right hp
      have h2 :
          (if 1 - 2 * m - p ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) =
            ⊤ := by
        exact ite_eq_left (by linarith)
      rw [h1, h2, Conjugation.map_top]
      exact isCompl_bot_top

theorem tate_piece_apply (m : ℤ) (p : ℤ) :
    (tate m).piece (latticeConjugation (TensorProduct.isBaseChange ℤ ℤ ℂ)) p =
      if p = -m then ⊤ else ⊥ := by
  dsimp [HodgeStructureOn.piece, tate]
  by_cases hp : p = -m
  · subst hp
    have h1 :
        (if -m ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) = ⊤ := by
      exact ite_eq_left (by linarith)
    have h_other : -2 * m - -m = -m := by ring
    rw [h1]
    have h2 : (if -2 * m - -m ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) = ⊤ := by
      rw [h_other]
      exact ite_eq_left (by linarith)
    rw [h2, Conjugation.map_top, inf_top_eq]
    split_ifs with h_cond
    · rfl
    · exfalso; exact h_cond rfl
  · rw [ite_eq_right hp]
    rcases lt_or_gt_of_ne hp with hp_lt | hp_gt
    · have h1 :
          (if p ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) = ⊤ := by
        exact ite_eq_left (by linarith)
      have h2_cond : ¬ (-2 * m - p ≤ -m) := by linarith
      have h2 :
          (if -2 * m - p ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) =
            ⊥ := by
        exact ite_eq_right h2_cond
      rw [h1, h2, Submodule.map_bot, inf_bot_eq]
    · have hp_not_le : ¬ p ≤ -m := by linarith
      have h1 :
          (if p ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) = ⊥ := by
        exact ite_eq_right hp_not_le
      rw [h1, bot_inf_eq]

/-- The Tate structure `ℤ(0)` is effective (weight 0). -/
theorem isEffective_tate_zero : (tate 0).IsEffective := by
  dsimp [HodgeStructureOn.IsEffective, tate]
  exact ⟨rfl, rfl⟩

end

end TauCeti.Geometry.Hodge
