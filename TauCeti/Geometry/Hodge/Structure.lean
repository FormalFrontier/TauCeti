/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Order.ModularLattice
public import Mathlib.Order.Monotone.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import TauCeti.Geometry.Hodge.Conjugation
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Pure Hodge Structures and the Hodge Decomposition

This module defines pure Hodge structures of weight `n` and proves the fundamental
Hodge decomposition theorem (the L0 milestone of the `HodgeStructures` roadmap).

For any pure Hodge structure (i.e. a bounded antitone `n`-opposed filtration on a complex vector
space equipped with a conjugation), the Hodge pieces form an internal direct sum
`W = ⨁_p H^{p, n-p}`. Producing such filtrations from geometry (e.g. on compact Kähler manifolds)
is outside the scope of this module.

## Main Definitions

* `TauCeti.Geometry.Hodge.HodgeStructureOn`: Pure Hodge structure of weight `n` on a complex
  vector space `W` equipped with a conjugation `ω`.
* `TauCeti.Geometry.Hodge.HodgeStructure`: Pure Hodge structure on the
  complexification of a `ℤ`-module `V` (an abbreviation for `HodgeStructureOn`).
* `TauCeti.Geometry.Hodge.HodgeStructureOn.piece`: The `(p, q)`-piece
  $H^{p,q} = F^p \cap \overline{F^{n-p}}$ with $q := n - p$.
* `TauCeti.Geometry.Hodge.HodgeStructureOn.IsEffective`: Predicate stating that $F^{n+1} = 0$,
  so that the Hodge numbers are supported in $[0, n]$.
* `TauCeti.Geometry.Hodge.HodgeStructureOn.twist`: The Tate twist $W(m)$ of a pure Hodge structure.
* `TauCeti.Geometry.Hodge.HodgeStructureOn.Hom`: Morphisms of pure Hodge structures at the
  conjugation/real level (preserving filtration and commuting with conjugation).
* `TauCeti.Geometry.Hodge.tate`: The Tate Hodge structure $\mathbb{Z}(m)$ of weight $-2m$.

## Main Theorems

* `TauCeti.Geometry.Hodge.HodgeStructureOn.isInternal_piece`: **(L0 Milestone)** The `(p, q)`-pieces
  of a pure Hodge structure form an internal direct sum $W = \bigoplus_p H^{p, n-p}$.
* `TauCeti.Geometry.Hodge.HodgeStructureOn.map_conj_piece`: Conjugation symmetry of the Hodge
  pieces $\overline{H^{p,q}} = H^{n-p, p}$.
* `TauCeti.Geometry.Hodge.HodgeStructureOn.isEffective_iff_piece_eq_bot`: Characterization of
  effective Hodge structures in terms of their vanishing pieces outside $[0, n]$.
* `TauCeti.Geometry.Hodge.isEffective_tate_iff`: Classification of effective Tate structures
  $(\mathbb{Z}(m)\text{ is effective} \leftrightarrow m \le 0)$.
* `TauCeti.Geometry.Hodge.tate_piece_apply`: Explicit description of the Hodge pieces of
  $\mathbb{Z}(m)$.

## References

* Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Section 6.
* Deligne, *Théorie de Hodge II*, Section 1.2.1.
* Smith, Booker, `pure-hodge-structures-lean4` (prior L0 formalization in Lean 4).
* The `IsBaseChange` complexification interface and the `opposed`/Deligne §1.2.1 naming follow
  the Mathlib Zulip discussion cited by the `HodgeStructures` roadmap.
-/

namespace TauCeti.Geometry.Hodge

variable {V : Type*} [AddCommGroup V]
variable {Vℂ : Type*} [AddCommGroup Vℂ] [Module ℂ Vℂ]
  {ιℂ : V →ₗ[ℤ] Vℂ}

/-- Pure Hodge structure of weight `n` on a complex vector space `W` equipped with a
conjugation `ω`. The primary datum is a decreasing, bounded filtration `F` which is
`n`-opposed: `F^p ⊕ ω(F^{n+1-p}) = W`. -/
@[ext]
public structure HodgeStructureOn (W : Type*) [AddCommGroup W] [Module ℂ W]
    (ω : Conjugation W) (n : ℤ) where
  /-- The decreasing Hodge filtration. -/
  F : ℤ → Submodule ℂ W
  F_antitone : Antitone F
  F_bot : ∃ p, F p = ⊥
  opposed : ∀ p, IsCompl (F p) ((F (n + 1 - p)).map ω.toEquiv.toLinearMap)

/-- Pure Hodge structure of weight `n` on the complexification `Vℂ` of a `ℤ`-module `V`.
This is an abbreviation for `HodgeStructureOn Vℂ (latticeConjugation hℂ) n`. -/
public abbrev HodgeStructure (hℂ : IsBaseChange ℂ ιℂ) (n : ℤ) : Type _ :=
  HodgeStructureOn Vℂ (latticeConjugation hℂ) n

namespace HodgeStructureOn

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {ω : Conjugation W} {n : ℤ}
  (hs : HodgeStructureOn W ω n)

/-- The Hodge filtration reaches `⊤` for sufficiently negative indices. -/
public theorem F_top : ∃ p, hs.F p = ⊤ := by
  rcases hs.F_bot with ⟨q, hq⟩
  refine ⟨n + 1 - q, ?_⟩
  have h_opp := hs.opposed (n + 1 - q)
  have h_sub : n + 1 - (n + 1 - q) = q := by ring
  rw [h_sub, hq, Submodule.map_bot] at h_opp
  exact eq_top_of_isCompl_bot h_opp

/-- The `(p, q)`-piece $H^{p,q} = F^p \cap \overline{F^{n-p}}$ (with $q := n - p$) of a pure
Hodge structure. -/
@[expose]
public def piece (p : ℤ) : Submodule ℂ W :=
  hs.F p ⊓ (hs.F (n - p)).map ω.toEquiv.toLinearMap

/-- Definitional restatement of the `(p, q)`-piece of a pure Hodge structure. -/
public theorem piece_def (p : ℤ) :
    hs.piece p = hs.F p ⊓ (hs.F (n - p)).map ω.toEquiv.toLinearMap := rfl

/-- Membership in the `(p, q)`-piece $H^{p,q} = F^p \cap \overline{F^{n-p}}$ (with $q := n - p$)
is characterized by membership in both filtration submodules. -/
@[simp]
public theorem mem_piece_iff (p : ℤ) (x : W) :
    x ∈ hs.piece p ↔ x ∈ hs.F p ∧ x ∈ (hs.F (n - p)).map ω.toEquiv.toLinearMap :=
  Submodule.mem_inf

/-- The `(p, q)`-piece is contained in $F^p$. -/
public theorem piece_le_F (p : ℤ) : hs.piece p ≤ hs.F p :=
  inf_le_left

/-- The `(p, q)`-piece is contained in $\overline{F^{n-p}}$. -/
public theorem piece_le_conj_F (p : ℤ) :
    hs.piece p ≤ (hs.F (n - p)).map ω.toEquiv.toLinearMap :=
  inf_le_right

/-- A weight-`n` Hodge structure is **effective** when $F^{n+1} = 0$, so that its Hodge numbers
are supported in $[0, n]$. -/
public def IsEffective : Prop :=
  hs.F (n + 1) = ⊥

/-- Definitional characterization of effectivity. -/
public theorem isEffective_iff : hs.IsEffective ↔ hs.F (n + 1) = ⊥ :=
  Iff.rfl

/-- In an effective Hodge structure, $F^0 = ⊤$. -/
public theorem IsEffective.F_zero_eq_top (h : hs.IsEffective) : hs.F 0 = ⊤ := by
  have h_opp := hs.opposed 0
  have h_sub : n + 1 - 0 = n + 1 := by ring
  rw [h_sub, h, Submodule.map_bot] at h_opp
  exact eq_top_of_isCompl_bot h_opp

/-- A pure Hodge structure is effective if and only if $F^0 = ⊤$. -/
public theorem isEffective_iff_F_zero_eq_top : hs.IsEffective ↔ hs.F 0 = ⊤ := by
  constructor
  · exact IsEffective.F_zero_eq_top hs
  · intro h0
    have h_opp := hs.opposed 0
    have h_sub : n + 1 - 0 = n + 1 := by ring
    rw [h_sub, h0] at h_opp
    have h_bot := eq_bot_of_isCompl_top h_opp.symm
    have h_bot' := congr_arg (Submodule.map ω.toEquiv.toLinearMap) h_bot
    rw [ω.map_map_self, Submodule.map_bot] at h_bot'
    exact h_bot'

/-- Conjugation symmetry of the Hodge pieces: $\overline{H^{p,q}} = H^{n-p, p} = H^{q, p}$. -/
@[simp]
public theorem map_conj_piece (p : ℤ) :
    (hs.piece p).map ω.toEquiv.toLinearMap = hs.piece (n - p) := by
  rw [piece_def, Submodule.map_inf _ ω.toEquiv.injective, ω.map_map_self, inf_comm, piece_def]
  have h_sub : n - (n - p) = p := by ring
  rw [h_sub]

/-- Opposition shifted by one: `F^{p+1}` is complementary to `ω(F^{n-p})`. -/
public theorem opposed_add_one (p : ℤ) :
    IsCompl (hs.F (p + 1)) ((hs.F (n - p)).map ω.toEquiv.toLinearMap) := by
  have h_sub : n + 1 - (p + 1) = n - p := by ring
  rw [← h_sub]
  exact hs.opposed (p + 1)

/-- Inductive step for Hodge filtration: $F^p = F^{p+1} \sqcup H^{p, n-p}$. -/
public theorem F_eq_F_add_one_sup_piece (p : ℤ) :
    hs.F p = hs.F (p + 1) ⊔ hs.piece p := by
  have h_opp := hs.opposed_add_one p
  have h_le : hs.F (p + 1) ≤ hs.F p := hs.F_antitone (by omega)
  have h_mod := sup_inf_assoc_of_le ((hs.F (n - p)).map ω.toEquiv.toLinearMap) h_le
  rw [h_opp.codisjoint.eq_top, top_inf_eq, inf_comm] at h_mod
  exact h_mod

/-- Downward induction helper: if a property holds at `p_bot` and is preserved when going
from `k` to `k - 1` using `F (k-1) = F k ⊔ piece (k-1)`, it holds for all `p ≤ p_bot`. -/
public theorem induction_down_F (P : ℤ → Submodule ℂ W → Prop) (p_bot p : ℤ) (hp : p ≤ p_bot)
    (hp_bot : P p_bot (hs.F p_bot))
    (h_step : ∀ k, p ≤ k - 1 → k ≤ p_bot → P k (hs.F k) → P (k - 1) (hs.F (k - 1))) :
    P p (hs.F p) := by
  have : ∀ n (hn : n ≤ p_bot), p ≤ n → P n (hs.F n) := by
    intro n hn
    refine Int.leInductionDown (motive := fun k _ => p ≤ k → P k (hs.F k)) ?base ?pred n hn
    · intro _
      exact hp_bot
    · intro k hk ih hpk
      exact h_step k (by omega) hk (ih (by omega))
  exact this p hp le_rfl

/-- Every Hodge filtration stage $F^p$ is contained in the span of the Hodge pieces. -/
public theorem F_le_iSup_piece (p : ℤ) :
    hs.F p ≤ ⨆ q, hs.piece q := by
  rcases hs.F_bot with ⟨p_bot, hp_bot⟩
  by_cases hp : p_bot ≤ p
  · have h_bot : hs.F p = ⊥ := le_bot_iff.mp (hp_bot ▸ hs.F_antitone hp)
    rw [h_bot]
    exact bot_le
  · refine hs.induction_down_F (fun _ S => S ≤ ⨆ q, hs.piece q) p_bot p (le_of_not_ge hp) ?_ ?_
    · rw [hp_bot]; exact bot_le
    · intro k _ _ ih
      rw [hs.F_eq_F_add_one_sup_piece (k - 1)]
      have : k - 1 + 1 = k := by ring
      rw [this]
      exact sup_le ih (le_iSup hs.piece (k - 1))

/-- The Hodge pieces span the entire complex vector space: $igoplus_p H^{p, n-p} = W$. -/
public theorem iSup_piece_eq_top : ⨆ q, hs.piece q = ⊤ := by
  rcases hs.F_top with ⟨p_top, hp_top⟩
  refine top_unique ?_
  rw [← hp_top]
  exact hs.F_le_iSup_piece p_top

/-- The sum of all pieces $H^{q, n-q}$ with $q 
e p$ lies in
$F^{p+1} ⊔ \overline{F^{n+1-p}}$. -/
public theorem iSup_ne_piece_le (p : ℤ) :
    (⨆ (q) (_ : q ≠ p), hs.piece q) ≤
      hs.F (p + 1) ⊔ (hs.F (n + 1 - p)).map ω.toEquiv.toLinearMap := by
  refine iSup₂_le ?_
  intro q hqp
  rcases lt_or_gt_of_ne hqp with hqp_lt | hqp_gt
  · have h1 : hs.piece q ≤ (hs.F (n - q)).map ω.toEquiv.toLinearMap := hs.piece_le_conj_F q
    have h2 : n + 1 - p ≤ n - q := by omega
    have h3 : hs.F (n - q) ≤ hs.F (n + 1 - p) := hs.F_antitone h2
    have h4 : (hs.F (n - q)).map ω.toEquiv.toLinearMap ≤
        (hs.F (n + 1 - p)).map ω.toEquiv.toLinearMap := Submodule.map_mono h3
    exact le_trans (le_trans h1 h4) le_sup_right
  · have h1 : hs.piece q ≤ hs.F q := hs.piece_le_F q
    have h2 : p + 1 ≤ q := by omega
    have h3 : hs.F q ≤ hs.F (p + 1) := hs.F_antitone h2
    exact le_trans (le_trans h1 h3) le_sup_left

/-- The Hodge pieces are linearly independent (disjoint submodules). -/
public theorem iSupIndep_piece : iSupIndep hs.piece := by
  intro p
  rw [disjoint_iff]
  -- The span of pieces for q ≠ p lies in F^{p+1} ⊔ ω(F^{n+1-p}), which meets H^{p,n-p} trivially.
  have h_disj :
      hs.piece p ⊓ (hs.F (p + 1) ⊔ (hs.F (n + 1 - p)).map ω.toEquiv.toLinearMap) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx_piece, hx_sup⟩
    rcases (hs.mem_piece_iff p x).mp hx_piece with ⟨hx_Fp, hx_conj⟩
    rcases (Submodule.mem_sup).mp hx_sup with ⟨a, ha, b, hb, rfl⟩
    have ha_Fp : a ∈ hs.F p := hs.F_antitone (by omega) ha
    have hb_Fp : b ∈ hs.F p := by
      have : b = (a + b) - a := by abel
      rw [this]
      exact Submodule.sub_mem _ hx_Fp ha_Fp
    have hb_disj : b ∈ hs.F p ⊓ (hs.F (n + 1 - p)).map ω.toEquiv.toLinearMap :=
      Submodule.mem_inf.mpr ⟨hb_Fp, hb⟩
    have h_opp_p := (hs.opposed p).disjoint.eq_bot
    have hb_zero : b = 0 := by rw [h_opp_p] at hb_disj; exact hb_disj
    subst hb_zero
    rw [add_zero] at hx_conj ⊢
    have ha_disj : a ∈ hs.F (p + 1) ⊓ (hs.F (n - p)).map ω.toEquiv.toLinearMap :=
      Submodule.mem_inf.mpr ⟨ha, hx_conj⟩
    have h_opp_p1 := hs.opposed_add_one p
    have h_opp_p1_disj := h_opp_p1.disjoint.eq_bot
    rw [h_opp_p1_disj] at ha_disj
    exact ha_disj
  exact le_bot_iff.mp (le_trans (inf_le_inf_left _ (hs.iSup_ne_piece_le p)) (le_of_eq h_disj))

/-- **L0 milestone -- the Hodge decomposition.** The `(p, q)`-pieces of a pure Hodge structure
give an internal direct sum $W = igoplus_p H^{p, n-p}$. -/
public theorem isInternal_piece : DirectSum.IsInternal hs.piece := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨hs.iSupIndep_piece, hs.iSup_piece_eq_top⟩

public theorem piece_eq_bot_of_lt_zero (h : hs.IsEffective) {p : ℤ} (hp : p < 0) :
    hs.piece p = ⊥ := by
  rw [piece_def]
  have hp' : n + 1 ≤ n - p := by omega
  have hF : hs.F (n - p) = ⊥ := le_bot_iff.mp (h ▸ hs.F_antitone hp')
  rw [hF, Submodule.map_bot, inf_bot_eq]

public theorem piece_eq_bot_of_gt_weight (h : hs.IsEffective) {p : ℤ} (hp : n < p) :
    hs.piece p = ⊥ := by
  rw [piece_def]
  have hp' : n + 1 ≤ p := by omega
  have hF : hs.F p = ⊥ := le_bot_iff.mp (h ▸ hs.F_antitone hp')
  rw [hF, bot_inf_eq]

/-- Characterization of effective Hodge structures in terms of vanishing pieces outside `[0, n]`. -/
public theorem isEffective_iff_piece_eq_bot :
    hs.IsEffective ↔ ∀ p : ℤ, p < 0 ∨ n < p → hs.piece p = ⊥ := by
  constructor
  · intro h p hp
    rcases hp with hp_lt | hp_gt
    · exact hs.piece_eq_bot_of_lt_zero h hp_lt
    · exact hs.piece_eq_bot_of_gt_weight h hp_gt
  · intro hp_bot
    have h_bot : hs.F (n + 1) = ⊥ := by
      rcases hs.F_bot with ⟨p_bot, hp_bot'⟩
      by_cases hp_le : p_bot ≤ n + 1
      · exact le_bot_iff.mp (hp_bot' ▸ hs.F_antitone hp_le)
      · have hle : n + 1 ≤ p_bot := le_of_not_ge hp_le
        refine hs.induction_down_F (fun _ S => S = ⊥) p_bot (n + 1) hle hp_bot' ?_
        intro k hk _ ih
        rw [hs.F_eq_F_add_one_sup_piece (k - 1)]
        have : k - 1 + 1 = k := by ring
        have hk' : n < k - 1 := by omega
        rw [this, ih, hp_bot (k - 1) (Or.inr hk'), bot_sup_eq]
    exact h_bot

/-- The Tate twist $W(m)$ of a pure Hodge structure of weight $n$ by $m \in \mathbb{Z}$,
yielding a pure Hodge structure of weight $n - 2m$ on the same underlying space and conjugation,
with filtration shifted by $F^p(W(m)) = F^{p+m}(W)$. -/
@[expose]
public def twist (m : ℤ) : HodgeStructureOn W ω (n - 2 * m) where
  F p := hs.F (p + m)
  F_antitone := by
    intro p q hpq
    exact hs.F_antitone (by omega)
  F_bot := by
    rcases hs.F_bot with ⟨p, hp⟩
    exact ⟨p - m, by rw [sub_add_cancel, hp]⟩
  opposed p := by
    have h_eval : n - 2 * m + 1 - p + m = n + 1 - (p + m) := by ring
    have h_opp := hs.opposed (p + m)
    rw [← h_eval] at h_opp
    exact h_opp

@[simp]
public theorem twist_F (m : ℤ) (p : ℤ) :
    (hs.twist m).F p = hs.F (p + m) := rfl

@[simp]
public theorem twist_piece (m : ℤ) (p : ℤ) :
    (hs.twist m).piece p = hs.piece (p + m) := by
  rw [piece_def, twist_F, twist_F, piece_def]
  have h_sub : n - 2 * m - p + m = n - (p + m) := by ring
  rw [h_sub]

end HodgeStructureOn

/-- A morphism of pure Hodge structures at the real/conjugation level: a `ℂ`-linear map
commuting with conjugation and preserving the Hodge filtrations. (For integral or rational
structures, compatibility with the underlying lattice/space is additionally required.) -/
@[ext]
public structure HodgeStructureOn.Hom {W₁ : Type*} [AddCommGroup W₁] [Module ℂ W₁]
    {ω₁ : Conjugation W₁} {W₂ : Type*} [AddCommGroup W₂] [Module ℂ W₂] {ω₂ : Conjugation W₂}
    {n : ℤ} (hs₁ : HodgeStructureOn W₁ ω₁ n) (hs₂ : HodgeStructureOn W₂ ω₂ n) where
  /-- The underlying `ℂ`-linear map. -/
  toLinearMap : W₁ →ₗ[ℂ] W₂
  /-- Preservation of the Hodge filtration: $f(F_1^p) \subseteq F_2^p$. -/
  map_F_le : ∀ p : ℤ, (hs₁.F p).map toLinearMap ≤ hs₂.F p
  /-- Commutation with conjugation: $f(\overline{x}) = \overline{f(x)}$. -/
  map_conj : ∀ x : W₁,
    toLinearMap (ω₁.toEquiv.toLinearMap x) = ω₂.toEquiv.toLinearMap (toLinearMap x)

namespace HodgeStructureOn.Hom

variable {W₁ : Type*} [AddCommGroup W₁] [Module ℂ W₁] {ω₁ : Conjugation W₁}
  {W₂ : Type*} [AddCommGroup W₂] [Module ℂ W₂] {ω₂ : Conjugation W₂}
  {n : ℤ} {hs₁ : HodgeStructureOn W₁ ω₁ n} {hs₂ : HodgeStructureOn W₂ ω₂ n}

public instance : DFunLike (Hom hs₁ hs₂) W₁ (fun _ => W₂) where
  coe f := f.toLinearMap
  coe_injective f g h := by
    ext x
    exact congrFun h x

@[simp]
public theorem coe_toLinearMap (f : Hom hs₁ hs₂) : ⇑f.toLinearMap = f := rfl

/-- Identity morphism of a pure Hodge structure. -/
public def id (hs : HodgeStructureOn W₁ ω₁ n) : Hom hs hs where
  toLinearMap := LinearMap.id
  map_F_le p := by rw [Submodule.map_id]
  map_conj x := rfl

/-- Composition of morphisms of pure Hodge structures. -/
public def comp {W₃ : Type*} [AddCommGroup W₃] [Module ℂ W₃] {ω₃ : Conjugation W₃}
    {hs₃ : HodgeStructureOn W₃ ω₃ n} (g : Hom hs₂ hs₃) (f : Hom hs₁ hs₂) : Hom hs₁ hs₃ where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_F_le p := by
    rw [Submodule.map_comp]
    exact le_trans (Submodule.map_mono (f.map_F_le p)) (g.map_F_le p)
  map_conj x := by
    simp only [LinearMap.comp_apply]
    rw [f.map_conj, g.map_conj]

/-- A morphism of pure Hodge structures preserves the `(p, q)`-pieces:
$f(H^{p,q}) \subseteq H^{p,q}$. -/
public theorem map_piece_le (f : Hom hs₁ hs₂) (p : ℤ) :
    (hs₁.piece p).map f.toLinearMap ≤ hs₂.piece p := by
  rintro x hx
  rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
  rcases (hs₁.mem_piece_iff p y).mp hy with ⟨hyF, hyconj⟩
  rw [hs₂.mem_piece_iff]
  refine ⟨f.map_F_le p (Submodule.mem_map_of_mem hyF), ?_⟩
  rcases Submodule.mem_map.mp hyconj with ⟨z, hz, rfl⟩
  rw [Submodule.mem_map]
  refine ⟨f.toLinearMap z, f.map_F_le (n - p) (Submodule.mem_map_of_mem hz), ?_⟩
  exact (f.map_conj z).symm

end HodgeStructureOn.Hom

/-- The Tate Hodge structure $\mathbb{Z}(m)$ of weight $-2m$ on $V = \mathbb{Z}$. -/
@[expose]
public noncomputable def tate (m : ℤ) :
    HodgeStructure (TensorProduct.isBaseChange ℤ ℤ ℂ) (-2 * m) where
  F p := if p ≤ -m then ⊤ else ⊥
  F_antitone := by
    intro p q hpq
    change (if q ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) ≤
      (if p ≤ -m then ⊤ else ⊥)
    by_cases hq : q ≤ -m
    · have hp : p ≤ -m := by omega
      rw [ite_eq_left hq, ite_eq_left hp]
    · rw [ite_eq_right hq]
      exact bot_le
  F_bot := ⟨-m + 1, ite_eq_right (by omega)⟩
  opposed p := by
    change IsCompl (if p ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥)
      (Submodule.map (latticeConjugation (TensorProduct.isBaseChange ℤ ℤ ℂ)).toEquiv.toLinearMap
        (if -2 * m + 1 - p ≤ -m then ⊤ else ⊥))
    by_cases hp : p ≤ -m
    · have h1 : (if p ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) = ⊤ :=
        ite_eq_left hp
      have h2 : (if -2 * m + 1 - p ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) = ⊥ :=
        ite_eq_right (by omega)
      rw [h1, h2, Submodule.map_bot]
      exact isCompl_top_bot
    · have h1 : (if p ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) = ⊥ :=
        ite_eq_right hp
      have h2 : (if -2 * m + 1 - p ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) = ⊤ :=
        ite_eq_left (by omega)
      rw [h1, h2, Conjugation.map_top]
      exact isCompl_bot_top

@[simp]
public theorem tate_F (m p : ℤ) : (tate m).F p = if p ≤ -m then ⊤ else ⊥ := rfl

/-- The `(p, q)`-pieces of the Tate Hodge structure $\mathbb{Z}(m)$: the piece at $p = -m$
is all of `ℂ ⊗[ℤ] ℤ` and every other piece is `⊥`. -/
@[simp]
public theorem tate_piece_apply (m : ℤ) (p : ℤ) :
    (tate m).piece p = if p = -m then ⊤ else ⊥ := by
  rw [HodgeStructureOn.piece_def, tate_F, tate_F]
  by_cases hp : p = -m
  · subst hp
    have h1 : (if -m ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) = ⊤ :=
      ite_eq_left (by omega)
    have h2 : (if -2 * m - -m ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) = ⊤ :=
      ite_eq_left (by omega)
    rw [h1, h2, Conjugation.map_top, inf_top_eq, ite_eq_left (by omega)]
  · rw [ite_eq_right hp]
    rcases lt_or_gt_of_ne hp with hp_lt | hp_gt
    · have h1 : (if p ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) = ⊤ :=
        ite_eq_left (by omega)
      have h2 : (if -2 * m - p ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) = ⊥ :=
        ite_eq_right (by omega)
      rw [h1, h2, Submodule.map_bot, inf_bot_eq]
    · have h1 : (if p ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) = ⊥ :=
        ite_eq_right (by omega)
      rw [h1, bot_inf_eq]

/-- The Tate Hodge structure $\mathbb{Z}(m)$ of weight $-2m$ is effective if and only
if $m \le 0$. -/
public theorem isEffective_tate_iff (m : ℤ) : (tate m).IsEffective ↔ m ≤ 0 := by
  rw [HodgeStructureOn.isEffective_iff, tate_F]
  constructor
  · intro h
    by_contra! hm
    have h_top : (if -2 * m + 1 ≤ -m then (⊤ : Submodule ℂ (Complexification ℤ)) else ⊥) = ⊤ :=
      ite_eq_left (by omega)
    rw [h_top] at h
    have h_mem : (1 : ℂ) ⊗ₜ[ℤ] (1 : ℤ) ∈ (⊤ : Submodule ℂ (Complexification ℤ)) :=
      Submodule.mem_top
    rw [h, Submodule.mem_bot] at h_mem
    have h_ne : (1 : ℂ) ⊗ₜ[ℤ] (1 : ℤ) ≠ 0 := fun h_zero => by
      simpa using congrArg (TensorProduct.rid ℤ ℂ) h_zero
    exact h_ne h_mem
  · intro hm
    exact ite_eq_right (by omega)

end TauCeti.Geometry.Hodge
