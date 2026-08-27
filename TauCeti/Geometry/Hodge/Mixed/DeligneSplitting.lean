/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.Morphism

/-!
# Deligne's bigrading of a mixed Hodge structure

Deligne's canonical bigrading of a mixed Hodge structure is the family of complex subspaces

`I^{p,q} = (F^p ∩ W_{p+q}) ∩ (conj F^q ∩ W_{p+q} + ∑_{j ≥ 2} conj F^{q-j+1} ∩ W_{p+q-j})`,

built from the Hodge filtration, its conjugate, and the complexified weight filtration. It is the
working tool of the mixed theory: strictness of a morphism of mixed Hodge structures is proved
through it, and it is what the theory of variations consumes. Accordingly it is *defined* here by
Deligne's closed formula rather than obtained from an existence statement, so that lemmas can be
stated about it.

This file constructs the bigrading and establishes the part of its theory that follows from the
formula itself:

* the containments `I^{p,q} ≤ F^p`, `I^{p,q} ≤ W_{p+q}` and
  `I^{p,q} ≤ conj F^q ⊔ W_{p+q-2}` — so `I^{p,q}` lies in the Hodge step and weight step of its
  bidegree, and modulo `W_{p+q-2}` in `conj F^q`;
* the vanishing of `I^{p,q}` outside the range fixed by the boundedness of the two filtrations;
* the conjugate of `I^{p,q}`, which is the same formula with the Hodge filtration and its
  conjugate exchanged;
* functoriality: a morphism of mixed Hodge structures carries `I^{p,q}` into `I^{p,q}`;
* the computation of the bigrading of a *pure* Hodge structure viewed as a mixed one: it is
  concentrated on the antidiagonal `p + q = n`, where it is the Hodge component `H^{p,q}`.

That `⨁_{p,q} I^{p,q}` is the whole space, and the recovery `W_k = ⨆_{p+q ≤ k} I^{p,q}` of the
weight filtration, are proved in `TauCeti/Geometry/Hodge/Mixed/Decomposition.lean`, which needs
the pure Hodge structure carried by the graded pieces and so cannot be part of this file. What
remains of Deligne's theorem after that module is the recovery `F^p = ⨆_{p' ≥ p} ⨆_{q'} I^{p',q'}`
of the Hodge filtration and the conjugation symmetry `I^{p,q} ≡ conj I^{q,p}` modulo lower
bidegree.

## Main declarations

* `TauCeti.Hodge.MixedHodgeStructure.deligneSplitting`: the bigrading `I^{p,q}`.
* `TauCeti.Hodge.MixedHodgeStructure.deligneSplitting_le_conjF_sup_WC`: the piece `I^{p,q}` lies
  in `conj F^q` modulo the weight filtration two steps down.
* `TauCeti.Hodge.MixedHodgeStructure.map_latticeConj_deligneSplitting`: the conjugate of a
  bigrading piece.
* `TauCeti.Hodge.MixedHodgeStructure.Hom.map_deligneSplitting_le`: functoriality.
* `TauCeti.Hodge.MixedHodgeStructure.ofPure_deligneSplitting_eq_piece_of_add_eq` and
  `…deligneSplitting_eq_bot_of_add_ne`: the bigrading of a pure Hodge structure.

## References

Deligne, *Théorie de Hodge II*, 1.2.10 and 2.3.5; Peters–Steenbrink, *Mixed Hodge Structures*,
Lemma-Definition 3.4 and Ch. 3. The formula and the conventions are those fixed for Layer L2 of
the Hodge structures roadmap.
-/

public section

namespace TauCeti.Hodge

universe u v w u' v' w'

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}

namespace MixedHodgeStructure

variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ} (mhs : MixedHodgeStructure hℚ hℂ)

/-! ### The bigrading -/

/-- **Deligne's bigrading** of a mixed Hodge structure:

`I^{p,q} = (F^p ∩ W_{p+q}) ∩ (conj F^q ∩ W_{p+q} + ∑_{j ≥ 2} conj F^{q-j+1} ∩ W_{p+q-j})`,

with the tail sum indexed here by `j - 2 : ℕ`. -/
noncomputable def deligneSplitting (p q : ℤ) : Submodule ℂ Vℂ :=
  (mhs.F p ⊓ mhs.WC (p + q)) ⊓
    ((mhs.conjF q ⊓ mhs.WC (p + q)) ⊔
      ⨆ j : ℕ, mhs.conjF (q - (j : ℤ) - 1) ⊓ mhs.WC (p + q - (j : ℤ) - 2))

/-- Deligne's closed formula for the bigrading. -/
theorem deligneSplitting_def (p q : ℤ) :
    mhs.deligneSplitting p q =
      (mhs.F p ⊓ mhs.WC (p + q)) ⊓
        ((mhs.conjF q ⊓ mhs.WC (p + q)) ⊔
          ⨆ j : ℕ, mhs.conjF (q - (j : ℤ) - 1) ⊓ mhs.WC (p + q - (j : ℤ) - 2)) :=
  (rfl)

/-- Membership in Deligne's bigrading, expanded into its three defining conditions. -/
@[simp]
theorem mem_deligneSplitting_iff (p q : ℤ) (x : Vℂ) :
    x ∈ mhs.deligneSplitting p q ↔
      x ∈ mhs.F p ∧ x ∈ mhs.WC (p + q) ∧
        x ∈ (mhs.conjF q ⊓ mhs.WC (p + q)) ⊔
          ⨆ j : ℕ, mhs.conjF (q - (j : ℤ) - 1) ⊓ mhs.WC (p + q - (j : ℤ) - 2) := by
  simp only [deligneSplitting_def, Submodule.mem_inf, and_assoc]

/-- Vectors lying simultaneously in `F^p`, `conj F^q`, and `W_{p+q}` lie in the corresponding
Deligne bigrading piece. -/
theorem F_inf_conjF_inf_WC_le_deligneSplitting (p q : ℤ) :
    mhs.F p ⊓ mhs.conjF q ⊓ mhs.WC (p + q) ≤ mhs.deligneSplitting p q := by
  rw [deligneSplitting_def]
  refine le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right) ?_
  exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans le_sup_left

/-- A Deligne bigrading piece lies in the second factor of its defining intersection. -/
private theorem deligneSplitting_le_conjF_inf_WC_sup_iSup (p q : ℤ) :
    mhs.deligneSplitting p q ≤
      (mhs.conjF q ⊓ mhs.WC (p + q)) ⊔
        ⨆ j : ℕ, mhs.conjF (q - (j : ℤ) - 1) ⊓ mhs.WC (p + q - (j : ℤ) - 2) := by
  rw [deligneSplitting_def]
  exact inf_le_right

/-- Deligne's bigrading repackaged as a single family indexed by bidegrees, the form in which
`DirectSum.IsInternal` consumes it. -/
noncomputable def deligneSplittingFamily (pq : ℤ × ℤ) : Submodule ℂ Vℂ :=
  mhs.deligneSplitting pq.1 pq.2

/-- The bidegree-indexed family is Deligne's bigrading. -/
@[simp]
theorem deligneSplittingFamily_apply (pq : ℤ × ℤ) :
    mhs.deligneSplittingFamily pq = mhs.deligneSplitting pq.1 pq.2 :=
  (rfl)

/-- A bigrading piece lies in the Hodge filtration step of its first index. -/
theorem deligneSplitting_le_F (p q : ℤ) : mhs.deligneSplitting p q ≤ mhs.F p := by
  rw [deligneSplitting_def]
  exact inf_le_left.trans inf_le_left

/-- A bigrading piece lies in the weight filtration step of its total degree. -/
theorem deligneSplitting_le_WC (p q : ℤ) : mhs.deligneSplitting p q ≤ mhs.WC (p + q) := by
  rw [deligneSplitting_def]
  exact inf_le_left.trans inf_le_right

/-- After shifting by `m`, a Deligne bigrading piece lies in `conj F^{q-m}` modulo the weight
filtration step `W_{p+q-m-2}`. -/
theorem deligneSplitting_le_conjF_sub_sup_WC (p q m : ℤ) (hm : 0 ≤ m) :
    mhs.deligneSplitting p q ≤
      mhs.conjF (q - m) ⊔ mhs.WC (p + q - m - 2) := by
  refine (mhs.deligneSplitting_le_conjF_inf_WC_sup_iSup p q).trans ?_
  refine sup_le ((inf_le_left.trans (mhs.conjF_antitone (by omega))).trans le_sup_left)
    (iSup_le fun j ↦ ?_)
  by_cases hj : (j : ℤ) < m
  · exact (inf_le_left.trans (mhs.conjF_antitone (by omega))).trans le_sup_left
  · exact (inf_le_right.trans (mhs.WC_monotone
      (by omega : p + q - (j : ℤ) - 2 ≤ p + q - m - 2))).trans le_sup_right

/-- Modulo the weight filtration two steps below its total degree, a bigrading piece lies in the
conjugate Hodge filtration step of its second index. -/
theorem deligneSplitting_le_conjF_sup_WC (p q : ℤ) :
    mhs.deligneSplitting p q ≤ mhs.conjF q ⊔ mhs.WC (p + q - 2) := by
  simpa using mhs.deligneSplitting_le_conjF_sub_sup_WC p q 0 le_rfl

/-- If the weight filtration vanishes two steps below the total degree, Deligne's formula
collapses to the intersection of its three leading filtration steps. -/
theorem deligneSplitting_eq_F_inf_conjF_inf_WC_of_WC_eq_bot {p q : ℤ}
    (h : mhs.WC (p + q - 2) = ⊥) :
    mhs.deligneSplitting p q = mhs.F p ⊓ mhs.conjF q ⊓ mhs.WC (p + q) := by
  have htail :
      (⨆ j : ℕ, mhs.conjF (q - (j : ℤ) - 1) ⊓
        mhs.WC (p + q - (j : ℤ) - 2)) = ⊥ := by
    apply iSup_eq_bot.2
    intro j
    exact le_bot_iff.1 (inf_le_right.trans ((mhs.WC_monotone (by omega)).trans_eq h))
  rw [deligneSplitting_def, htail, sup_bot_eq]
  ac_rfl

/-- If `W_m = 0` with `m ≤ p + q - 2`, then
`I^{p,q} ≤ F^p ∩ conj F^{m+2-p}`. -/
theorem deligneSplitting_le_F_inf_conjF_of_WC_eq_bot {m p q : ℤ} (hm : mhs.WC m = ⊥)
    (h : m + 1 < p + q) :
    mhs.deligneSplitting p q ≤ mhs.F p ⊓ mhs.conjF (m + 2 - p) := by
  refine le_inf (mhs.deligneSplitting_le_F p q) ?_
  have hd : 0 ≤ p + q - m - 2 := by omega
  have hfirst : q - (p + q - m - 2) = m + 2 - p := by omega
  have hsecond : p + q - (p + q - m - 2) - 2 = m := by omega
  simpa only [hfirst, hsecond, hm, sup_bot_eq] using
    mhs.deligneSplitting_le_conjF_sub_sup_WC p q (p + q - m - 2) hd

/-- Above a Hodge filtration index at which the filtration vanishes, the bigrading vanishes: the
hypothesis bounds the *first* index. -/
theorem deligneSplitting_eq_bot_of_F_eq_bot_left {b : ℤ} (hb : mhs.F b = ⊥) {p q : ℤ}
    (hbp : b ≤ p) :
    mhs.deligneSplitting p q = ⊥ :=
  le_bot_iff.1 ((mhs.deligneSplitting_le_F p q).trans ((mhs.F_antitone hbp).trans_eq hb))

/-- Below a weight filtration index at which the filtration vanishes, the bigrading vanishes. -/
theorem deligneSplitting_eq_bot_of_WC_eq_bot {k : ℤ} (hk : mhs.WC k = ⊥) {p q : ℤ}
    (hpq : p + q ≤ k) : mhs.deligneSplitting p q = ⊥ :=
  le_bot_iff.1 ((mhs.deligneSplitting_le_WC p q).trans ((mhs.WC_monotone hpq).trans_eq hk))

/-- The conjugate of a bigrading piece is given by Deligne's formula with the Hodge filtration and
its conjugate exchanged. -/
theorem map_latticeConj_deligneSplitting (p q : ℤ) :
    (mhs.deligneSplitting p q).map (latticeConj hℂ) =
      (mhs.conjF p ⊓ mhs.WC (p + q)) ⊓
        ((mhs.F q ⊓ mhs.WC (p + q)) ⊔
          ⨆ j : ℕ, mhs.F (q - (j : ℤ) - 1) ⊓ mhs.WC (p + q - (j : ℤ) - 2)) := by
  have hinj : Function.Injective (latticeConj hℂ) := (latticeConj_involutive hℂ).injective
  rw [deligneSplitting_def]
  simp only [Submodule.map_inf _ hinj, Submodule.map_sup, Submodule.map_iSup, conjF_conjF,
    ← conjF_def, WC_conj]

end MixedHodgeStructure

/-! ### Functoriality -/

namespace MixedHodgeStructure.Hom

variable {V'ℤ : Type u'} {V'ℚ : Type v'} {V'ℂ : Type w'}
variable [AddCommGroup V'ℤ] [AddCommGroup V'ℚ] [Module ℚ V'ℚ] [AddCommGroup V'ℂ] [Module ℂ V'ℂ]
variable {ι'ℚ : V'ℤ →ₗ[ℤ] V'ℚ} {ι'ℂ : V'ℤ →ₗ[ℤ] V'ℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {h'ℚ : IsBaseChange ℚ ι'ℚ} {h'ℂ : IsBaseChange ℂ ι'ℂ}
variable {source : MixedHodgeStructure hℚ hℂ} {target : MixedHodgeStructure h'ℚ h'ℂ}

/-- **Functoriality of Deligne's bigrading.** A morphism of mixed Hodge structures carries the
bigrading piece `I^{p,q}` of its source into the bigrading piece `I^{p,q}` of its target. -/
theorem map_deligneSplitting_le (f : Hom source target) (p q : ℤ) :
    (source.deligneSplitting p q).map f.toLinearMap ≤ target.deligneSplitting p q := by
  rw [deligneSplitting_def, deligneSplitting_def]
  refine (Submodule.map_inf_le _).trans (inf_le_inf ((Submodule.map_inf_le _).trans
    (inf_le_inf (f.map_F_le p) (f.map_WC_le (p + q)))) ?_)
  rw [Submodule.map_sup, Submodule.map_iSup]
  exact sup_le_sup ((Submodule.map_inf_le _).trans
      (inf_le_inf (f.map_conjF_le q) (f.map_WC_le (p + q))))
    (iSup_mono fun j ↦ (Submodule.map_inf_le _).trans
      (inf_le_inf (f.map_conjF_le _) (f.map_WC_le _)))

/-- Elementwise form of functoriality of Deligne's bigrading. -/
theorem map_mem_deligneSplitting (f : Hom source target) (p q : ℤ) {x : Vℂ}
    (hx : x ∈ source.deligneSplitting p q) : f.toLinearMap x ∈ target.deligneSplitting p q :=
  f.map_deligneSplitting_le p q (Submodule.mem_map_of_mem hx)

end MixedHodgeStructure.Hom

/-! ### The bigrading of a pure Hodge structure -/

namespace MixedHodgeStructure

variable (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ) {n : ℤ} (hs : HodgeStructure hℂ n)

/-- **On the antidiagonal the Deligne bigrading of a pure Hodge structure is its Hodge
decomposition:** for `p + q = n` the piece `I^{p,q}` is the Hodge component `H^{p,q}`. -/
@[simp]
theorem ofPure_deligneSplitting_eq_piece_of_add_eq {p q : ℤ} (hpq : p + q = n) :
    (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).deligneSplitting p q = hs.piece p := by
  obtain rfl : q = n - p := by omega
  have hcollapse :=
    deligneSplitting_eq_F_inf_conjF_inf_WC_of_WC_eq_bot
      (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs)
      (p := p) (q := n - p) (ofPure_WC_eq_bot_of_lt hℚ hℂ hs (by omega))
  rw [hcollapse,
    ofPure_WC_eq_top_of_le hℚ hℂ hs (by omega), inf_top_eq,
    MixedHodgeStructure.ofPure_F, ofPure_conjF, HodgeStructureOn.piece_def]

/-- **Off the antidiagonal the Deligne bigrading of a pure Hodge structure vanishes.** Below it
the weight filtration is zero; above it the defining intersection is cut out by two complementary
filtration steps. -/
@[simp]
theorem ofPure_deligneSplitting_eq_bot_of_add_ne {p q : ℤ} (hpq : p + q ≠ n) :
    (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).deligneSplitting p q = ⊥ := by
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · exact deligneSplitting_eq_bot_of_WC_eq_bot _ (ofPure_WC_eq_bot_of_lt hℚ hℂ hs hlt) le_rfl
  · refine le_bot_iff.1 ?_
    have hle :=
      deligneSplitting_le_F_inf_conjF_of_WC_eq_bot
        (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs)
        (ofPure_WC_eq_bot_of_lt hℚ hℂ hs (k := n - 1) (by omega)) (by omega : n - 1 + 1 < p + q)
    rw [MixedHodgeStructure.ofPure_F, ofPure_conjF] at hle
    have hindex : n - 1 + 2 - p = n + 1 - p := by omega
    exact hle.trans (by simpa only [hindex] using
      (hs.isCompl_F_conjF p).disjoint.le_bot)

end MixedHodgeStructure

end TauCeti.Hodge
