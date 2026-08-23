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

* the conjugate Hodge filtration `TauCeti.Hodge.MixedHodgeStructure.conjF` of a mixed Hodge
  structure, with its basic order theory;
* the containments `I^{p,q} ≤ F^p`, `I^{p,q} ≤ W_{p+q}` and
  `I^{p,q} ≤ conj F^q ⊔ W_{p+q-2}` — the last says that *modulo lower weight* the bigrading piece
  really does sit in `F^p ∩ conj F^q`, which is the bidegree it is meant to carry;
* the vanishing of `I^{p,q}` outside the range fixed by the boundedness of the two filtrations;
* the conjugate of `I^{p,q}`, which is the same formula with the Hodge filtration and its
  conjugate exchanged;
* functoriality: a morphism of mixed Hodge structures carries `I^{p,q}` into `I^{p,q}`;
* the computation of the bigrading of a *pure* Hodge structure viewed as a mixed one: it is
  concentrated on the antidiagonal `p + q = n`, where it is the Hodge component `H^{p,q}`. In
  particular the bigrading of a pure structure is an internal direct sum, namely its Hodge
  decomposition.

The remaining steps of Deligne's theorem — that `⨁_{p,q} I^{p,q}` is the whole space for an
arbitrary mixed Hodge structure, the recovery of `F` and `W` from the bigrading, and the
conjugation symmetry `I^{p,q} ≡ conj I^{q,p}` modulo lower bidegree — are not proved here.

## Main declarations

* `TauCeti.Hodge.MixedHodgeStructure.conjF`: the conjugate Hodge filtration.
* `TauCeti.Hodge.MixedHodgeStructure.deligneSplitting`: the bigrading `I^{p,q}`.
* `TauCeti.Hodge.MixedHodgeStructure.deligneSplitting_le_conjF_sup_WC`: the piece `I^{p,q}` lies
  in `conj F^q` modulo the weight filtration two steps down.
* `TauCeti.Hodge.MixedHodgeStructure.map_latticeConj_deligneSplitting`: the conjugate of a
  bigrading piece.
* `TauCeti.Hodge.MixedHodgeStructure.Hom.map_deligneSplitting_le`: functoriality.
* `TauCeti.Hodge.MixedHodgeStructure.deligneSplitting_ofPure_of_add_eq` and
  `…_of_add_ne`: the bigrading of a pure Hodge structure.
* `TauCeti.Hodge.MixedHodgeStructure.isInternal_deligneSplittingFamily_ofPure`: for a pure Hodge
  structure the bigrading is an internal direct sum, the Hodge decomposition.

## References

Deligne, *Théorie de Hodge II*, 1.2.11 and 2.3.5; Peters–Steenbrink, *Mixed Hodge Structures*,
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

/-! ### The conjugate Hodge filtration -/

/-- The conjugate `conj F^p` of the `p`-th step of the Hodge filtration of a mixed Hodge
structure, taken for lattice-induced conjugation. -/
noncomputable def conjF (p : ℤ) : Submodule ℂ Vℂ :=
  (mhs.F p).map (latticeConj hℂ)

/-- The conjugate Hodge filtration step is the image of the Hodge filtration step under
lattice-induced conjugation. -/
theorem conjF_def (p : ℤ) : mhs.conjF p = (mhs.F p).map (latticeConj hℂ) := (rfl)

/-- The conjugate Hodge filtration is decreasing. -/
theorem conjF_antitone : Antitone mhs.conjF := fun _ _ h ↦ by
  rw [conjF_def, conjF_def]
  exact Submodule.map_mono (mhs.F_antitone h)

/-- Membership in a conjugate Hodge filtration step is detected by conjugating. -/
@[simp]
theorem mem_conjF_iff (p : ℤ) (x : Vℂ) : x ∈ mhs.conjF p ↔ latticeConj hℂ x ∈ mhs.F p := by
  rw [conjF_def]
  refine ⟨?_, fun hx ↦ ⟨latticeConj hℂ x, hx, latticeConj_apply_apply hℂ x⟩⟩
  rintro ⟨y, hy, rfl⟩
  rwa [latticeConj_apply_apply]

/-- Conjugating a Hodge filtration step twice recovers it. -/
@[simp]
theorem conjF_conjF (p : ℤ) : (mhs.conjF p).map (latticeConj hℂ) = mhs.F p := by
  refine le_antisymm ?_ fun x hx ↦
    ⟨latticeConj hℂ x, (mhs.mem_conjF_iff p _).2 (by rwa [latticeConj_apply_apply]),
      latticeConj_apply_apply hℂ x⟩
  rintro x ⟨y, hy, rfl⟩
  exact (mhs.mem_conjF_iff p y).1 hy

/-- The conjugate Hodge filtration is exhaustive wherever the Hodge filtration is. -/
theorem conjF_of_eq_top {p : ℤ} (hp : mhs.F p = ⊤) : mhs.conjF p = ⊤ :=
  Submodule.eq_top_iff'.2 fun x ↦ (mhs.mem_conjF_iff p x).2 (hp ▸ Submodule.mem_top)

/-- The conjugate Hodge filtration is separated wherever the Hodge filtration is. -/
theorem conjF_of_eq_bot {p : ℤ} (hp : mhs.F p = ⊥) : mhs.conjF p = ⊥ := by
  rw [conjF_def, hp, Submodule.map_bot]

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

/-- Deligne's bigrading repackaged as a single family indexed by bidegrees, the form in which
`DirectSum.IsInternal` consumes it. -/
noncomputable def deligneSplittingFamily (pq : ℤ × ℤ) : Submodule ℂ Vℂ :=
  mhs.deligneSplitting pq.1 pq.2

/-- The bidegree-indexed family is Deligne's bigrading. -/
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

/-- Modulo the weight filtration two steps below its total degree, a bigrading piece lies in the
conjugate Hodge filtration step of its second index. Together with
`TauCeti.Hodge.MixedHodgeStructure.deligneSplitting_le_F` this is the statement that `I^{p,q}`
carries the bidegree `(p, q)` it is named for. -/
theorem deligneSplitting_le_conjF_sup_WC (p q : ℤ) :
    mhs.deligneSplitting p q ≤ mhs.conjF q ⊔ mhs.WC (p + q - 2) := by
  rw [deligneSplitting_def]
  refine inf_le_right.trans (sup_le (inf_le_left.trans le_sup_left) (iSup_le fun j ↦ ?_))
  exact (inf_le_right.trans (mhs.WC_monotone (by omega))).trans le_sup_right

/-- Above a Hodge filtration index at which the filtration vanishes, the bigrading vanishes. -/
theorem deligneSplitting_eq_bot_of_F_eq_bot {b : ℤ} (hb : mhs.F b = ⊥) {p q : ℤ} (hbp : b ≤ p) :
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

/-- A morphism of mixed Hodge structures preserves the conjugate Hodge filtration. -/
theorem map_conjF_le (f : Hom source target) (p : ℤ) :
    (source.conjF p).map f.toLinearMap ≤ target.conjF p := by
  have hcomm : ∀ y : Vℂ,
      f.toLinearMap (latticeConj hℂ y) = latticeConj h'ℂ (f.toLinearMap y) := by
    rw [toLinearMap_def]
    exact rationalMapToComplex_commutes_conj hℚ hℂ h'ℚ h'ℂ f.toRatLinearMap
  rw [Submodule.map_le_iff_le_comap]
  intro y hy
  rw [Submodule.mem_comap, mem_conjF_iff, ← hcomm]
  exact f.map_F_le p (Submodule.mem_map_of_mem ((source.mem_conjF_iff p y).1 hy))

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

/-- The conjugate Hodge filtration of a pure Hodge structure viewed as a mixed one is its
conjugate Hodge filtration. -/
@[simp]
theorem ofPure_conjF (p : ℤ) :
    (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).conjF p = hs.conjF p := by
  rw [conjF_def, MixedHodgeStructure.ofPure_F, HodgeStructureOn.conjF_def,
    latticeConjugation_toLinearMap]

/-- The weight filtration of a pure Hodge structure of weight `n`, viewed as a mixed one, is the
whole space from degree `n` on. -/
theorem ofPure_WC_of_le {k : ℤ} (hk : n ≤ k) :
    (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).WC k = ⊤ := by
  rw [WC_def, MixedHodgeStructure.ofPure_WQ, concentratedWeightFiltration_of_le hk,
    rationalToComplexSubmodule_top]

/-- The weight filtration of a pure Hodge structure of weight `n`, viewed as a mixed one, vanishes
below degree `n`. -/
theorem ofPure_WC_of_lt {k : ℤ} (hk : k < n) :
    (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).WC k = ⊥ := by
  rw [WC_def, MixedHodgeStructure.ofPure_WQ, concentratedWeightFiltration_of_lt hk,
    rationalToComplexSubmodule_bot]

/-- **On the antidiagonal the Deligne bigrading of a pure Hodge structure is its Hodge
decomposition:** for `p + q = n` the piece `I^{p,q}` is the Hodge component `H^{p,q}`. -/
theorem deligneSplitting_ofPure_of_add_eq {p q : ℤ} (hpq : p + q = n) :
    (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).deligneSplitting p q = hs.piece p := by
  obtain rfl : q = n - p := by omega
  have hbot : ∀ j : ℕ, (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).conjF
      (n - p - (j : ℤ) - 1) ⊓
      (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).WC (p + (n - p) - (j : ℤ) - 2) = ⊥ :=
    fun j ↦ by rw [ofPure_WC_of_lt hℚ hℂ hs (by omega), inf_bot_eq]
  rw [deligneSplitting_def, ofPure_WC_of_le hℚ hℂ hs (by omega)]
  simp only [hbot, iSup_bot, sup_bot_eq, inf_top_eq]
  rw [MixedHodgeStructure.ofPure_F, ofPure_conjF, HodgeStructureOn.piece_def]

/-- **Off the antidiagonal the Deligne bigrading of a pure Hodge structure vanishes.** Below it
the weight filtration is zero; above it the defining intersection is cut out by two complementary
filtration steps. -/
theorem deligneSplitting_ofPure_of_add_ne {p q : ℤ} (hpq : p + q ≠ n) :
    (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).deligneSplitting p q = ⊥ := by
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · exact deligneSplitting_eq_bot_of_WC_eq_bot _ (ofPure_WC_of_lt hℚ hℂ hs hlt) le_rfl
  · refine le_bot_iff.1 ?_
    have hsecond :
        ((MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).conjF q ⊓
            (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).WC (p + q)) ⊔
          (⨆ j : ℕ, (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).conjF (q - (j : ℤ) - 1) ⊓
            (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).WC (p + q - (j : ℤ) - 2)) ≤
          (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).conjF (n + 1 - p) := by
      refine sup_le (inf_le_left.trans (conjF_antitone _ (by omega))) (iSup_le fun j ↦ ?_)
      rcases le_or_gt n (p + q - (j : ℤ) - 2) with h | h
      · exact inf_le_left.trans (conjF_antitone _ (by omega))
      · rw [ofPure_WC_of_lt hℚ hℂ hs h, inf_bot_eq]
        exact bot_le
    rw [deligneSplitting_def]
    refine (inf_le_inf inf_le_left hsecond).trans ?_
    rw [ofPure_conjF, MixedHodgeStructure.ofPure_F]
    exact (hs.isCompl_F_conjF p).disjoint.le_bot

/-- **For a pure Hodge structure the Deligne bigrading is an internal direct sum**, namely the
Hodge decomposition placed on the antidiagonal `p + q = n`. This exhibits the bigrading as
nondegenerate, and is the case of Deligne's theorem in which the weight filtration has a single
jump. -/
theorem isInternal_deligneSplittingFamily_ofPure :
    DirectSum.IsInternal
      (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).deligneSplittingFamily := by
  classical
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ (top_unique ?_)
  · intro pq
    rcases eq_or_ne (pq.1 + pq.2) n with h | h
    · rw [deligneSplittingFamily_apply, deligneSplitting_ofPure_of_add_eq hℚ hℂ hs h]
      refine (hs.piece_iSupIndep pq.1).mono_right (iSup₂_le fun rs hrs ↦ ?_)
      rcases eq_or_ne (rs.1 + rs.2) n with h' | h'
      · rw [deligneSplittingFamily_apply, deligneSplitting_ofPure_of_add_eq hℚ hℂ hs h']
        exact le_iSup₂_of_le rs.1 (fun hEq ↦ hrs (Prod.ext hEq (by omega))) le_rfl
      · rw [deligneSplittingFamily_apply, deligneSplitting_ofPure_of_add_ne hℚ hℂ hs h']
        exact bot_le
    · rw [deligneSplittingFamily_apply, deligneSplitting_ofPure_of_add_ne hℚ hℂ hs h]
      exact disjoint_bot_left
  · rw [← hs.iSup_piece_eq_top]
    refine iSup_le fun p ↦ le_iSup_of_le (p, n - p) ?_
    rw [deligneSplittingFamily_apply]
    exact le_of_eq (deligneSplitting_ofPure_of_add_eq hℚ hℂ hs (by omega)).symm

end MixedHodgeStructure

end TauCeti.Hodge
