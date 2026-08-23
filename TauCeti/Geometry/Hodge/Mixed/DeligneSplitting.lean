/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.Morphism

/-!
# Deligne's bigrading of a mixed Hodge structure

Deligne's canonical bigrading `I^{p,q}` of a mixed Hodge structure is given by a closed formula in
the Hodge filtration `F`, its conjugate `conj F`, and the complexified weight filtration `W`:
`I^{p,q} = (F^p ⊓ W_{p+q}) ⊓ (conj F^q ⊓ W_{p+q} + ∑_{j ≥ 1} conj F^{q-j} ⊓ W_{p+q-j-1})`.
It is the working tool of the mixed theory: the recovery of `F` and `W` from it, and Deligne's
strictness theorem for morphisms of mixed Hodge structures, are all proved through it. Because a
consumer needs to state lemmas about a *fixed* bigrading rather than destruct an existential, the
formula is taken as the definition, `TauCeti.Hodge.MixedHodgeStructure.deligneSplitting`, rather
than obtaining the bigrading from an existence theorem.

This file sets up the bigrading and the part of its theory that follows from the formula alone: it
lies in `F^p` and in `W_{p+q}`, it vanishes once `F^p` does or once `W_{p+q}` does, it satisfies
the containments `⨆_{p' ≥ p} I^{p',q} ≤ F^p` and `⨆_{p+q ≤ k} I^{p,q} ≤ W_k` that one half of the
recovery statements asks for, and — the point of the definition being canonical — every morphism of
mixed Hodge structures carries `I^{p,q}` into `I^{p,q}`.

The bigrading is then computed completely on a pure Hodge structure viewed as a mixed one: it
vanishes off the antidiagonal `p + q = n` and is the Hodge component `H^{p,n-p}` on it, so
Deligne's formula specializes to the pure `(p,q)`-decomposition, and the bigrading of a pure
structure is an internal direct sum. This is the compatibility of the mixed theory with the pure
theory of `TauCeti/Geometry/Hodge/Decomposition.lean`, and it is what rules out a formula whose
indices are shifted: only the stated one collapses to `TauCeti.Hodge.HodgeStructureOn.piece`.

The remaining, genuinely mixed, content — that `I^{p,q}` is an internal direct sum for an arbitrary
mixed Hodge structure, the reverse containments recovering `F` and `W`, the conjugation relation
`I^{p,q} ≡ conj I^{q,p}` modulo strictly lower bidegree, and strictness itself — is not proved
here.

## Main declarations

* `TauCeti.Hodge.MixedHodgeStructure.conjF`: the conjugate of the Hodge filtration of a mixed
  Hodge structure.
* `TauCeti.Hodge.MixedHodgeStructure.deligneSplitting`: Deligne's bigrading `I^{p,q}`.
* `TauCeti.Hodge.MixedHodgeStructure.iSup_deligneSplitting_le_F` and
  `TauCeti.Hodge.MixedHodgeStructure.iSup_deligneSplitting_le_WC`: the bigrading is subordinate to
  both filtrations.
* `TauCeti.Hodge.MixedHodgeStructure.Hom.map_deligneSplitting_le`: functoriality of the bigrading.
* `TauCeti.Hodge.MixedHodgeStructure.ofPure_deligneSplitting_of_add_eq` and
  `TauCeti.Hodge.MixedHodgeStructure.ofPure_deligneSplitting_of_add_ne`: on a pure Hodge structure
  the bigrading is the Hodge decomposition, concentrated on the antidiagonal `p + q = n`.
* `TauCeti.Hodge.MixedHodgeStructure.isInternal_ofPure_deligneSplitting`: consequently the
  bigrading of a pure structure is an internal direct sum.

## References

Deligne, *Théorie de Hodge II*, 1.2.8 and 1.2.11; Peters–Steenbrink, *Mixed Hodge Structures*,
Lemma-Definition 3.4 and §3.1. The formula and the plan of its use are those of the Hodge
structures roadmap, layer L2.
-/

public section

namespace TauCeti.Hodge

universe u v w u' v' w'

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}

namespace MixedHodgeStructure

variable (mhs : MixedHodgeStructure hℚ hℂ)

/-! ### The conjugate Hodge filtration -/

/-- The conjugate `conj F^p` of the Hodge filtration of a mixed Hodge structure, taken for the
lattice-induced conjugation of the complex model. -/
noncomputable def conjF (p : ℤ) : Submodule ℂ Vℂ :=
  (mhs.F p).map (latticeConj hℂ)

/-- The conjugate Hodge filtration step is the image of the Hodge filtration step under
lattice-induced conjugation. -/
theorem conjF_def (p : ℤ) : mhs.conjF p = (mhs.F p).map (latticeConj hℂ) :=
  (rfl)

/-- Membership in a conjugate Hodge filtration step is detected by conjugating. -/
@[simp]
theorem mem_conjF_iff (p : ℤ) (x : Vℂ) : x ∈ mhs.conjF p ↔ latticeConj hℂ x ∈ mhs.F p := by
  refine ⟨?_, fun hx ↦ ⟨latticeConj hℂ x, hx, latticeConj_apply_apply hℂ x⟩⟩
  rintro ⟨y, hy, rfl⟩
  rwa [latticeConj_apply_apply]

/-- The conjugate Hodge filtration is decreasing. -/
theorem conjF_antitone : Antitone mhs.conjF := fun _ _ h ↦
  Submodule.map_mono (mhs.F_antitone h)

/-- Conjugating a Hodge filtration step twice recovers it. -/
theorem conjF_conjF (p : ℤ) : (mhs.conjF p).map (latticeConj hℂ) = mhs.F p := by
  ext x
  rw [Submodule.mem_map]
  refine ⟨?_, fun hx ↦ ⟨latticeConj hℂ x, ?_, latticeConj_apply_apply hℂ x⟩⟩
  · rintro ⟨y, hy, rfl⟩
    exact (mhs.mem_conjF_iff p y).1 hy
  · rw [mem_conjF_iff, latticeConj_apply_apply]
    exact hx

/-! ### Deligne's bigrading -/

/-- **Deligne's bigrading.** The subspace
`I^{p,q} = (F^p ⊓ W_{p+q}) ⊓ (conj F^q ⊓ W_{p+q} + ∑_{j ≥ 1} conj F^{q-j} ⊓ W_{p+q-j-1})`
of the complex model of a mixed Hodge structure, with the tail sum indexed by `j = 1 + i`,
`i : ℕ`.

The correction tail is what makes the bigrading canonical in the mixed case: it is exactly the
failure of `conj F` to be opposed to `F`, measured in strictly lower weight. For a pure structure
every tail term vanishes and `I^{p,q}` collapses to the Hodge component `H^{p,n-p}` on the
antidiagonal `p + q = n`; see
`TauCeti.Hodge.MixedHodgeStructure.ofPure_deligneSplitting_of_add_eq`. -/
noncomputable def deligneSplitting (p q : ℤ) : Submodule ℂ Vℂ :=
  (mhs.F p ⊓ mhs.WC (p + q)) ⊓
    ((mhs.conjF q ⊓ mhs.WC (p + q)) ⊔
      ⨆ i : ℕ, mhs.conjF (q - 1 - i) ⊓ mhs.WC (p + q - 2 - i))

/-- Deligne's bigrading, unfolded. -/
theorem deligneSplitting_def (p q : ℤ) :
    mhs.deligneSplitting p q =
      (mhs.F p ⊓ mhs.WC (p + q)) ⊓
        ((mhs.conjF q ⊓ mhs.WC (p + q)) ⊔
          ⨆ i : ℕ, mhs.conjF (q - 1 - i) ⊓ mhs.WC (p + q - 2 - i)) :=
  (rfl)

/-- Deligne's bigrading is subordinate to the Hodge filtration in its first index. -/
theorem deligneSplitting_le_F (p q : ℤ) : mhs.deligneSplitting p q ≤ mhs.F p :=
  inf_le_left.trans inf_le_left

/-- Deligne's bigrading is subordinate to the weight filtration in its total degree. -/
theorem deligneSplitting_le_WC (p q : ℤ) : mhs.deligneSplitting p q ≤ mhs.WC (p + q) :=
  inf_le_left.trans inf_le_right

/-- Deligne's bigrading vanishes above the top of the Hodge filtration. -/
theorem deligneSplitting_eq_bot_of_F_eq_bot {b p : ℤ} (hb : mhs.F b = ⊥) (hbp : b ≤ p) (q : ℤ) :
    mhs.deligneSplitting p q = ⊥ :=
  le_bot_iff.1 ((mhs.deligneSplitting_le_F p q).trans (hb ▸ mhs.F_antitone hbp))

/-- Deligne's bigrading vanishes below the bottom of the weight filtration. -/
theorem deligneSplitting_eq_bot_of_WQ_eq_bot {a p q : ℤ} (ha : mhs.WQ a = ⊥) (h : p + q ≤ a) :
    mhs.deligneSplitting p q = ⊥ := by
  have hW : mhs.WC (p + q) ≤ ⊥ := by
    refine (mhs.WC_monotone h).trans_eq ?_
    rw [WC_def, ha, rationalToComplexSubmodule_bot]
  exact le_bot_iff.1 ((mhs.deligneSplitting_le_WC p q).trans hW)

/-- Half of the recovery of the Hodge filtration from Deligne's bigrading: the bidegrees with
first index at least `p` span no more than `F^p`. -/
theorem iSup_deligneSplitting_le_F (p : ℤ) :
    ⨆ p' : ℤ, ⨆ (_ : p ≤ p'), ⨆ q : ℤ, mhs.deligneSplitting p' q ≤ mhs.F p :=
  iSup₂_le fun p' hp' ↦
    iSup_le fun q ↦ (mhs.deligneSplitting_le_F p' q).trans (mhs.F_antitone hp')

/-- Half of the recovery of the weight filtration from Deligne's bigrading: the bidegrees of total
degree at most `k` span no more than `W_k`. -/
theorem iSup_deligneSplitting_le_WC (k : ℤ) :
    ⨆ p : ℤ, ⨆ q : ℤ, ⨆ (_ : p + q ≤ k), mhs.deligneSplitting p q ≤ mhs.WC k :=
  iSup_le fun p ↦
    iSup₂_le fun q h ↦ (mhs.deligneSplitting_le_WC p q).trans (mhs.WC_monotone h)

end MixedHodgeStructure

/-! ### Functoriality -/

namespace MixedHodgeStructure.Hom

variable {V'ℤ : Type u'} {V'ℚ : Type v'} {V'ℂ : Type w'}
variable [AddCommGroup V'ℤ] [AddCommGroup V'ℚ] [Module ℚ V'ℚ] [AddCommGroup V'ℂ] [Module ℂ V'ℂ]
variable {ι'ℚ : V'ℤ →ₗ[ℤ] V'ℚ} {ι'ℂ : V'ℤ →ₗ[ℤ] V'ℂ}
variable {h'ℚ : IsBaseChange ℚ ι'ℚ} {h'ℂ : IsBaseChange ℂ ι'ℂ}
variable {source : MixedHodgeStructure hℚ hℂ} {target : MixedHodgeStructure h'ℚ h'ℂ}

/-- A morphism of mixed Hodge structures preserves the conjugate Hodge filtration, because its
complex action commutes with lattice-induced conjugation. -/
theorem map_conjF_le (f : Hom source target) (q : ℤ) :
    (source.conjF q).map f.toLinearMap ≤ target.conjF q := by
  rintro _ ⟨x, hx, rfl⟩
  refine (target.mem_conjF_iff q _).2 ?_
  rw [← f.commutes_conj x]
  exact f.map_F_le q ⟨latticeConj hℂ x, (source.mem_conjF_iff q x).1 hx, rfl⟩

/-- **Functoriality of Deligne's bigrading.** A morphism of mixed Hodge structures carries the
bidegree `(p,q)` part of the source into the bidegree `(p,q)` part of the target. -/
theorem map_deligneSplitting_le (f : Hom source target) (p q : ℤ) :
    (source.deligneSplitting p q).map f.toLinearMap ≤ target.deligneSplitting p q := by
  rw [deligneSplitting_def, deligneSplitting_def]
  refine (Submodule.map_inf_le _).trans (inf_le_inf ?_ ?_)
  · exact (Submodule.map_inf_le _).trans
      (inf_le_inf (f.map_F_le p) (f.map_WC_le (p + q)))
  · rw [Submodule.map_sup, Submodule.map_iSup]
    refine sup_le_sup ((Submodule.map_inf_le _).trans
      (inf_le_inf (f.map_conjF_le q) (f.map_WC_le (p + q)))) (iSup_mono fun i ↦ ?_)
    exact (Submodule.map_inf_le _).trans
      (inf_le_inf (f.map_conjF_le _) (f.map_WC_le _))

/-- Elementwise form of the functoriality of Deligne's bigrading. -/
theorem map_mem_deligneSplitting (f : Hom source target) (p q : ℤ) {x : Vℂ}
    (hx : x ∈ source.deligneSplitting p q) : f x ∈ target.deligneSplitting p q :=
  f.map_deligneSplitting_le p q ⟨x, hx, rfl⟩

end MixedHodgeStructure.Hom

/-! ### The bigrading of a pure Hodge structure -/

namespace MixedHodgeStructure

variable (hℚ hℂ) {n : ℤ}

/-- The complexified weight filtration of a pure structure viewed as mixed is everything from the
weight on. -/
theorem ofPure_WC_of_le (hs : HodgeStructure hℂ n) {k : ℤ} (h : n ≤ k) :
    (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).WC k = ⊤ := by
  rw [WC_def, ofPure_WQ, concentratedWeightFiltration_of_le h, rationalToComplexSubmodule_top]

/-- The complexified weight filtration of a pure structure viewed as mixed vanishes below the
weight. -/
theorem ofPure_WC_of_lt (hs : HodgeStructure hℂ n) {k : ℤ} (h : k < n) :
    (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).WC k = ⊥ := by
  rw [WC_def, ofPure_WQ, concentratedWeightFiltration_of_lt h, rationalToComplexSubmodule_bot]

/-- The conjugate Hodge filtration of a pure structure viewed as mixed is the one of the pure
structure. -/
theorem ofPure_conjF (hs : HodgeStructure hℂ n) :
    (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).conjF = hs.conjF := by
  funext p
  rw [conjF_def, ofPure_F, HodgeStructureOn.conjF_def, latticeConjugation_toLinearMap]

/-- **On the antidiagonal, Deligne's bigrading of a pure Hodge structure is its Hodge
decomposition.** All the tail terms of the formula sit in weight strictly below `n`, hence vanish,
and the remaining intersection `F^p ⊓ conj F^{n-p}` is the Hodge component. -/
theorem ofPure_deligneSplitting_of_add_eq (hs : HodgeStructure hℂ n) {p q : ℤ} (hpq : p + q = n) :
    (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).deligneSplitting p q = hs.piece p := by
  have htail : ∀ i : ℕ,
      (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).conjF (q - 1 - i) ⊓
        (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).WC (p + q - 2 - i) = ⊥ := fun i ↦ by
    rw [ofPure_WC_of_lt hℚ hℂ hs (by omega), inf_bot_eq]
  rw [deligneSplitting_def, ofPure_WC_of_le hℚ hℂ hs hpq.ge]
  simp only [htail, iSup_bot, sup_bot_eq, inf_top_eq]
  rw [ofPure_conjF, ofPure_F, HodgeStructureOn.piece_def, show n - p = q by omega]

/-- **Off the antidiagonal, Deligne's bigrading of a pure Hodge structure vanishes.** Below the
weight the whole weight filtration is zero; above it, the second factor of the formula is contained
in `conj F^{n+1-p}`, which is complementary to `F^p` by opposedness. -/
theorem ofPure_deligneSplitting_of_add_ne (hs : HodgeStructure hℂ n) {p q : ℤ} (hpq : p + q ≠ n) :
    (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).deligneSplitting p q = ⊥ := by
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · rw [deligneSplitting_def, ofPure_WC_of_lt hℚ hℂ hs hlt, inf_bot_eq, bot_inf_eq]
  · refine le_bot_iff.1 ?_
    have hsecond :
        ((MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).conjF q ⊓
            (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).WC (p + q)) ⊔
          (⨆ i : ℕ, (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).conjF (q - 1 - i) ⊓
            (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).WC (p + q - 2 - i)) ≤
          hs.conjF (n + 1 - p) := by
      refine sup_le (inf_le_left.trans ?_) (iSup_le fun i ↦ ?_)
      · rw [ofPure_conjF]
        exact hs.conjF_antitone (by omega)
      · rcases le_or_gt n (p + q - 2 - (i : ℤ)) with hi | hi
        · refine inf_le_left.trans ?_
          rw [ofPure_conjF]
          exact hs.conjF_antitone (by omega)
        · rw [ofPure_WC_of_lt hℚ hℂ hs hi, inf_bot_eq]
          exact bot_le
    rw [deligneSplitting_def]
    refine (inf_le_inf inf_le_left hsecond).trans ?_
    rw [ofPure_F]
    exact (hs.isCompl_F_conjF p).disjoint.le_bot

/-- **The bigrading of a pure Hodge structure is an internal direct sum**: Deligne's formula
recovers the Hodge decomposition, placed on the antidiagonal `p + q = n` of the bigrading. -/
theorem isInternal_ofPure_deligneSplitting (hs : HodgeStructure hℂ n) :
    DirectSum.IsInternal fun pq : ℤ × ℤ ↦
      (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).deligneSplitting pq.1 pq.2 := by
  classical
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rintro ⟨p, q⟩
    rcases eq_or_ne (p + q) n with hn | hn
    · refine Disjoint.mono_left (ofPure_deligneSplitting_of_add_eq hℚ hℂ hs hn).le
        ((hs.piece_iSupIndep p).mono_right (iSup₂_le ?_))
      rintro ⟨r, s⟩ hrs
      rcases eq_or_ne (r + s) n with hrn | hrn
      · refine (ofPure_deligneSplitting_of_add_eq hℚ hℂ hs hrn).le.trans ?_
        refine le_iSup₂_of_le r (fun hr ↦ hrs ?_) le_rfl
        rw [Prod.mk.injEq]
        omega
      · exact (ofPure_deligneSplitting_of_add_ne hℚ hℂ hs hrn).le.trans bot_le
    · exact Disjoint.mono_left (ofPure_deligneSplitting_of_add_ne hℚ hℂ hs hn).le
        disjoint_bot_left
  · refine top_unique ?_
    rw [← hs.iSup_piece_eq_top]
    refine iSup_le fun p ↦ ?_
    refine (ofPure_deligneSplitting_of_add_eq (Vℚ := Vℚ) hℚ hℂ hs
      (p := p) (q := n - p) (by omega)).ge.trans ?_
    exact le_iSup (fun pq : ℤ × ℤ ↦
      (MixedHodgeStructure.ofPure (Vℚ := Vℚ) hℚ hℂ hs).deligneSplitting pq.1 pq.2) (p, n - p)

end MixedHodgeStructure

/-! ### The bigrading of a Tate structure -/

/-- The bigrading of the Tate structure `ℤ(m)` is the whole line in bidegree `(-m,-m)`. -/
theorem tateMixed_deligneSplitting_neg_neg (m : ℤ) :
    (tateMixed m).deligneSplitting (-m) (-m) = ⊤ := by
  rw [tateMixed_eq_ofPure,
    MixedHodgeStructure.ofPure_deligneSplitting_of_add_eq _ _ (tate m) (by ring), tate_piece]
  simp

/-- The bigrading of the Tate structure `ℤ(m)` vanishes in every other bidegree. -/
theorem tateMixed_deligneSplitting_eq_bot {m p q : ℤ} (h : ¬(p = -m ∧ q = -m)) :
    (tateMixed m).deligneSplitting p q = ⊥ := by
  rw [tateMixed_eq_ofPure]
  rcases eq_or_ne (p + q) (-2 * m) with hpq | hpq
  · have hp : p ≠ -m := by
      rintro rfl
      exact h ⟨rfl, by omega⟩
    rw [MixedHodgeStructure.ofPure_deligneSplitting_of_add_eq _ _ (tate m) hpq, tate_piece]
    simp [hp]
  · exact MixedHodgeStructure.ofPure_deligneSplitting_of_add_ne _ _ (tate m) hpq

end TauCeti.Hodge
