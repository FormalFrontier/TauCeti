/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.DeligneSplitting
public import TauCeti.Geometry.Hodge.Mixed.Graded

/-!
# Deligne's bigrading is an internal direct sum

`TauCeti/Geometry/Hodge/Mixed/DeligneSplitting.lean` builds the bigrading `I^{p,q}` of a mixed
Hodge structure from Deligne's closed formula and proves what follows from the formula alone. This
file proves Deligne's theorem about it: the pieces `I^{p,q}` form an internal direct sum of the
complex vector space, and the complexified weight step `W_k` is exactly the supremum of the pieces
of total degree at most `k`,

`W_k = ⨆_{p + q ≤ k} I^{p,q}`.

Everything runs through the comparison of `I^{p,q}` with the pure Hodge structure carried by the
graded piece `gr^W_{p+q}`, built in `TauCeti/Geometry/Hodge/Mixed/Graded.lean`. Three facts drive
it.

* `I^{p,q}` meets `W_{p+q-1}` trivially. A vector of `I^{p,q} ∩ W_m` with `m < p + q` lies in
  `F^p`, and lies in `conj F^{m+1-p}` modulo `W_{m-1}`; its class in `gr^W_m` therefore lies in
  two complementary steps of a pure Hodge structure of weight `m` and so vanishes, pushing the
  vector down to `W_{m-1}`. Iterating exhausts the weight filtration downwards.
* `I^{p,q}` covers the Hodge component `H^{p,q}` of `gr^W_{p+q}`, granted that `W_{p+q-1}` is
  already spanned by bigrading pieces. A representative of a class in `H^{p,q}` lies in `F^p` and
  is congruent modulo `W_{p+q-1}` to a vector of `conj F^q`; splitting the error term into the
  bigrading pieces whose first index is at least `p` — which lie in `F^p` — and those whose first
  index is smaller — which lie in the second factor of Deligne's formula — corrects the
  representative into `I^{p,q}` without changing its class. Running this against the Hodge
  decomposition of `gr^W_k` and inducting upwards on `k` from a weight step where the filtration
  vanishes gives the recovery of `W`, and with it that the bigrading spans.
* A weight step meets the pieces of larger total degree trivially. This is a descending induction
  on the weight which peels off one total degree at a time, and independence follows: a vector of
  `I^{p,q}` lying in the sum of all the other pieces first loses its part of larger total degree,
  and what is left has a class in `gr^W_{p+q}` lying both in `H^{p,q}` and in the complementary
  `conj F^{q+1} ⊔ F^{p+1}`, hence vanishing.

What remains of Deligne's theory after this file: the recovery `F^p = ⨆_{p' ≥ p} I^{p',q}` of the
Hodge filtration, the conjugation symmetry `I^{p,q} ≡ conj I^{q,p}` modulo strictly lower
bidegree, and the strictness of a morphism of mixed Hodge structures.

## Main declarations

* `TauCeti.Hodge.MixedHodgeStructure.deligneSplitting_disjoint_WC`: `I^{p,q}` meets `W_{p+q-1}`
  trivially.
* `TauCeti.Hodge.MixedHodgeStructure.WC_eq_iSup_deligneSplitting`: the recovery
  `W_k = ⨆_{p+q ≤ k} I^{p,q}` of the weight filtration.
* `TauCeti.Hodge.MixedHodgeStructure.map_deligneSplitting_eq_piece`: the image of `I^{p,q}` in
  `gr^W_{p+q}` is the Hodge component `H^{p,q}`.
* `TauCeti.Hodge.MixedHodgeStructure.iSup_deligneSplittingFamily_eq_top`: the bigrading spans.
* `TauCeti.Hodge.MixedHodgeStructure.iSupIndep_deligneSplittingFamily`: the pieces are
  independent.
* `TauCeti.Hodge.MixedHodgeStructure.isInternal_deligneSplittingFamily`: **Deligne's theorem**,
  the bigrading is an internal direct sum.

## References

Deligne, *Théorie de Hodge II*, 1.2.8 and 1.2.10; Peters–Steenbrink, *Mixed Hodge Structures*,
Lemma-Definition 3.4.
-/

public section

namespace TauCeti.Hodge

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}

namespace MixedHodgeStructure

variable (mhs : MixedHodgeStructure hℚ hℂ)

/-! ### A bigrading piece meets the lower weight steps trivially -/

/-- A vector of `I^{p,q}` lying in a weight step *below* its total degree already lies one step
further down.

Its class in `gr^W_m` lies both in the `p`-th step of the induced Hodge filtration and in the
`(m+1-p)`-th step of the conjugate one — the second because Deligne's formula puts `I^{p,q}` in
`conj F^{m+1-p}` modulo `W_{m-1}` — and those two steps of a pure Hodge structure of weight `m`
are complementary. -/
theorem deligneSplitting_inf_WC_le (p q m : ℤ) (hm : m < p + q) :
    mhs.deligneSplitting p q ⊓ mhs.WC m ≤ mhs.WC (m - 1) := by
  rintro x ⟨hxI, hxW⟩
  have hF : x ∈ mhs.F p := mhs.deligneSplitting_le_F p q hxI
  have hconj : x ∈ mhs.conjF (m + 1 - p) ⊔ mhs.WC (m - 1) := by
    have hx := mhs.deligneSplitting_le_conjF_sub_sup_WC p q (p + q - m - 1) (by omega) hxI
    have h₁ : q - (p + q - m - 1) = m + 1 - p := by omega
    have h₂ : p + q - (p + q - m - 1) - 2 = m - 1 := by omega
    rwa [h₁, h₂] at hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hconj
  have hax : a - x = -b := by rw [← hab]; abel
  have haW : a ∈ mhs.WC m := by
    have hxa : a = x - b := by rw [← hab]; abel
    exact hxa ▸ Submodule.sub_mem _ hxW (mhs.WC_monotone (by omega) hb)
  have hmk : (Submodule.Quotient.mk (⟨a, haW⟩ : mhs.WC m) : weightGradedComplex mhs.WC m) =
      Submodule.Quotient.mk (⟨x, hxW⟩ : mhs.WC m) := by
    refine (Submodule.Quotient.eq _).2 (Submodule.mem_comap.2 ?_)
    -- Unfold the subtype subtraction at the quotient boundary to ambient membership in `WC`.
    change a - x ∈ mhs.WC (m - 1)
    exact hax ▸ Submodule.neg_mem _ hb
  have hu₁ : Submodule.Quotient.mk (⟨x, hxW⟩ : mhs.WC m) ∈
      (mhs.complexGradedHodgeStructure m).F p := by
    rw [complexGradedHodgeStructure_F, mem_complexGradedF_iff]
    exact ⟨⟨x, hxW⟩, hF, rfl⟩
  have hu₂ : Submodule.Quotient.mk (⟨x, hxW⟩ : mhs.WC m) ∈
      (mhs.complexGradedHodgeStructure m).conjF (m + 1 - p) := by
    rw [complexGradedHodgeStructure_conjF, mem_complexGradedF_iff]
    exact ⟨⟨a, haW⟩, by rwa [← conjF_def], hmk⟩
  have hzero := ((mhs.complexGradedHodgeStructure m).isCompl_F_conjF p).disjoint.le_bot ⟨hu₁, hu₂⟩
  rw [Submodule.mem_bot] at hzero
  exact Submodule.mem_comap.1
    ((Submodule.Quotient.mk_eq_zero ((mhs.WC (m - 1)).submoduleOf (mhs.WC m))).1 hzero)

/-- **A bigrading piece meets the weight step below its total degree trivially.** -/
theorem deligneSplitting_disjoint_WC (p q : ℤ) :
    Disjoint (mhs.deligneSplitting p q) (mhs.WC (p + q - 1)) := by
  obtain ⟨k₀, hk₀⟩ := mhs.WC_bot
  have key : ∀ n : ℕ, mhs.deligneSplitting p q ⊓ mhs.WC (p + q - 1) ≤
      mhs.WC (p + q - 1 - (n : ℤ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep : p + q - 1 - ((n + 1 : ℕ) : ℤ) = p + q - 1 - (n : ℤ) - 1 := by push_cast; ring
      rw [hstep]
      exact (le_inf inf_le_left ih).trans
        (mhs.deligneSplitting_inf_WC_le p q (p + q - 1 - (n : ℤ)) (by omega))
  rw [disjoint_iff, ← le_bot_iff]
  refine (key (p + q - 1 - k₀).toNat).trans ?_
  rw [← hk₀]
  exact mhs.WC_monotone (by omega)

/-- Where the Hodge filtration vanishes in the *second* index the bigrading vanishes: `I^{p,q}`
then lies in `W_{p+q-1}`, which it meets trivially. -/
theorem deligneSplitting_eq_bot_of_F_eq_bot_le {b : ℤ} (hb : mhs.F b = ⊥) {p q : ℤ} (hbq : b ≤ q) :
    mhs.deligneSplitting p q = ⊥ := by
  refine (mhs.deligneSplitting_disjoint_WC p q).eq_bot_of_le ?_
  refine (mhs.deligneSplitting_le_conjF_sup_WC p q).trans (sup_le ?_ (mhs.WC_monotone (by omega)))
  exact ((mhs.conjF_antitone hbq).trans_eq (mhs.conjF_eq_bot_of_F_eq_bot hb)).trans bot_le

/-- Above a weight index at which the weight filtration is everything the bigrading vanishes. -/
theorem deligneSplitting_eq_bot_of_WC_eq_top {k : ℤ} (hk : mhs.WC k = ⊤) {p q : ℤ}
    (hkpq : k < p + q) : mhs.deligneSplitting p q = ⊥ :=
  (mhs.deligneSplitting_disjoint_WC p q).eq_bot_of_le
    (le_top.trans (hk ▸ mhs.WC_monotone (by omega : k ≤ p + q - 1)))

/-! ### The bigrading covers the Hodge components of the graded pieces -/

/-- A bigrading piece whose first index is smaller than `p` and whose total degree is smaller than
`p + q` lies in the second factor of Deligne's formula for `I^{p,q}`.

This is the bookkeeping that makes the correction step below work: the terms of the formula for
`I^{p',q'}` all match, index for index, terms of the formula for `I^{p,q}` once `p' < p`. -/
private theorem deligneSplitting_le_sup_of_lt {p q p' q' : ℤ} (hp : p' < p)
    (hd : p' + q' < p + q) :
    mhs.deligneSplitting p' q' ≤
      (mhs.conjF q ⊓ mhs.WC (p + q)) ⊔
        ⨆ j : ℕ, mhs.conjF (q - (j : ℤ) - 1) ⊓ mhs.WC (p + q - (j : ℤ) - 2) := by
  rw [deligneSplitting_def]
  refine inf_le_right.trans (sup_le ?_ (iSup_le fun i ↦ ?_))
  · rcases eq_or_lt_of_le (by omega : p' + q' ≤ p + q - 1) with h | h
    · exact le_sup_of_le_left
        (inf_le_inf (mhs.conjF_antitone (by omega)) (mhs.WC_monotone (by omega)))
    · refine le_sup_of_le_right (le_iSup_of_le (p + q - 2 - (p' + q')).toNat ?_)
      have hcast : (((p + q - 2 - (p' + q')).toNat : ℕ) : ℤ) = p + q - 2 - (p' + q') := by omega
      rw [hcast]
      exact inf_le_inf (mhs.conjF_antitone (by omega)) (mhs.WC_monotone (by omega))
  · refine le_sup_of_le_right (le_iSup_of_le (i + (p + q - (p' + q')).toNat) ?_)
    have hcast : ((i + (p + q - (p' + q')).toNat : ℕ) : ℤ) = (i : ℤ) + (p + q - (p' + q')) := by
      push_cast
      omega
    rw [hcast]
    exact inf_le_inf (mhs.conjF_antitone (by omega)) (mhs.WC_monotone (by omega))

/-- **Deligne's bigrading covers the Hodge components of the graded pieces.** Granted that the
weight step `W_{k-1}` is already spanned by bigrading pieces, every class of the Hodge component
`H^{p,k-p}` of `gr^W_k` is represented by a vector of `I^{p,k-p}`.

A representative is corrected by subtracting the part of its error term supported in first indices
at least `p`, which lies in `F^p` and in `W_{k-1}`, so that neither membership in `F^p` nor the
class in `gr^W_k` changes; what is left of the error term lies in the second factor of Deligne's
formula. -/
private theorem piece_le_map_deligneSplitting {k : ℤ}
    (hW : mhs.WC (k - 1) ≤
      ⨆ (rs : ℤ × ℤ) (_ : rs.1 + rs.2 ≤ k - 1), mhs.deligneSplitting rs.1 rs.2)
    (p : ℤ) :
    (mhs.complexGradedHodgeStructure k).piece p ≤
      ((mhs.deligneSplitting p (k - p)).submoduleOf (mhs.WC k)).map
        ((mhs.WC (k - 1)).submoduleOf (mhs.WC k)).mkQ := by
  intro u hu
  obtain ⟨y, hyF, hyconj, hyu⟩ := (mhs.mem_complexGradedHodgeStructure_piece_iff k p u).1 hu
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hyconj
  have hsplit : mhs.WC (k - 1) ≤ (mhs.F p ⊓ mhs.WC (k - 1)) ⊔
      ((mhs.conjF (k - p) ⊓ mhs.WC (p + (k - p))) ⊔
        ⨆ j : ℕ, mhs.conjF (k - p - (j : ℤ) - 1) ⊓ mhs.WC (p + (k - p) - (j : ℤ) - 2)) := by
    refine hW.trans (iSup₂_le fun rs hrs ↦ ?_)
    rcases le_or_gt p rs.1 with h | h
    · exact le_sup_of_le_left (le_inf ((mhs.deligneSplitting_le_F _ _).trans (mhs.F_antitone h))
        ((mhs.deligneSplitting_le_WC _ _).trans (mhs.WC_monotone hrs)))
    · exact le_sup_of_le_right (mhs.deligneSplitting_le_sup_of_lt h (by omega))
  obtain ⟨c, hc, e, he, hce⟩ := Submodule.mem_sup.1 (hsplit hb)
  have hkp : p + (k - p) = k := by ring
  have haW : a ∈ mhs.WC (p + (k - p)) := by
    have hya : a = (y : Vℂ) - b := by rw [← hab]; abel
    rw [hkp, hya]
    exact Submodule.sub_mem _ y.2 (mhs.WC_monotone (by omega) hb)
  have hyc : (y : Vℂ) - c = a + e := by rw [← hab, ← hce]; abel
  have hxW : (y : Vℂ) - c ∈ mhs.WC k :=
    Submodule.sub_mem _ y.2 (mhs.WC_monotone (by omega) hc.2)
  have hxW' : (y : Vℂ) - c ∈ mhs.WC (p + (k - p)) := by rw [hkp]; exact hxW
  have hx : (y : Vℂ) - c ∈ mhs.deligneSplitting p (k - p) := by
    rw [mem_deligneSplitting_iff]
    refine ⟨Submodule.sub_mem _ hyF hc.1, hxW', ?_⟩
    rw [hyc]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left ⟨by rwa [← conjF_def] at ha, haW⟩) he
  refine ⟨⟨(y : Vℂ) - c, hxW⟩, hx, ?_⟩
  rw [Submodule.mkQ_apply, ← hyu]
  refine (Submodule.Quotient.eq _).2 (Submodule.mem_comap.2 ?_)
  -- Unfold the quotient representatives and `submoduleOf` membership back in the ambient space.
  change (y : Vℂ) - c - (y : Vℂ) ∈ mhs.WC (k - 1)
  have hneg : (y : Vℂ) - c - (y : Vℂ) = -c := by abel
  exact hneg ▸ Submodule.neg_mem _ hc.2

/-! ### The recovery of the weight filtration -/

/-- **Deligne's bigrading recovers the weight filtration**: the complexified weight step `W_k` is
the supremum of the bigrading pieces of total degree at most `k`.

One inclusion is the containment `I^{p,q} ≤ W_{p+q}`. The other is an induction upwards on `k`
starting from a step where the weight filtration vanishes: the pieces of total degree exactly `k`
cover the Hodge components of `gr^W_k`, hence all of `gr^W_k`, so together with `W_{k-1}` they
span `W_k`. -/
theorem WC_eq_iSup_deligneSplitting (k : ℤ) :
    mhs.WC k = ⨆ (rs : ℤ × ℤ) (_ : rs.1 + rs.2 ≤ k), mhs.deligneSplitting rs.1 rs.2 := by
  refine le_antisymm ?_ (iSup₂_le fun rs hrs ↦
    (mhs.deligneSplitting_le_WC rs.1 rs.2).trans (mhs.WC_monotone hrs))
  obtain ⟨k₀, hk₀⟩ := mhs.WC_bot
  have key : ∀ m : ℤ, k₀ ≤ m → mhs.WC m ≤
      ⨆ (rs : ℤ × ℤ) (_ : rs.1 + rs.2 ≤ m), mhs.deligneSplitting rs.1 rs.2 := by
    refine Int.leInduction (by rw [hk₀]; exact bot_le) ?_
    intro m _ ih
    have hm : m + 1 - 1 = m := by ring
    have hW : mhs.WC (m + 1 - 1) ≤
        ⨆ (rs : ℤ × ℤ) (_ : rs.1 + rs.2 ≤ m + 1 - 1), mhs.deligneSplitting rs.1 rs.2 := by
      rw [hm]; exact ih
    have htop : ((⨆ p : ℤ,
          (mhs.deligneSplitting p (m + 1 - p)).submoduleOf (mhs.WC (m + 1))).map
        ((mhs.WC (m + 1 - 1)).submoduleOf (mhs.WC (m + 1))).mkQ) = ⊤ := by
      refine top_unique ?_
      rw [← (mhs.complexGradedHodgeStructure (m + 1)).iSup_piece_eq_top, Submodule.map_iSup]
      exact iSup_mono fun p ↦ mhs.piece_le_map_deligneSplitting hW p
    rw [Submodule.map_mkQ_eq_top] at htop
    have hmap := congrArg (Submodule.map (mhs.WC (m + 1)).subtype) htop
    rw [Submodule.map_sup, Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype] at hmap
    simp only [Submodule.submoduleOf, Submodule.map_comap_subtype] at hmap
    rw [← hmap, hm, inf_of_le_right (mhs.WC_monotone (by omega : m ≤ m + 1))]
    refine sup_le (ih.trans (iSup₂_mono' fun rs hrs ↦ ⟨rs, by omega, le_rfl⟩))
      (iSup_le fun p ↦ ?_)
    exact inf_le_right.trans (le_iSup₂_of_le (p, m + 1 - p) (by omega) le_rfl)
  rcases le_or_gt k₀ k with h | h
  · exact key k h
  · exact (mhs.WC_monotone h.le).trans (by rw [hk₀]; exact bot_le)

private theorem map_deligneSplitting_le_piece (p q : ℤ) :
    ((mhs.deligneSplitting p q).submoduleOf (mhs.WC (p + q))).map
        ((mhs.WC (p + q - 1)).submoduleOf (mhs.WC (p + q))).mkQ ≤
      (mhs.complexGradedHodgeStructure (p + q)).piece p := by
  rintro _ ⟨x, hx, rfl⟩
  have hxI : (x : Vℂ) ∈ mhs.deligneSplitting p q := hx
  refine mhs.mk_mem_complexGradedHodgeStructure_piece (p + q) p x
    (mhs.deligneSplitting_le_F p q hxI) ?_
  have hconj := mhs.deligneSplitting_le_conjF_sup_WC p q hxI
  have hmono : mhs.conjF q ⊔ mhs.WC (p + q - 2) ≤
      mhs.conjF q ⊔ mhs.WC (p + q - 1) :=
    sup_le le_sup_left (le_sup_of_le_right (mhs.WC_monotone (by omega)))
  simpa only [conjF_def, add_sub_cancel_left] using hmono hconj

/-- The image of the Deligne bigrading piece `I^{p,q}` in `gr^W_{p+q}` is exactly the pure Hodge
component `H^{p,q}` of that graded piece. -/
theorem map_deligneSplitting_eq_piece (p q : ℤ) :
    ((mhs.deligneSplitting p q).submoduleOf (mhs.WC (p + q))).map
        ((mhs.WC (p + q - 1)).submoduleOf (mhs.WC (p + q))).mkQ =
      (mhs.complexGradedHodgeStructure (p + q)).piece p := by
  apply le_antisymm
  · exact mhs.map_deligneSplitting_le_piece p q
  · have hW := (mhs.WC_eq_iSup_deligneSplitting (p + q - 1)).le
    simpa only [add_sub_cancel_left] using mhs.piece_le_map_deligneSplitting hW p

/-- **Deligne's bigrading spans**: the supremum of all the pieces `I^{p,q}` is the whole complex
vector space. -/
theorem iSup_deligneSplittingFamily_eq_top :
    ⨆ pq : ℤ × ℤ, mhs.deligneSplittingFamily pq = ⊤ := by
  obtain ⟨k, hk⟩ := mhs.WC_top
  refine top_unique ?_
  rw [← hk, mhs.WC_eq_iSup_deligneSplitting k]
  exact iSup₂_le fun rs _ ↦ le_iSup_of_le rs (le_of_eq (mhs.deligneSplittingFamily_apply rs).symm)

/-! ### Independence of the bigrading pieces -/

/-- The bigrading pieces of a fixed total degree `m` meet the weight step `W_{m-1}` trivially.

Descending induction on the first index: a vector of the sum lying in `W_{m-1}` splits as `u + v`
with `u ∈ I^{p,m-p}` and `v` in the pieces of larger first index, hence in `F^{p+1}`; the class of
`u` in `gr^W_m` then lies in the Hodge component `H^{p,m-p}` and in `F^{p+1}`, which are disjoint,
so `u` lies in `W_{m-1}` and therefore vanishes. -/
theorem iSup_deligneSplitting_disjoint_WC (m : ℤ) :
    Disjoint (⨆ p : ℤ, mhs.deligneSplitting p (m - p)) (mhs.WC (m - 1)) := by
  obtain ⟨b, hb⟩ := mhs.F_bot
  have key : ∀ p : ℤ, p ≤ b → Disjoint
      (⨆ r, ⨆ (_ : p ≤ r), mhs.deligneSplitting r (m - r)) (mhs.WC (m - 1)) := by
    refine Int.leInductionDown ?_ ?_
    · refine disjoint_bot_left.mono_left (iSup₂_le fun r hr ↦ ?_)
      exact le_of_eq (mhs.deligneSplitting_eq_bot_of_F_eq_bot hb hr)
    · intro p _ ih
      rw [disjoint_iff, ← le_bot_iff]
      rintro x ⟨hx1, hx2⟩
      have hsplit : (⨆ r, ⨆ (_ : p - 1 ≤ r), mhs.deligneSplitting r (m - r)) ≤
          mhs.deligneSplitting (p - 1) (m - (p - 1)) ⊔
            ⨆ r, ⨆ (_ : p ≤ r), mhs.deligneSplitting r (m - r) := by
        refine iSup₂_le fun r hr ↦ ?_
        rcases eq_or_lt_of_le hr with h | h
        · exact h ▸ le_sup_left
        · exact le_sup_of_le_right (le_iSup₂_of_le r (by omega) le_rfl)
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsplit hx1)
      have huW : u ∈ mhs.WC m := by
        have hle := mhs.deligneSplitting_le_WC (p - 1) (m - (p - 1)) hu
        -- Normalize the total degree of `I^{p-1,m-(p-1)}` to the ambient weight `m`.
        rwa [show p - 1 + (m - (p - 1)) = m by ring] at hle
      have hvW : v ∈ mhs.WC m := by
        have hvu : v = x - u := by rw [← huv]; abel
        rw [hvu]
        exact Submodule.sub_mem _ (mhs.WC_monotone (by omega) hx2) huW
      have hvF : v ∈ mhs.F p :=
        (iSup₂_le fun r hr ↦ (mhs.deligneSplitting_le_F r (m - r)).trans (mhs.F_antitone hr)) hv
      have hclassu : Submodule.Quotient.mk (⟨u, huW⟩ : mhs.WC m) ∈
          (mhs.complexGradedHodgeStructure m).piece (p - 1) := by
        refine mhs.mk_mem_complexGradedHodgeStructure_piece m (p - 1) ⟨u, huW⟩
          (mhs.deligneSplitting_le_F _ _ hu) ?_
        have hle := mhs.deligneSplitting_le_conjF_sup_WC (p - 1) (m - (p - 1)) hu
        rw [conjF_def] at hle
        refine (sup_le le_sup_left (le_sup_of_le_right (mhs.WC_monotone ?_))) hle
        omega
      have hclassv : Submodule.Quotient.mk (⟨v, hvW⟩ : mhs.WC m) ∈
          (mhs.complexGradedHodgeStructure m).F (p - 1 + 1) := by
        rw [complexGradedHodgeStructure_F, mem_complexGradedF_iff]
        -- Normalize the successor filtration index before using `hvF : v ∈ F p`.
        exact ⟨⟨v, hvW⟩, by rwa [show p - 1 + 1 = p by ring], rfl⟩
      have huv' : (Submodule.Quotient.mk (⟨u, huW⟩ : mhs.WC m) :
            weightGradedComplex mhs.WC m) =
          -Submodule.Quotient.mk (⟨v, hvW⟩ : mhs.WC m) := by
        rw [eq_neg_iff_add_eq_zero, ← Submodule.Quotient.mk_add]
        refine (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_comap.2 ?_)
        -- Unfold addition of quotient representatives to ambient membership in the lower step.
        change u + v ∈ mhs.WC (m - 1)
        rw [huv]
        exact hx2
      have hzero := ((mhs.complexGradedHodgeStructure m).isCompl_piece_conjF_sup_F
        (p - 1)).disjoint.le_bot ⟨hclassu, huv' ▸ Submodule.neg_mem _
          (Submodule.mem_sup_right hclassv)⟩
      rw [Submodule.mem_bot] at hzero
      have huWlow : u ∈ mhs.WC (m - 1) := Submodule.mem_comap.1
        ((Submodule.Quotient.mk_eq_zero ((mhs.WC (m - 1)).submoduleOf (mhs.WC m))).1 hzero)
      have hu0 : u = 0 := by
        have := (mhs.deligneSplitting_disjoint_WC (p - 1) (m - (p - 1))).le_bot
          -- Normalize the lower weight step for the total degree of the selected piece.
          ⟨hu, by rwa [show p - 1 + (m - (p - 1)) - 1 = m - 1 by ring]⟩
        simpa using this
      have hxv : x = v := by rw [← huv, hu0, zero_add]
      exact ih.le_bot ⟨hxv ▸ hv, hx2⟩
  refine (key (min b (m - b)) (min_le_left _ _)).mono_left (iSup_le fun p ↦ ?_)
  rcases le_or_gt (min b (m - b)) p with h | h
  · exact le_iSup₂_of_le p h le_rfl
  · rw [mhs.deligneSplitting_eq_bot_of_F_eq_bot_le hb (by omega : b ≤ m - p)]
    exact bot_le

/-- Above a weight index at which the weight filtration is everything, all bigrading pieces of
larger total degree vanish. -/
theorem iSup_deligneSplitting_eq_bot_of_WC_eq_top {M : ℤ} (hM : mhs.WC M = ⊤) {k : ℤ}
    (hk : M ≤ k) :
    (⨆ (rs : ℤ × ℤ) (_ : k < rs.1 + rs.2), mhs.deligneSplitting rs.1 rs.2) = ⊥ :=
  le_bot_iff.1 (iSup₂_le fun _ hrs ↦
    le_of_eq (mhs.deligneSplitting_eq_bot_of_WC_eq_top hM (by omega)))

/-- **A weight step meets the bigrading pieces of larger total degree trivially.** Descending
induction on the weight peels off one total degree at a time, using that the pieces of total
degree `k` meet `W_{k-1}` trivially. -/
theorem WC_disjoint_iSup_deligneSplitting (k : ℤ) :
    Disjoint (mhs.WC k)
      (⨆ (rs : ℤ × ℤ) (_ : k < rs.1 + rs.2), mhs.deligneSplitting rs.1 rs.2) := by
  obtain ⟨M, hM⟩ := mhs.WC_top
  have key : ∀ n : ℤ, n ≤ M → Disjoint (mhs.WC n)
      (⨆ (rs : ℤ × ℤ) (_ : n < rs.1 + rs.2), mhs.deligneSplitting rs.1 rs.2) := by
    refine Int.leInductionDown ?_ ?_
    · rw [mhs.iSup_deligneSplitting_eq_bot_of_WC_eq_top hM le_rfl]
      exact disjoint_bot_right
    · intro n _ ih
      rw [disjoint_iff, ← le_bot_iff]
      rintro x ⟨hx1, hx2⟩
      have hsplit : (⨆ (rs : ℤ × ℤ) (_ : n - 1 < rs.1 + rs.2), mhs.deligneSplitting rs.1 rs.2) ≤
          (⨆ p : ℤ, mhs.deligneSplitting p (n - p)) ⊔
            ⨆ (rs : ℤ × ℤ) (_ : n < rs.1 + rs.2), mhs.deligneSplitting rs.1 rs.2 := by
        refine iSup₂_le fun rs hrs ↦ ?_
        rcases eq_or_lt_of_le (by omega : n ≤ rs.1 + rs.2) with h | h
        · refine le_sup_of_le_left (le_iSup_of_le rs.1 (le_of_eq ?_))
          congr 1
          omega
        · exact le_sup_of_le_right (le_iSup₂_of_le rs h le_rfl)
      obtain ⟨g, hg, y, hy, hgy⟩ := Submodule.mem_sup.1 (hsplit hx2)
      have hgW : g ∈ mhs.WC n :=
        (iSup_le fun p ↦ (mhs.deligneSplitting_le_WC p (n - p)).trans
          (mhs.WC_monotone (by omega))) hg
      have hyW : y ∈ mhs.WC n := by
        have hyx : y = x - g := by rw [← hgy]; abel
        rw [hyx]
        exact Submodule.sub_mem _ (mhs.WC_monotone (by omega) hx1) hgW
      have hy0 : y = 0 := by simpa using ih.le_bot ⟨hyW, hy⟩
      have hxg : x = g := by rw [← hgy, hy0, add_zero]
      exact (mhs.iSup_deligneSplitting_disjoint_WC n).le_bot ⟨by rw [hxg]; exact hg, hx1⟩
  rcases le_or_gt k M with h | h
  · exact key k h
  · rw [mhs.iSup_deligneSplitting_eq_bot_of_WC_eq_top hM h.le]
    exact disjoint_bot_right

/-- **The pieces of Deligne's bigrading are independent.**

A vector of `I^{p,q}` lying in the sum of the other pieces first loses its part of larger total
degree, which the previous lemma kills; what is left lies in `W_{p+q}` and splits into `W_{p+q-1}`
and pieces of the same total degree but different first index, the latter lying in `F^{p+1}` and
in `conj F^{q+1}` modulo `W_{p+q-1}`. Its class in `gr^W_{p+q}` therefore lies both in the Hodge
component `H^{p,q}` and in the complementary `conj F^{q+1} ⊔ F^{p+1}`, so it vanishes and the
vector falls into `W_{p+q-1}`, which `I^{p,q}` meets trivially. -/
theorem iSupIndep_deligneSplittingFamily : iSupIndep mhs.deligneSplittingFamily := by
  intro pq
  obtain ⟨p, q⟩ := pq
  simp only [deligneSplittingFamily_apply]
  rw [disjoint_iff, ← le_bot_iff]
  rintro x ⟨hx1, hx2⟩
  have hxW : x ∈ mhs.WC (p + q) := mhs.deligneSplitting_le_WC p q hx1
  have hbound : (⨆ rs : ℤ × ℤ, ⨆ (_ : rs ≠ (p, q)), mhs.deligneSplitting rs.1 rs.2) ≤
      ((⨆ r, ⨆ (_ : r ≠ p), mhs.deligneSplitting r (p + q - r)) ⊔ mhs.WC (p + q - 1)) ⊔
        ⨆ (rs : ℤ × ℤ) (_ : p + q < rs.1 + rs.2), mhs.deligneSplitting rs.1 rs.2 := by
    refine iSup₂_le fun rs hrs ↦ ?_
    rcases lt_trichotomy (rs.1 + rs.2) (p + q) with h | h | h
    · exact le_sup_of_le_left (le_sup_of_le_right
        ((mhs.deligneSplitting_le_WC rs.1 rs.2).trans (mhs.WC_monotone (by omega))))
    · refine le_sup_of_le_left (le_sup_of_le_left (le_iSup₂_of_le rs.1 ?_ (le_of_eq ?_)))
      · intro hr
        exact hrs (Prod.ext hr (by omega))
      · congr 1
        omega
    · exact le_sup_of_le_right (le_iSup₂_of_le rs h le_rfl)
  obtain ⟨w, hw, y, hy, hwy⟩ := Submodule.mem_sup.1 (hbound hx2)
  have hwW : w ∈ mhs.WC (p + q) :=
    (sup_le (iSup₂_le fun r _ ↦ (mhs.deligneSplitting_le_WC r (p + q - r)).trans
      (mhs.WC_monotone (by omega))) (mhs.WC_monotone (by omega))) hw
  have hy0 : y = 0 := by
    have hyW : y ∈ mhs.WC (p + q) := by
      have hyx : y = x - w := by rw [← hwy]; abel
      rw [hyx]
      exact Submodule.sub_mem _ hxW hwW
    simpa using (mhs.WC_disjoint_iSup_deligneSplitting (p + q)).le_bot ⟨hyW, hy⟩
  have hxw : x = w := by rw [← hwy, hy0, add_zero]
  obtain ⟨z, hz, w', hw', hzw⟩ := Submodule.mem_sup.1 hw
  have hzle : (⨆ r, ⨆ (_ : r ≠ p), mhs.deligneSplitting r (p + q - r)) ≤
      ((mhs.F (p + 1) ⊓ mhs.WC (p + q)) ⊔
        (mhs.conjF (q + 1) ⊓ mhs.WC (p + q))) ⊔ mhs.WC (p + q - 1) := by
    refine iSup₂_le fun r hr ↦ ?_
    rcases lt_or_gt_of_ne hr with h | h
    · rw [deligneSplitting_def]
      refine inf_le_right.trans (sup_le ?_ (iSup_le fun j ↦ ?_))
      · exact le_sup_of_le_left (le_sup_of_le_right
          (inf_le_inf (mhs.conjF_antitone (by omega)) (mhs.WC_monotone (by omega))))
      · exact le_sup_of_le_right (inf_le_right.trans (mhs.WC_monotone (by omega)))
    · exact le_sup_of_le_left (le_sup_of_le_left (le_inf
        ((mhs.deligneSplitting_le_F r _).trans (mhs.F_antitone (by omega)))
        ((mhs.deligneSplitting_le_WC r _).trans (mhs.WC_monotone (by omega)))))
  obtain ⟨zz, hzz, z₃, hz₃, hzzz⟩ := Submodule.mem_sup.1 (hzle hz)
  obtain ⟨z₁, hz₁, z₂, hz₂, hz₁₂⟩ := Submodule.mem_sup.1 hzz
  have hz₃W : z₃ ∈ mhs.WC (p + q) := mhs.WC_monotone (by omega) hz₃
  have hw'W : w' ∈ mhs.WC (p + q) := mhs.WC_monotone (by omega) hw'
  have hxeq : x = z₁ + z₂ + z₃ + w' := by rw [hxw, ← hzw, ← hzzz, ← hz₁₂]
  have hclassx : Submodule.Quotient.mk (⟨x, hxW⟩ : mhs.WC (p + q)) ∈
      (mhs.complexGradedHodgeStructure (p + q)).piece p := by
    refine mhs.mk_mem_complexGradedHodgeStructure_piece (p + q) p ⟨x, hxW⟩
      (mhs.deligneSplitting_le_F p q hx1) ?_
    have hle := mhs.deligneSplitting_le_conjF_sup_WC p q hx1
    -- Express the second bidegree `q` in the graded-piece convention `(p + q) - p`.
    rw [conjF_def, show q = p + q - p by ring] at hle
    exact (sup_le le_sup_left (le_sup_of_le_right (mhs.WC_monotone (by omega)))) hle
  have hmk : (Submodule.Quotient.mk (⟨x, hxW⟩ : mhs.WC (p + q)) :
        weightGradedComplex mhs.WC (p + q)) =
      Submodule.Quotient.mk (⟨z₁, hz₁.2⟩ : mhs.WC (p + q)) +
        Submodule.Quotient.mk (⟨z₂, hz₂.2⟩ : mhs.WC (p + q)) := by
    rw [← Submodule.Quotient.mk_add]
    refine (Submodule.Quotient.eq _).2 (Submodule.mem_comap.2 ?_)
    -- Unfold subtraction of quotient representatives to membership in the lower weight step.
    change x - (z₁ + z₂) ∈ mhs.WC (p + q - 1)
    have hrest : x - (z₁ + z₂) = z₃ + w' := by rw [hxeq]; abel
    rw [hrest]
    exact Submodule.add_mem _ hz₃ hw'
  have hclass₁ : Submodule.Quotient.mk (⟨z₁, hz₁.2⟩ : mhs.WC (p + q)) ∈
      (mhs.complexGradedHodgeStructure (p + q)).F (p + 1) := by
    rw [complexGradedHodgeStructure_F, mem_complexGradedF_iff]
    exact ⟨⟨z₁, hz₁.2⟩, hz₁.1, rfl⟩
  have hclass₂ : Submodule.Quotient.mk (⟨z₂, hz₂.2⟩ : mhs.WC (p + q)) ∈
      (mhs.complexGradedHodgeStructure (p + q)).conjF (p + q + 1 - p) := by
    rw [complexGradedHodgeStructure_conjF, mem_complexGradedF_iff]
    refine ⟨⟨z₂, hz₂.2⟩, ?_, rfl⟩
    rw [← conjF_def]
    exact mhs.conjF_antitone (by omega) hz₂.1
  have hzero := ((mhs.complexGradedHodgeStructure (p + q)).isCompl_piece_conjF_sup_F
    p).disjoint.le_bot ⟨hclassx, by
      rw [hmk]
      exact Submodule.add_mem _ (Submodule.mem_sup_right hclass₁)
        (Submodule.mem_sup_left hclass₂)⟩
  rw [Submodule.mem_bot] at hzero
  have hxlow : x ∈ mhs.WC (p + q - 1) := Submodule.mem_comap.1
    ((Submodule.Quotient.mk_eq_zero
      ((mhs.WC (p + q - 1)).submoduleOf (mhs.WC (p + q)))).1 hzero)
  exact (mhs.deligneSplitting_disjoint_WC p q).le_bot ⟨hx1, hxlow⟩

/-- **Deligne's theorem.** The pieces `I^{p,q}` of Deligne's bigrading form an internal direct sum
of the complex vector space underlying a mixed Hodge structure. -/
theorem isInternal_deligneSplittingFamily :
    DirectSum.IsInternal mhs.deligneSplittingFamily := by
  classical
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    mhs.iSupIndep_deligneSplittingFamily mhs.iSup_deligneSplittingFamily_eq_top

end MixedHodgeStructure

end TauCeti.Hodge
