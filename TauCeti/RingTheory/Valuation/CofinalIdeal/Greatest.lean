/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.RingTheory.Valuation.CofinalIdeal.Basic

/-!
# The ideal-indexed characteristic subgroup `cΓ_v(I)`

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), §7.1, Lemmas 7.2 and 7.4 and Definition 7.3.**

For a valuation `v` and an ideal `I` satisfying the standing hypothesis of §7.1 — that `I` has
the same radical as some finitely generated ideal — Wedhorn attaches to `I` a convex subgroup
`cΓ_v(I)` of the value group by a case split: it is the characteristic subgroup `cΓ_v` when
`v(I)` meets it, and otherwise the *greatest* convex subgroup for which every value of `I` is
cofinal. Lemma 7.2 is what makes the second branch well posed, and Lemma 7.4 characterises when
`cΓ_v(I)` is everything — the condition that cuts out `Spv (A, I)`.

The engine throughout is Lemma 7.1 (`TauCeti.RingTheory.Valuation.CofinalIdeal.Basic`): the elements
whose value is cofinal form a *radical ideal*. Being an ideal propagates cofinality from a
generating set to the ideal it spans; being radical propagates it across `√I = √J`. Those are
the two uses Wedhorn makes of it, and both appear here.

## Main definitions

* `Valuation.IdealCofinalFor v H I` : every element of `I` has value cofinal for `H`.
* `Valuation.IdealMeetsCharacteristicSubgroup v I` : `v(I)` meets `cΓ_v`, the
  branch condition of Definition 7.3.
* `Valuation.valueSet v I` : the nonzero values of `v` on `I`.
* `Valuation.characteristicSubgroupOfIdeal` : **Definition 7.3**, `cΓ_v(I)`.

## Main results
* `Valuation.idealMeetsCharacteristicSubgroup_iff` and
  `Valuation.idealMeetsCharacteristicSubgroup_of_one_le` : the branch condition of
  Definition 7.3 restated on `valueSet`, and the introduction rule discharging it from a
  value `≥ 1`.

* `Valuation.idealCofinalFor_iff_forall_isCofinalElement` : the ideal condition is
  cofinality of each nonzero value as an element of the value group; vanishing values are
  excluded rather than constrained, since `0` is cofinal for every subgroup.
* `Valuation.idealCofinalFor_of_span`,
  `Valuation.le_closure_singleton_of_idealCofinalFor` and
  `Valuation.le_of_idealCofinalFor_of_mem_valueSet` : the membership, maximality and
  minimality halves of **Lemma 7.2**, with `Valuation.isLeast_of_idealCofinalFor` the
  least-element form of the last.
* `Valuation.idealCofinalFor_radical_iff` : cofinality depends only on the radical.
* `Valuation.exists_mem_max_restrict_ne_zero` : a finite spanning set contains a
  nonvanishing value-maximising element whenever the ideal does not vanish identically.
* `Valuation.isGreatestIdealCofinal_closure_singleton_of_span` : **Lemma 7.2's
  greatest-cofinal conclusion** from a generating set, with
  `exists_isGreatestIdealCofinal_of_not_meets` its existence form, which is what Definition 7.3
  presupposes.
* `Valuation.exists_mem_valueSet_mem_characteristicSubgroupOfIdeal` and
  `Valuation.isLeast_characteristicSubgroupOfIdeal` : **Lemma 7.2's attainment and
  minimality conclusions** for `cΓ_v(I)` — off the first branch and with `v` not identically zero
  on `I`, it contains a value of `I` and is the least convex subgroup that does.
* `Valuation.characteristicSubgroup_le_characteristicSubgroupOfIdeal` : `cΓ_v(I)` always
  contains `cΓ_v`.
* `Valuation.characteristicSubgroupOfIdeal_eq_top_iff` and
  `Valuation.characteristicSubgroupOfIdeal_eq_top_iff_forall_span` : **Lemma 7.4**, in
  the all-of-`I` and generating-set forms.
* `Valuation.characteristicSubgroupOfIdeal_eq_top_congr_of_isEquiv` : that criterion is
  an invariant of the valuation class, which is what lets `Spv (A, I)` be carved out of the
  valuation spectrum.

## Implementation notes

The §7.1 development here — Lemma 7.2's greatest-cofinal and attainment conclusions, the case
split of Definition 7.3, and Lemma 7.4 — follows Wedhorn directly. The AINTLIB adic-spaces
development (`aintlib-adic-spaces`, revision `37bbdaeb9`) reaches the same section by a route
that does not pass through these results: its `Spv.IsInSpvAI`
(`projects/AdicSpaces/Adic spaces/SpvAI.lean`) *defines* `Spv (A, I)` by clause (ii) of Lemma
7.4, the disjunction `(∀ a ∈ I, CofinalValue v a) ∨ IsMicrobial v`, so it needs neither
Definition 7.3's `cΓ_v(I)` nor Lemma 7.2's existence result, and states no Lemma 7.4. Those
three are therefore without a formalised antecedent here; the equivalence between the two
routes is what `characteristicSubgroupOfIdeal_eq_top_iff` supplies.

Two pieces do have antecedents: the convex-subgroup notion this rests on came from the same
development (`projects/AdicSpaces/Adic spaces/ValuationContinuity.lean`, `ConvexSubgroup` and
`ConvexSubgroup.minContain`) and reached this file through
`TauCeti.Algebra.Order.Group.ConvexSubgroup`; and the cofinal-value predicate corresponds to
its `Valuation.CofinalValue` in `SpvAI.lean`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Lemma 7.1, Lemma 7.2, Definition 7.3, Lemma 7.4
-/

public section

namespace Valuation

open MonoidWithZeroHom

variable {A : Type*} [Ring A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The predicate cut out by Wedhorn Lemma 7.2: every element of `I` has value cofinal
for `H`. -/
def IdealCofinalFor (v : Valuation A Γ₀)
    (H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))) (I : Ideal A) : Prop :=
  ∀ a ∈ I, CofinalValueFor v H.toSubgroup a

/-- The defining property of ideal-wide cofinality. Needed because the definition's body is not
exposed, so consumers cannot apply `IdealCofinalFor` as a `∀` directly. Mirrors
`cofinalValueFor_def`. -/
theorem idealCofinalFor_def {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {I : Ideal A} :
    IdealCofinalFor v H I ↔ ∀ a ∈ I, CofinalValueFor v H.toSubgroup a :=
  Iff.rfl

/-- The condition is antitone in the ideal. -/
theorem IdealCofinalFor.mono {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {I J : Ideal A}
    (h : IdealCofinalFor v H J) (hIJ : I ≤ J) : IdealCofinalFor v H I :=
  fun a ha ↦ h a (hIJ ha)

/-- Below the strict-containment threshold, the ideal condition says exactly that `I` is
contained in the cofinality ideal of Lemma 7.1. -/
theorem idealCofinalFor_iff_le_cofinalIdeal {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))}
    (hH : characteristicSubgroup v < H) {I : Ideal A} :
    IdealCofinalFor v H I ↔ I ≤ cofinalIdeal v hH :=
  ⟨fun h _ hx ↦ mem_cofinalIdeal.mpr (h _ hx), fun h _ hx ↦ mem_cofinalIdeal.mp (h hx)⟩

/-- The values of `I` meet the characteristic subgroup: the first branch of Wedhorn
Definition 7.3. -/
def IdealMeetsCharacteristicSubgroup (v : Valuation A Γ₀) (I : Ideal A) : Prop :=
  ∃ (a : A) (_ : a ∈ I) (h : (MonoidWithZeroHom.ofClass v) a ≠ 0),
    valueGroup.mk (.ofClass v) 1 a (by simp) h ∈ characteristicSubgroup v

/-- An attained value `≥ 1` always meets the characteristic subgroup — so under Wedhorn's
disjointness hypothesis every element of `I` has value strictly below `1`, the observation
recorded after Lemma 7.2. -/
theorem lt_one_of_not_idealMeetsCharacteristicSubgroup {v : Valuation A Γ₀} {I : Ideal A}
    (hdisj : ¬ IdealMeetsCharacteristicSubgroup v I) {a : A} (haI : a ∈ I) : v a < 1 := by
  by_contra hge
  push Not at hge
  have ha0 : (MonoidWithZeroHom.ofClass v) a ≠ 0 := by
    simpa using (zero_lt_one.trans_le hge).ne'
  exact hdisj ⟨a, haI, ha0, valueGroup_mk_mem_characteristicSubgroup_of_one_le_value ha0 hge⟩

/-- The ideal condition inherits that monotonicity. -/
theorem IdealCofinalFor.mono_subgroup {v : Valuation A Γ₀}
    {H K : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {I : Ideal A}
    (h : IdealCofinalFor v K I) (hHK : H ≤ K) : IdealCofinalFor v H I :=
  fun a ha ↦ (h a ha).mono hHK

/-! ### Reduction to the value set -/

/-- The nonzero values attained by `v` on an ideal, as a subset of the value group. It carries
the attainment hypothesis of Lemma 7.2 and the maximality half; note that no maximum is taken
over it — Wedhorn maximises over a finite generating set, which is why the standing
finite-generation hypothesis is needed at all. -/
def valueSet (v : Valuation A Γ₀) (I : Ideal A) : Set (valueGroup (.ofClass v)) :=
  {γ | ∃ a ∈ I, v.restrict a = (γ : ValueGroup₀ (.ofClass v))}

@[simp]
theorem mem_valueSet {v : Valuation A Γ₀} {I : Ideal A} {γ : valueGroup (.ofClass v)} :
    γ ∈ valueSet v I ↔ ∃ a ∈ I, v.restrict a = (γ : ValueGroup₀ (.ofClass v)) :=
  Iff.rfl

/-- The branch condition of Definition 7.3, restated on `valueSet`: `v(I)` meets `cΓ_v`. The
definition quantifies over ring elements, this form over the values they attain; they carry the
same data through `Valuation.restrict_eq_mk`. -/
theorem idealMeetsCharacteristicSubgroup_iff {v : Valuation A Γ₀} {I : Ideal A} :
    IdealMeetsCharacteristicSubgroup v I ↔ ∃ γ ∈ valueSet v I, γ ∈ characteristicSubgroup v := by
  constructor
  · rintro ⟨a, haI, h0, hmem⟩
    exact ⟨_, ⟨a, haI, v.restrict_eq_mk h0⟩, hmem⟩
  · rintro ⟨γ, ⟨a, haI, hval⟩, hmem⟩
    have h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0 := by
      intro h
      rw [v.restrict_eq_zero_iff.mpr (by simpa using h)] at hval
      exact WithZero.coe_ne_zero hval.symm
    refine ⟨a, haI, h0, ?_⟩
    have hγ : valueGroup.mk (.ofClass v) 1 a (by simp) h0 = γ := by
      exact_mod_cast (v.restrict_eq_mk h0).symm.trans hval
    rwa [hγ]

/-- An element of `I` with value at least `1` puts `v(I)` into `cΓ_v`. This is the positive
counterpart of `lt_one_of_not_idealMeetsCharacteristicSubgroup`, and the introduction rule
that callers use
to discharge the first branch of Definition 7.3. -/
theorem idealMeetsCharacteristicSubgroup_of_one_le {v : Valuation A Γ₀} {I : Ideal A} {a : A}
    (haI : a ∈ I) (ha : 1 ≤ v a) : IdealMeetsCharacteristicSubgroup v I := by
  have h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0 := by
    simpa using (zero_lt_one.trans_le ha).ne'
  exact ⟨a, haI, h0, valueGroup_mk_mem_characteristicSubgroup_of_one_le_value h0 ha⟩

/-- **The bridge from the ideal to the group.** An ideal is cofinal for `H` exactly when every
one of its nonzero values is a cofinal *element* of the value group. The vanishing values need
no condition, since `0` is cofinal for every subgroup — which is why they are excluded from
`valueSet` rather than constrained. -/
theorem idealCofinalFor_iff_forall_isCofinalElement {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {I : Ideal A} :
    IdealCofinalFor v H I ↔
      ∀ γ ∈ valueSet v I, TauCeti.IsCofinalElement H.toSubgroup γ := by
  constructor
  · rintro hI γ ⟨a, haI, ha⟩
    have h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0 := by
      intro hz
      exact absurd (ha ▸ v.restrict_eq_zero_iff.mpr hz) WithZero.coe_ne_zero
    have := (cofinalValueFor_iff_isCofinalElement h0).mp (hI a haI)
    have hmk : valueGroup.mk (.ofClass v) 1 a (by simp) h0 = γ := by
      have := (v.restrict_eq_mk h0).symm.trans ha
      exact_mod_cast this
    exact hmk ▸ this
  · intro hS a haI
    by_cases h0 : (MonoidWithZeroHom.ofClass v) a = 0
    · exact cofinalValueFor_of_eq_zero h0
    · refine (cofinalValueFor_iff_isCofinalElement h0).mpr (hS _ ⟨a, haI, ?_⟩)
      exact v.restrict_eq_mk h0

/-! ### The membership, maximality and minimality halves of Wedhorn Lemma 7.2 -/

/-- **Maximality half.** Any convex subgroup for which `I` is cofinal is contained in the one
generated by a single attained value below `1`. Only membership of `h` in the value set is
needed — not that `h` dominates it. -/
theorem le_closure_singleton_of_idealCofinalFor {v : Valuation A Γ₀} {I : Ideal A}
    {K : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))} {h : valueGroup (.ofClass v)}
    (hh : h ∈ valueSet v I) (hlt : h < 1) (hK : IdealCofinalFor v K I) :
    K ≤ TauCeti.ConvexSubgroup.closure {h} :=
  (TauCeti.isCofinalElement_iff_subset_closure hlt).mp
    (idealCofinalFor_iff_forall_isCofinalElement.mp hK h hh)

/-- **Minimality half.** A convex subgroup for which `I` is cofinal sits below every convex
subgroup containing so much as one value of `I`. No domination hypothesis is needed. -/
theorem le_of_idealCofinalFor_of_mem_valueSet {v : Valuation A Γ₀} {I : Ideal A}
    {H K : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))}
    (hcof : IdealCofinalFor v H I) {γ : valueGroup (.ofClass v)}
    (hγ : γ ∈ valueSet v I) (hγK : γ ∈ K) : H ≤ K :=
  -- through the convex subgroup `γ` generates: `H` is below it, and it is below `K`
  (le_closure_singleton_of_idealCofinalFor hγ
      (idealCofinalFor_iff_forall_isCofinalElement.mp hcof γ hγ).lt_one hcof).trans
    (TauCeti.ConvexSubgroup.closure_le.mpr (Set.singleton_subset_iff.mpr hγK))

/-- **Minimality, as a least-element statement.** Any convex subgroup for which `I` is cofinal
and which contains a value of `I` is the least convex subgroup meeting `v(I)`. -/
theorem isLeast_of_idealCofinalFor {v : Valuation A Γ₀} {I : Ideal A}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))}
    (hcof : IdealCofinalFor v H I) (hmeet : ∃ γ ∈ valueSet v I, γ ∈ H) :
    IsLeast {K | ∃ γ ∈ valueSet v I, γ ∈ K} H :=
  ⟨hmeet, fun _ ⟨_, hγ, hγK⟩ ↦ le_of_idealCofinalFor_of_mem_valueSet hcof hγ hγK⟩

/-- **Membership half.** It suffices to check cofinality on a generating set: if every element
of `T` has cofinal value, so does every element of the ideal `T` spans.

Note what this does *not* say: the values on `I` need not be bounded by the values on `T`,
since `v (c * t) = v c * v t` can exceed `v t` when `1 < v c`. The hypothesis constrains the
generators only, not the ideal's values. -/
theorem idealCofinalFor_of_span {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))}
    (hH : characteristicSubgroup v < H) {T : Set A} {I : Ideal A} (hspan : Ideal.span T = I)
    (hT : ∀ t ∈ T, CofinalValueFor v H.toSubgroup t) : IdealCofinalFor v H I :=
  (idealCofinalFor_iff_le_cofinalIdeal hH).mpr <| by
    rw [← hspan, Ideal.span_le]
    exact fun t ht ↦ mem_cofinalIdeal.mpr (hT t ht)

/-- If `v` vanishes on the whole of `I` then every convex subgroup works, so the greatest one
is `⊤`. This is Wedhorn's "if `v(I) = {0}`, we may choose `H = Γv`". -/
theorem isGreatestIdealCofinal_top_of_forall_eq_zero {v : Valuation A Γ₀} {I : Ideal A}
    (h : ∀ a ∈ I, (MonoidWithZeroHom.ofClass v) a = 0) : IsGreatest {K | IdealCofinalFor v K I} ⊤ :=
  ⟨fun a ha ↦ cofinalValueFor_of_eq_zero (h a ha), fun _ _ ↦ le_top⟩

/-! ### Reduction along the radical

From here commutativity is needed: the radical of an ideal is Mathlib's `Ideal.radical`, which
is defined over a commutative semiring. Everything above needs only a ring. -/

section CommRing

variable {A : Type*} [CommRing A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Cofinality of an ideal depends only on its radical.** This is what allows `I` to be
replaced by a finitely generated ideal with the same radical — the standing hypothesis
of §7.1. -/
theorem idealCofinalFor_radical_iff {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))}
    (hH : characteristicSubgroup v < H) {I : Ideal A} :
    IdealCofinalFor v H I.radical ↔ IdealCofinalFor v H I := by
  rw [idealCofinalFor_iff_le_cofinalIdeal hH, idealCofinalFor_iff_le_cofinalIdeal hH]
  exact (isRadical_cofinalIdeal hH).radical_le_iff

/-- Two ideals with the same radical are cofinal for exactly the same convex subgroups. -/
theorem idealCofinalFor_congr_of_radical_eq {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))}
    (hH : characteristicSubgroup v < H) {I J : Ideal A} (hIJ : I.radical = J.radical) :
    IdealCofinalFor v H I ↔ IdealCofinalFor v H J := by
  rw [← idealCofinalFor_radical_iff hH (I := I), ← idealCofinalFor_radical_iff hH (I := J), hIJ]

/-! ### Assembling Lemma 7.2's greatest-cofinal conclusion -/

/-- **Wedhorn Lemma 7.2**, in the form the standing hypothesis of §7.1 supplies it.

Given a generating set `T` of an ideal `J` with the same radical as `I`, and a value
`h < 1` dominating the values on `T` and attained (up to a power) on `I`, the convex subgroup
generated by `h` is the greatest one for which `I` is cofinal.

Domination is stated on `ValueGroup₀`, so generators lying in the support are allowed: a
vanishing value is cofinal for free. Attainment is required only up to a power, because `h`
lives on `J` rather than on `I`. -/
theorem isGreatestIdealCofinal_closure_singleton_of_span {v : Valuation A Γ₀}
    {I J : Ideal A} {T : Set A} {h : valueGroup (.ofClass v)} {n : ℕ}
    (hH : characteristicSubgroup v < TauCeti.ConvexSubgroup.closure {h})
    (hspan : Ideal.span T = J) (hrad : I.radical = J.radical) (hlt : h < 1) (hn : n ≠ 0)
    (hdom : ∀ t ∈ T, v.restrict t ≤ (h : ValueGroup₀ (.ofClass v)))
    (hatt : h ^ n ∈ valueSet v I) :
    IsGreatest {K | IdealCofinalFor v K I} (TauCeti.ConvexSubgroup.closure {h}) := by
  constructor
  · -- membership: generators → J (ideal) → I (radical)
    refine (idealCofinalFor_congr_of_radical_eq hH hrad).mpr ?_
    refine idealCofinalFor_of_span hH hspan fun t ht ↦ ?_
    by_cases h0 : (MonoidWithZeroHom.ofClass v) t = 0
    · exact cofinalValueFor_of_eq_zero h0
    · refine cofinalValueFor_closure_singleton_of_le h0 ?_ hlt
      have := hdom t ht
      rwa [v.restrict_eq_mk h0, WithZero.coe_le_coe] at this
  · -- maximality: `h ^ n` is attained on `I`, and generates the same subgroup as `h`
    intro K hK
    have := le_closure_singleton_of_idealCofinalFor hatt ((pow_lt_one_iff hn).mpr hlt) hK
    rwa [TauCeti.ConvexSubgroup.closure_singleton_pow hn] at this

/-- Radical membership upgraded to a *nonzero* exponent: if `√I = √J` then every element of `I`
has a positive power in `J`. The exponent `0` is harmless to exclude, since `a ^ 0 ∈ J` forces
`J = ⊤`, and then `a ^ 1 ∈ J` too.

Used in both directions below — to move from `I` into the finitely generated `J`, and back. -/
private theorem exists_pow_ne_zero_mem_of_radical_eq {I J : Ideal A}
    (hrad : I.radical = J.radical) {a : A} (ha : a ∈ I) : ∃ n, n ≠ 0 ∧ a ^ n ∈ J := by
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (hrad ▸ Ideal.le_radical ha)
  rcases Nat.eq_zero_or_pos n with rfl | hp
  · refine ⟨1, one_ne_zero, ?_⟩
    have h1 : (1 : A) ∈ J := by simpa using hn
    simp [(Ideal.eq_top_iff_one J).mpr h1]
  · exact ⟨n, hp.ne', hn⟩

/-- If `v` vanishes on a generating set of `J` and `√I = √J`, then `v` vanishes on all of `I`.

Both places where the construction below needs a nonvanishing value are contrapositives of this:
the generating set is nonempty, and the value-maximising generator is nonzero. -/
private theorem mem_supp_of_radical_eq_of_forall_mem_supp {v : Valuation A Γ₀} {I J : Ideal A}
    {T : Finset A} (hT : Ideal.span (T : Set A) = J) (hrad : I.radical = J.radical)
    (hsupp : ∀ t ∈ T, t ∈ v.supp) {a : A} (ha : a ∈ I) : a ∈ v.supp := by
  obtain ⟨n, hn0, hn⟩ := exists_pow_ne_zero_mem_of_radical_eq hrad ha
  have hpow : a ^ n ∈ v.supp := by
    rw [← hT] at hn
    exact Ideal.span_le.mpr (fun t ht ↦ hsupp t ht) hn
  rw [v.mem_supp_iff, map_pow] at hpow
  exact (v.mem_supp_iff _).mpr ((pow_eq_zero_iff hn0).mp hpow)

/-- The value of a power is the power of the value, read in the value group rather than in
`ValueGroup₀`. Both the disjointness argument and the construction below need it, at the two
different generators they work with. -/
private theorem restrict_pow_eq_mk_pow {v : Valuation A Γ₀} {t : A}
    (ht0 : (MonoidWithZeroHom.ofClass v) t ≠ 0) (n : ℕ) :
    v.restrict (t ^ n)
      = ((valueGroup.mk (.ofClass v) 1 t (by simp) ht0 ^ n : valueGroup (.ofClass v)) :
          ValueGroup₀ (.ofClass v)) := by
  rw [map_pow, v.restrict_eq_mk ht0]
  simp

/-- Under Wedhorn's disjointness hypothesis the class of a generator stays out of `cΓ_v`: were
it inside, so would be its `n`-th power, which is the class of `t ^ n ∈ I` — exactly the
meeting that is excluded. -/
private theorem not_mem_characteristicSubgroup_of_pow_mem {v : Valuation A Γ₀} {I : Ideal A}
    (hdisj : ¬ IdealMeetsCharacteristicSubgroup v I) {t : A}
    (ht0 : (MonoidWithZeroHom.ofClass v) t ≠ 0) {n : ℕ} (hn : t ^ n ∈ I) :
    valueGroup.mk (.ofClass v) 1 t (by simp) ht0 ∉ characteristicSubgroup v := by
  intro hmem
  have hn0 : (MonoidWithZeroHom.ofClass v) (t ^ n) ≠ 0 := by
    simpa [map_pow] using pow_ne_zero n ht0
  refine hdisj ⟨t ^ n, hn, hn0, ?_⟩
  have hclass : valueGroup.mk (.ofClass v) 1 (t ^ n) (by simp) hn0
      = valueGroup.mk (.ofClass v) 1 t (by simp) ht0 ^ n :=
    mod_cast (v.restrict_eq_mk hn0).symm.trans (restrict_pow_eq_mk_pow ht0 n)
  rw [hclass]
  exact pow_mem hmem n

/-- **A generator of greatest value, not in the support.** If `I` and `Ideal.span T` have the same
radical and `v` does not vanish identically on `I`, then some `t₀ ∈ T` maximises `v.restrict` over
`T` and has `v t₀ ≠ 0`.

Nonvanishing is what needs the radical hypothesis: were every generator in the support, so would
be everything of `I`, contradicting the witness. Maximality is then `Finset.exists_max_image`, and
the maximiser inherits nonvanishing because it dominates every generator. -/
theorem exists_mem_max_restrict_ne_zero {v : Valuation A Γ₀} {I J : Ideal A} {T : Finset A}
    (hT : Ideal.span (T : Set A) = J) (hrad : I.radical = J.radical) {a₀ : A} (ha₀I : a₀ ∈ I)
    (ha₀0 : (MonoidWithZeroHom.ofClass v) a₀ ≠ 0) :
    ∃ t₀ ∈ T, (MonoidWithZeroHom.ofClass v) t₀ ≠ 0 ∧ ∀ t ∈ T, v.restrict t ≤ v.restrict t₀ := by
  have hsupp : ¬ ∀ t ∈ T, t ∈ v.supp := fun hall ↦
    ha₀0 ((v.mem_supp_iff _).mp (mem_supp_of_radical_eq_of_forall_mem_supp hT hrad hall ha₀I))
  have hTne : T.Nonempty := by
    rcases T.eq_empty_or_nonempty with rfl | hne'
    · exact absurd (by simp) hsupp
    · exact hne'
  obtain ⟨t₀, ht₀T, ht₀max⟩ := T.exists_max_image (fun t ↦ v.restrict t) hTne
  refine ⟨t₀, ht₀T, fun hz ↦ hsupp fun t ht ↦ ?_, ht₀max⟩
  rw [v.mem_supp_iff]
  have hle : v.restrict t ≤ v.restrict t₀ := ht₀max t ht
  rw [v.restrict_eq_zero_iff.mpr hz] at hle
  exact v.restrict_eq_zero_iff.mp (le_antisymm hle zero_le)

/-- **Wedhorn Lemma 7.2, existence form of the greatest-cofinal conclusion.** Under the standing
hypothesis of §7.1 — that `I` has the same radical as some finitely generated ideal — with `v(I)`
missing `cΓ_v` and not identically zero, a greatest convex subgroup for which `I` is cofinal
exists, and it meets `v(I)`.

This is what makes Definition 7.3 well posed: its second branch names *the* greatest such
subgroup, so the definition presupposes exactly this statement. -/
private theorem exists_isGreatestIdealCofinal {v : Valuation A Γ₀} {I : Ideal A}
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical)
    (hdisj : ¬ IdealMeetsCharacteristicSubgroup v I)
    (hne : ∃ a ∈ I, (MonoidWithZeroHom.ofClass v) a ≠ 0) :
    ∃ H, IsGreatest {K | IdealCofinalFor v K I} H ∧ characteristicSubgroup v ≤ H ∧
      ∃ γ ∈ valueSet v I, γ ∈ H := by
  obtain ⟨J, ⟨T, hT⟩, hrad⟩ := hfg
  obtain ⟨a₀, ha₀I, ha₀0⟩ := hne
  obtain ⟨t₀, ht₀T, ht₀0, ht₀max⟩ := exists_mem_max_restrict_ne_zero hT hrad ha₀I ha₀0
  -- the witness and the power of it that lands in `I`
  set h : valueGroup (.ofClass v) := valueGroup.mk (.ofClass v) 1 t₀ (by simp) ht₀0 with hdef
  have hrestr : v.restrict t₀ = (h : ValueGroup₀ (.ofClass v)) := v.restrict_eq_mk ht₀0
  have ht₀J : t₀ ∈ J := hT ▸ Ideal.subset_span ht₀T
  obtain ⟨n, hn0, hn⟩ := exists_pow_ne_zero_mem_of_radical_eq hrad.symm ht₀J
  have hpow : v.restrict (t₀ ^ n) = ((h ^ n : valueGroup (.ofClass v)) : ValueGroup₀ _) :=
    restrict_pow_eq_mk_pow ht₀0 n
  have hatt : h ^ n ∈ valueSet v I := ⟨t₀ ^ n, hn, hpow⟩
  have hlt_n : (h ^ n : valueGroup (.ofClass v)) < 1 := by
    have h2 : v.restrict (t₀ ^ n) < 1 :=
      v.restrict_lt_one_iff.mpr (lt_one_of_not_idealMeetsCharacteristicSubgroup hdisj hn)
    rwa [hpow, ← WithZero.coe_one, WithZero.coe_lt_coe] at h2
  have hlt : h < 1 := (pow_lt_one_iff hn0).mp hlt_n
  have hnot : h ∉ characteristicSubgroup v :=
    not_mem_characteristicSubgroup_of_pow_mem hdisj ht₀0 hn
  -- the attained power lies in the constructed subgroup, so the value set meets it
  have hmem : h ^ n ∈ TauCeti.ConvexSubgroup.closure {h} := by
    rw [← TauCeti.ConvexSubgroup.closure_singleton_pow hn0]
    exact TauCeti.ConvexSubgroup.subset_closure _ rfl
  refine ⟨TauCeti.ConvexSubgroup.closure {h}, ?_,
    (TauCeti.ConvexSubgroup.lt_closure_singleton hnot).le, h ^ n, hatt, hmem⟩
  refine isGreatestIdealCofinal_closure_singleton_of_span
    (TauCeti.ConvexSubgroup.lt_closure_singleton hnot) hT hrad hlt hn0 ?_ hatt
  intro t ht
  rw [← hrestr]
  exact ht₀max t ht

/-- **Wedhorn Lemma 7.2's greatest-cofinal conclusion, as Definition 7.3 uses it.** Only the
standing hypothesis of §7.1 and
the disjointness `v(I) ∩ cΓ_v = ∅` are needed: the case where `v` vanishes identically on `I`
is covered separately by `⊤`.

The last conjunct — that the subgroup meets `v(I)` — is guarded by the nonvanishing hypothesis
rather than asserted outright, because it is false in the `⊤` branch: there `valueSet v I` is
empty, so no subgroup whatever meets it. -/
theorem exists_isGreatestIdealCofinal_of_not_meets {v : Valuation A Γ₀} {I : Ideal A}
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical)
    (hdisj : ¬ IdealMeetsCharacteristicSubgroup v I) :
    ∃ H, IsGreatest {K | IdealCofinalFor v K I} H ∧ characteristicSubgroup v ≤ H ∧
      ((∃ a ∈ I, (MonoidWithZeroHom.ofClass v) a ≠ 0) → ∃ γ ∈ valueSet v I, γ ∈ H) := by
  by_cases hne : ∃ a ∈ I, (MonoidWithZeroHom.ofClass v) a ≠ 0
  · obtain ⟨H, hgreat, hle, hmeet⟩ := exists_isGreatestIdealCofinal hfg hdisj hne
    exact ⟨H, hgreat, hle, fun _ ↦ hmeet⟩
  · push Not at hne
    exact ⟨⊤, isGreatestIdealCofinal_top_of_forall_eq_zero hne, le_top,
      fun ⟨a, haI, ha0⟩ ↦ absurd (hne a haI) ha0⟩

/-! ### Wedhorn Definition 7.3 -/

open scoped Classical in
/-- **Wedhorn Definition 7.3: `cΓ_v(I)`.** It is `cΓ_v` when `v(I)` meets the characteristic
subgroup, and otherwise the greatest convex subgroup for which every value of `I` is cofinal —
which exists by Lemma 7.2, and is why the standing hypothesis of §7.1 is carried here.

Note that this is a **case split**, not the convex subgroup generated by `cΓ_v` together with
`v(I)`; those differ. -/
noncomputable def characteristicSubgroupOfIdeal (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    TauCeti.ConvexSubgroup (valueGroup (.ofClass v)) :=
  if h : IdealMeetsCharacteristicSubgroup v I then characteristicSubgroup v
  else (exists_isGreatestIdealCofinal_of_not_meets hfg h).choose

/-- First branch of Definition 7.3. -/
@[simp]
theorem characteristicSubgroupOfIdeal_of_meets {v : Valuation A Γ₀} {I : Ideal A}
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) (h : IdealMeetsCharacteristicSubgroup v I) :
    characteristicSubgroupOfIdeal v I hfg = characteristicSubgroup v := by
  classical
  rw [characteristicSubgroupOfIdeal, dite_eq_left h]

/-- Second branch of Definition 7.3: off the first branch, `cΓ_v(I)` really is the greatest
convex subgroup for which `I` is cofinal. -/
theorem isGreatestIdealCofinal_characteristicSubgroupOfIdeal {v : Valuation A Γ₀} {I : Ideal A}
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical)
    (h : ¬ IdealMeetsCharacteristicSubgroup v I) :
    IsGreatest {K | IdealCofinalFor v K I} (characteristicSubgroupOfIdeal v I hfg) := by
  classical
  rw [characteristicSubgroupOfIdeal, dite_eq_right h]
  exact (exists_isGreatestIdealCofinal_of_not_meets hfg h).choose_spec.1

/-- **`cΓ_v(I)` always contains `cΓ_v`** — the sentence Wedhorn records immediately after
Definition 7.3. -/
theorem characteristicSubgroup_le_characteristicSubgroupOfIdeal (v : Valuation A Γ₀)
    (I : Ideal A) (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    characteristicSubgroup v ≤ characteristicSubgroupOfIdeal v I hfg := by
  classical
  by_cases h : IdealMeetsCharacteristicSubgroup v I
  · rw [characteristicSubgroupOfIdeal_of_meets hfg h]
  · rw [characteristicSubgroupOfIdeal, dite_eq_right h]
    exact (exists_isGreatestIdealCofinal_of_not_meets hfg h).choose_spec.2.1

/-- **`cΓ_v(I)` meets `v(I)`** — the attainment half of Wedhorn Lemma 7.2, on the branch where
Definition 7.3 invokes it: some value of `I` lies in `cΓ_v(I)`.

Nonvanishing cannot be dropped: if `v` vanishes identically on `I` then `valueSet v I` is empty
and nothing meets it. -/
theorem exists_mem_valueSet_mem_characteristicSubgroupOfIdeal {v : Valuation A Γ₀} {I : Ideal A}
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical)
    (h : ¬ IdealMeetsCharacteristicSubgroup v I)
    (hne : ∃ a ∈ I, (MonoidWithZeroHom.ofClass v) a ≠ 0) :
    ∃ γ ∈ valueSet v I, γ ∈ characteristicSubgroupOfIdeal v I hfg := by
  classical
  rw [characteristicSubgroupOfIdeal, dite_eq_right h]
  exact (exists_isGreatestIdealCofinal_of_not_meets hfg h).choose_spec.2.2 hne

/-- **`cΓ_v(I)` is the least convex subgroup meeting `v(I)`** — the minimality conclusion of
Wedhorn Lemma 7.2, on the branch where Definition 7.3 invokes it.

Nonvanishing cannot be dropped: with `valueSet v I` empty nothing meets it, so the set has no
least element. -/
theorem isLeast_characteristicSubgroupOfIdeal {v : Valuation A Γ₀} {I : Ideal A}
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical)
    (h : ¬ IdealMeetsCharacteristicSubgroup v I)
    (hne : ∃ a ∈ I, (MonoidWithZeroHom.ofClass v) a ≠ 0) :
    IsLeast {K | ∃ γ ∈ valueSet v I, γ ∈ K} (characteristicSubgroupOfIdeal v I hfg) :=
  isLeast_of_idealCofinalFor (isGreatestIdealCofinal_characteristicSubgroupOfIdeal hfg h).1
    (exists_mem_valueSet_mem_characteristicSubgroupOfIdeal hfg h hne)

/-! ### Wedhorn Lemma 7.4 -/

/-- **Wedhorn Lemma 7.4, (i) ⟺ (ii).** `cΓ_v(I) = Γ_v` exactly when either every value of `I`
is cofinal for the whole value group, or `Γ_v = cΓ_v` already.

The disjuncts are not exclusive: when `v(I)` meets `cΓ_v`, the left one implies the right. -/
theorem characteristicSubgroupOfIdeal_eq_top_iff {v : Valuation A Γ₀} {I : Ideal A}
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    characteristicSubgroupOfIdeal v I hfg = ⊤ ↔
      (∀ a ∈ I, CofinalValue v a) ∨ characteristicSubgroup v = ⊤ := by
  classical
  by_cases hm : IdealMeetsCharacteristicSubgroup v I
  · rw [characteristicSubgroupOfIdeal_of_meets hfg hm]
    refine ⟨fun h ↦ Or.inr h, ?_⟩
    rintro (hall | hfull)
    · -- an attained value inside `cΓ_v` that is cofinal for everything forces `cΓ_v = ⊤`
      obtain ⟨a, haI, ha0, hmem⟩ := hm
      have hcof : CofinalValueFor v ⊤ a := cofinalValueFor_top_iff.mpr (hall a haI)
      have hlt : valueGroup.mk (.ofClass v) 1 a (by simp) ha0 < 1 := by
        have := hcof.lt_one
        rwa [v.restrict_eq_mk ha0, ← WithZero.coe_one, WithZero.coe_lt_coe] at this
      have hsub := (TauCeti.isCofinalElement_iff_subset_closure hlt).mp
        ((cofinalValueFor_iff_isCofinalElement ha0).mp hcof)
      refine top_le_iff.mp fun x _ ↦ ?_
      exact TauCeti.ConvexSubgroup.closure_le.mpr
        (fun y hy ↦ by rw [Set.mem_singleton_iff] at hy; exact hy ▸ hmem)
        (hsub (TauCeti.ConvexSubgroup.mem_top (x := x)))
    · exact hfull
  · have hg := isGreatestIdealCofinal_characteristicSubgroupOfIdeal hfg hm
    refine ⟨fun htop ↦ Or.inl fun a ha ↦ ?_, ?_⟩
    · have hcof := hg.1 a ha
      rw [htop, TauCeti.ConvexSubgroup.top_toSubgroup] at hcof
      exact cofinalValueFor_top_iff.mp hcof
    · rintro (hall | hfull)
      · refine top_le_iff.mp (hg.2 fun a ha ↦ ?_)
        rw [TauCeti.ConvexSubgroup.top_toSubgroup]
        exact cofinalValueFor_top_iff.mpr (hall a ha)
      · -- `cΓ_v = ⊤` and disjointness force every value on `I` to vanish
        refine top_le_iff.mp (hg.2 fun a ha ↦ ?_)
        by_cases h0 : (MonoidWithZeroHom.ofClass v) a = 0
        · exact cofinalValueFor_of_eq_zero h0
        · exact absurd ⟨a, ha, h0, hfull ▸ TauCeti.ConvexSubgroup.mem_top⟩ hm

/-- **Wedhorn Lemma 7.4, (i) ⟺ (iii).** Clause (iii) checks cofinality only on a generating
set `T` of any ideal with the same radical — the form the `Spv (A, I)` development uses, since
it turns a condition on all of `I` into a condition on generators. (`T` carries no finiteness
hypothesis here; finiteness comes from the standing hypothesis of §7.1 when the caller supplies
a finitely generated `J`.)

The generating set may be taken for any ideal `J` sharing a radical with `I`, not for `I`
itself. -/
theorem characteristicSubgroupOfIdeal_eq_top_iff_forall_span {v : Valuation A Γ₀} {I : Ideal A}
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {J : Ideal A} {T : Set A}
    (hspan : Ideal.span T = J) (hrad : I.radical = J.radical) :
    characteristicSubgroupOfIdeal v I hfg = ⊤ ↔
      (∀ t ∈ T, CofinalValue v t) ∨ characteristicSubgroup v = ⊤ := by
  rw [characteristicSubgroupOfIdeal_eq_top_iff hfg]
  by_cases hfull : characteristicSubgroup v = ⊤
  · simp [hfull]
  refine or_congr_left ?_
  have hHlt : characteristicSubgroup v < ⊤ := lt_of_le_of_ne le_top hfull
  constructor
  · -- values on `I` cofinal ⇒ values on `T` cofinal, since `T ⊆ J ⊆ √I`
    intro hall t ht
    have htJ : t ∈ J := hspan ▸ Ideal.subset_span ht
    obtain ⟨n, hn0, hn⟩ := exists_pow_ne_zero_mem_of_radical_eq hrad.symm htJ
    refine cofinalValueFor_top_iff.mp ((cofinalValueFor_pow_iff (Nat.pos_of_ne_zero hn0)).mp ?_)
    exact cofinalValueFor_top_iff.mpr (hall _ hn)
  · -- generators cofinal ⇒ all of `I` cofinal, through Lemma 7.1 and the radical
    intro hT a ha
    refine cofinalValueFor_top_iff.mp ?_
    refine (idealCofinalFor_congr_of_radical_eq hHlt hrad).mpr ?_ a ha
    exact idealCofinalFor_of_span hHlt hspan fun t ht ↦ cofinalValueFor_top_iff.mpr (hT t ht)

/-- **The `Spv (A, I)` criterion is an invariant of the valuation class.** This is what lets
`Spv (A, I)` be carved out of `Spv A`, whose points are equivalence classes.

Note that it is the *criterion* that transports, not `cΓ_v(I)` itself: equivalent valuations
have different value groups, so their ideal-indexed subgroups are not comparable. -/
theorem characteristicSubgroupOfIdeal_eq_top_congr_of_isEquiv {Γ₀' : Type*}
    [LinearOrderedCommGroupWithZero Γ₀'] {v : Valuation A Γ₀}
    {w : Valuation A Γ₀'} (h : v.IsEquiv w) {I : Ideal A}
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    characteristicSubgroupOfIdeal v I hfg = ⊤ ↔ characteristicSubgroupOfIdeal w I hfg = ⊤ := by
  rw [characteristicSubgroupOfIdeal_eq_top_iff hfg, characteristicSubgroupOfIdeal_eq_top_iff hfg]
  refine or_congr (forall_congr' fun a ↦ imp_congr_right fun _ ↦ h.cofinalValue_iff) ?_
  rw [← hasFullCharacteristicGroup_iff_characteristicSubgroup_eq_top,
    ← hasFullCharacteristicGroup_iff_characteristicSubgroup_eq_top]
  exact h.hasFullCharacteristicGroup_iff

end CommRing

end Valuation
