/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Algebra.Order.Group.Cofinal
public import TauCeti.RingTheory.Valuation.CharacteristicGroup

/-!
# The ideal of cofinal values

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Lemma 7.1.** For a valuation `v` on a
commutative ring and a convex subgroup `H` of its value group strictly containing the
characteristic subgroup `cΓ_v`, the elements whose value is cofinal for `H` form a radical
ideal. Almost all of this needs only a ring: `Ideal A` is `Submodule A A`, a *left* ideal,
and left absorption is exactly what the multiplicative step supplies, so the predicate, the
ideal, its membership lemma and its properness are all stated at `[Ring A]`. Commutativity
enters at one point, radicality, where Mathlib's `Ideal.IsRadical` requires it — and that is
the statement carrying Wedhorn's name, since Lemma 7.1 is about a commutative ring. This is
the object Wedhorn's §7.1
uses to reduce the construction of `cΓ_v(I)`
(Definition 7.3) to a finite generating set, and it is used twice in the proof of Lemma 7.2:
once to pass from generators to the whole ideal, and once to replace `I` by its radical.

Cofinality here is stated for a value that may vanish, since `0` is cofinal for every
subgroup — that is why the vanishing case is a case split in the proofs below rather than
something derivable from cofinality.

## Main definitions

* `Valuation.CofinalValueFor v H a` : The powers of `v a` fall below every member
  of the subgroup `H` of the value group.
* `Valuation.cofinalIdeal v hH` : Those elements, as an ideal.

## Main results
* `Valuation.cofinalValueFor_closure_singleton_of_le` : A value bounded by
  `h < 1` is cofinal for the convex subgroup `h` generates — below `1`, a larger value
  generates a smaller subgroup.

* `Valuation.cofinalValueFor_iff_isCofinalElement` : For a non-vanishing value, the
  valuation-side predicate agrees with the group-side `IsCofinalElement` on the value group.
  This is what lets Wedhorn Proposition 1.20 apply.
* `Valuation.isRadical_cofinalIdeal` : The ideal is radical — the `rad(c) = c` half
  of Lemma 7.1 — with `cofinalValueFor_pow_iff` the elementwise form behind it.
* `Valuation.cofinalIdeal_ne_top` : It is proper, a corollary of the ring-level
  `Valuation.not_cofinalValueFor_one`.
* `Valuation.cofinalValueFor_top_iff` : At the whole value group the predicate is the
  ambient `CofinalValue`.
* `Valuation.cofinalValueFor_neg_iff` : cofinality is invariant under negation, with
  `CofinalValueFor.sub` the resulting difference closure.

## Implementation notes

Ported from the AINTLIB adic-spaces development (`aintlib-adic-spaces`, revision `37bbdaeb9`,
`projects/AdicSpaces/Adic spaces/SpvAI.lean`, Apache-2.0), whose `Valuation.CofinalValue` and
its lemmas supplied the statement shapes and the proof skeleton for the cofinality predicate
and its closure properties. The cofinality bridge is rebuilt here against Mathlib's
`MonoidWithZeroHom.valueGroup` API rather than the parallel value-group construction used
there.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Lemma 7.1
-/

public section

namespace Valuation

open MonoidWithZeroHom

variable {A : Type*} [Ring A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- `v a` is **cofinal for the subgroup `H`** of the value group: its powers fall
below every member of `H` (Wedhorn Definition 1.16, at a value that may vanish). -/
def CofinalValueFor (v : Valuation A Γ₀)
    (H : Subgroup (valueGroup (.ofClass v))) (a : A) : Prop :=
  ∀ h ∈ H, ∃ n : ℕ, v.restrict a ^ n < (h : ValueGroup₀ (.ofClass v))

/-- The defining property of cofinality relative to a subgroup.

Deliberately not `@[simp]`: the right-hand side is the unfolded bounded quantifier, so tagging
it would rewrite `a ∈ cofinalIdeal v hH` past the named predicate and into raw `∀ … ∃ …` form.
`mem_cofinalIdeal` is the intended normal form. -/
theorem cofinalValueFor_def {v : Valuation A Γ₀}
    {H : Subgroup (valueGroup (.ofClass v))} {a : A} :
    CofinalValueFor v H a ↔
      ∀ h ∈ H, ∃ n : ℕ, v.restrict a ^ n < (h : ValueGroup₀ (.ofClass v)) :=
  Iff.rfl

/-- Cofinality for `H` is downward closed in the value. -/
theorem CofinalValueFor.of_le {v : Valuation A Γ₀}
    {H : Subgroup (valueGroup (.ofClass v))} {a b : A}
    (h : CofinalValueFor v H a) (hba : v b ≤ v a) : CofinalValueFor v H b := fun γ hγ ↦
  let ⟨n, hn⟩ := h γ hγ
  ⟨n, lt_of_le_of_lt (pow_le_pow_left' (v.restrict_le_iff.mpr hba) n) hn⟩

/-- Cofinality for a larger convex subgroup implies cofinality for a smaller one: the
monotonicity that makes the family in Wedhorn Lemma 7.2 downward closed. -/
theorem CofinalValueFor.mono {v : Valuation A Γ₀}
    {H K : Subgroup (valueGroup (.ofClass v))} {a : A}
    (h : CofinalValueFor v K a) (hHK : H ≤ K) : CofinalValueFor v H a :=
  cofinalValueFor_def.mpr fun g hg ↦ cofinalValueFor_def.mp h g (hHK hg)

/-- A vanishing value is cofinal for every subgroup (Wedhorn's remark after
Definition 1.16: the adjoined base `0` is cofinal for every subgroup). -/
theorem cofinalValueFor_of_eq_zero {v : Valuation A Γ₀}
    {H : Subgroup (valueGroup (.ofClass v))} {a : A} (ha : v a = 0) :
    CofinalValueFor v H a := by
  intro h _
  refine ⟨1, ?_⟩
  rw [pow_one, v.restrict_eq_zero_iff.mpr ha]
  exact zero_lt_iff.mpr WithZero.coe_ne_zero

/-- Zero has cofinal value. -/
@[simp]
theorem cofinalValueFor_zero (v : Valuation A Γ₀)
    (H : Subgroup (valueGroup (.ofClass v))) : CofinalValueFor v H 0 :=
  cofinalValueFor_of_eq_zero (map_zero v)

/-- A sum of cofinal-value elements has cofinal value: `v (a + b) ≤ max (v a) (v b)`. -/
theorem CofinalValueFor.add {v : Valuation A Γ₀}
    {H : Subgroup (valueGroup (.ofClass v))} {a b : A}
    (ha : CofinalValueFor v H a) (hb : CofinalValueFor v H b) :
    CofinalValueFor v H (a + b) := by
  rcases le_total (v a) (v b) with hab | hab
  · exact hb.of_le ((map_add_le_max v a b).trans (max_le hab le_rfl))
  · exact ha.of_le ((map_add_le_max v a b).trans (max_le le_rfl hab))

/-- Cofinality is invariant under negation, since `v (-a) = v a`. -/
@[simp]
theorem cofinalValueFor_neg_iff {v : Valuation A Γ₀}
    {H : Subgroup (valueGroup (.ofClass v))} {a : A} :
    CofinalValueFor v H (-a) ↔ CofinalValueFor v H a := by
  constructor <;> exact fun h ↦ h.of_le (le_of_eq (by simp [Valuation.map_neg]))

/-- A difference of cofinal-value elements has cofinal value. -/
theorem CofinalValueFor.sub {v : Valuation A Γ₀}
    {H : Subgroup (valueGroup (.ofClass v))} {a b : A}
    (ha : CofinalValueFor v H a) (hb : CofinalValueFor v H b) :
    CofinalValueFor v H (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add (cofinalValueFor_neg_iff.mpr hb)

/-- Multiplying by an element of value at most `1` preserves cofinality. -/
theorem CofinalValueFor.mul_left_of_le_one {v : Valuation A Γ₀}
    {H : Subgroup (valueGroup (.ofClass v))} {a b : A}
    (ha : CofinalValueFor v H a) (hb : v b ≤ 1) : CofinalValueFor v H (b * a) :=
  ha.of_le (by
    rw [map_mul]
    exact mul_le_of_le_one_left' hb)

/-- For a nonzero value, cofinality for `H` is cofinality of the corresponding element of
the value group: the bridge between the valuation-side and group-side predicates. -/
theorem cofinalValueFor_iff_isCofinalElement {v : Valuation A Γ₀}
    {H : Subgroup (valueGroup (.ofClass v))} {a : A}
    (h : (MonoidWithZeroHom.ofClass v) a ≠ 0) :
    CofinalValueFor v H a ↔
      TauCeti.IsCofinalElement H (valueGroup.mk (.ofClass v) 1 a (by simp) h) := by
  rw [cofinalValueFor_def, TauCeti.isCofinalElement_def]
  refine forall_congr' fun g ↦ forall_congr' fun _ ↦ exists_congr fun n ↦ ?_
  rw [v.restrict_eq_mk h, ← WithZero.coe_pow, WithZero.coe_lt_coe]

/-- **Wedhorn Lemma 7.1, the multiplicative step.** Below the strict-containment threshold
`cΓ_v < H`, cofinality for `H` is preserved by multiplication by an arbitrary ring element. -/
theorem CofinalValueFor.mul_left {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))}
    (hH : characteristicSubgroup v < H) {a : A} (ha : CofinalValueFor v H.toSubgroup a) (b : A) :
    CofinalValueFor v H.toSubgroup (b * a) := by
  rcases le_or_gt (v b) 1 with hb | hb
  · exact ha.mul_left_of_le_one hb
  · -- `v b > 1` is an attained value `≥ 1`, hence lies in `cΓ_v ⊊ H`.
    have hb0 : (MonoidWithZeroHom.ofClass v) b ≠ 0 := by
      simpa using (zero_lt_one.trans hb).ne'
    rcases eq_or_ne (v a) 0 with ha0' | ha0'
    · exact cofinalValueFor_of_eq_zero (by rw [map_mul, ha0', mul_zero])
    have ha0 : (MonoidWithZeroHom.ofClass v) a ≠ 0 := by simpa using ha0'
    have hab0 : (MonoidWithZeroHom.ofClass v) (b * a) ≠ 0 := by
      simpa [map_mul] using mul_ne_zero hb0 ha0
    have hmem : valueGroup.mk (.ofClass v) 1 b (by simp) hb0 ∈ characteristicSubgroup v :=
      valueGroup_mk_mem_characteristicSubgroup_of_one_le_value hb0 hb.le
    rw [cofinalValueFor_iff_isCofinalElement hab0]
    have := ((cofinalValueFor_iff_isCofinalElement ha0).mp ha).mul_of_lt_of_mem hH hmem
    have hmul : valueGroup.mk (.ofClass v) 1 b (by simp) hb0 *
        valueGroup.mk (.ofClass v) 1 a (by simp) ha0
        = valueGroup.mk (.ofClass v) 1 (b * a) (by simp) hab0 := by
      rw [valueGroup.mk_mul]; simp
    rw [← hmul]
    exact this

/-- A value bounded above by `h < 1` is cofinal for the convex subgroup `h` generates. This is
the inversion at the heart of Wedhorn's choice of `h := max { v t : t ∈ T }`: below `1` a
*larger* value generates a *smaller* convex subgroup, so the maximum yields the subgroup that
every generator is cofinal for. -/
theorem cofinalValueFor_closure_singleton_of_le {v : Valuation A Γ₀} {a : A}
    {h : valueGroup (.ofClass v)} (h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0)
    (hle : valueGroup.mk (.ofClass v) 1 a (by simp) h0 ≤ h) (hlt : h < 1) :
    CofinalValueFor v (TauCeti.ConvexSubgroup.closure {h}).toSubgroup a := by
  refine (cofinalValueFor_iff_isCofinalElement h0).mpr ?_
  have hgreatest : IsGreatest {valueGroup.mk (.ofClass v) 1 a (by simp) h0, h} h :=
    ⟨Set.mem_insert_of_mem _ rfl, by rintro x (rfl | rfl) <;> simp [hle]⟩
  exact (TauCeti.isGreatest_convexSubgroup_isCofinalElement hgreatest hlt).1 _
    (Set.mem_insert _ _)

/-- A cofinal value lies strictly below `1`. -/
theorem CofinalValueFor.lt_one {v : Valuation A Γ₀}
    {H : Subgroup (valueGroup (.ofClass v))} {a : A}
    (h : CofinalValueFor v H a) : v.restrict a < 1 := by
  rcases eq_or_ne ((MonoidWithZeroHom.ofClass v) a) 0 with h0 | h0
  · rw [v.restrict_eq_zero_iff.mpr (by simpa using h0)]
    exact zero_lt_one
  · rw [v.restrict_eq_mk h0, ← WithZero.coe_one, WithZero.coe_lt_coe]
    exact ((cofinalValueFor_iff_isCofinalElement h0).mp h).lt_one

/-- A power has cofinal value exactly when the element does (for a positive exponent):
the ingredient of `rad c = c` in Wedhorn Lemma 7.1. -/
@[simp]
theorem cofinalValueFor_pow_iff {v : Valuation A Γ₀}
    {H : Subgroup (valueGroup (.ofClass v))} {a : A} {m : ℕ} (hm : 0 < m) :
    CofinalValueFor v H (a ^ m) ↔ CofinalValueFor v H a := by
  constructor
  · intro h g hg
    obtain ⟨n, hn⟩ := h g hg
    refine ⟨m * n, ?_⟩
    rwa [map_pow, ← pow_mul] at hn
  · intro h g hg
    obtain ⟨n, hn⟩ := h g hg
    refine ⟨n, lt_of_le_of_lt ?_ hn⟩
    rw [map_pow, ← pow_mul]
    exact pow_le_pow_right_of_le_one' h.lt_one.le (Nat.le_mul_of_pos_left n hm)

/-- Cofinality for the whole value group is the ambient `CofinalValue`: the positive elements
of `ValueGroup₀` are exactly the coercions of the group elements. This is the bridge between
the subgroup-relative predicate here and the one already on `main`. -/
@[simp]
theorem cofinalValueFor_top_iff {v : Valuation A Γ₀} {a : A} :
    CofinalValueFor v ⊤ a ↔ CofinalValue v a := by
  rw [cofinalValueFor_def, cofinalValue_iff]
  constructor
  · intro h γ hγ
    obtain ⟨g, rfl⟩ := WithZero.ne_zero_iff_exists.mp hγ.ne'
    exact h g TauCeti.ConvexSubgroup.mem_top
  · intro h g _
    exact h (g : ValueGroup₀ (.ofClass v)) (by simp)

/-- `1` never has cofinal value: `v 1 = 1`, which is not below itself. Stated for the predicate
so that it needs only a ring — properness of the ideal below is a corollary. -/
@[simp]
theorem not_cofinalValueFor_one (v : Valuation A Γ₀)
    (H : Subgroup (valueGroup (.ofClass v))) : ¬ CofinalValueFor v H 1 :=
  fun h ↦ absurd h.lt_one (by simp)

/-! ### The ideal of cofinal values

`Ideal A` is `Submodule A A`, i.e. a *left* ideal, and `CofinalValueFor.mul_left` gives exactly left
absorption — which is exactly what `Ideal A = Submodule A A` asks for. So the ideal and its
membership and properness statements need only a ring; commutativity enters one step later,
at radicality, where Mathlib's `Ideal.IsRadical` requires it. Wedhorn states Lemma 7.1 over a
commutative ring, and it is `isRadical_cofinalIdeal` below that carries the lemma's name. -/

/-- The elements whose value is cofinal for `H`, as an ideal — a *left* ideal in general,
since `Ideal A` is `Submodule A A` and `CofinalValueFor.mul_left` supplies left absorption.
Over a commutative ring this is the ideal of **Wedhorn, Lemma 7.1**, whose radicality is
`isRadical_cofinalIdeal`. -/
def cofinalIdeal (v : Valuation A Γ₀)
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))}
    (hH : characteristicSubgroup v < H) : Ideal A where
  carrier := {a | CofinalValueFor v H.toSubgroup a}
  zero_mem' := cofinalValueFor_zero v H.toSubgroup
  add_mem' ha hb := CofinalValueFor.add ha hb
  smul_mem' b _ ha := CofinalValueFor.mul_left hH ha b

/-- Membership in the ideal is the cofinality predicate. This is the intended simp-normal form
for `cofinalIdeal`; `cofinalValueFor_def` deliberately does not unfold it further. -/
@[simp]
theorem mem_cofinalIdeal {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))}
    {hH : characteristicSubgroup v < H} {a : A} :
    a ∈ cofinalIdeal v hH ↔ CofinalValueFor v H.toSubgroup a :=
  Iff.rfl

/-- The ideal of cofinal values is proper: `1` has value `1`, which is not cofinal. -/
theorem cofinalIdeal_ne_top {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))}
    (hH : characteristicSubgroup v < H) : cofinalIdeal v hH ≠ ⊤ := fun htop ↦
  not_cofinalValueFor_one v H.toSubgroup (mem_cofinalIdeal.mp (htop ▸ Submodule.mem_top))

/-! ### Radicality -/

section CommRing

variable {A : Type*} [CommRing A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Wedhorn Lemma 7.1.** Over a commutative ring the ideal of cofinal values is radical.
Commutativity is needed only here, for Mathlib's `Ideal.IsRadical`. -/
theorem isRadical_cofinalIdeal {v : Valuation A Γ₀}
    {H : TauCeti.ConvexSubgroup (valueGroup (.ofClass v))}
    (hH : characteristicSubgroup v < H) : (cofinalIdeal v hH).IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
  rw [mem_cofinalIdeal] at hn ⊢
  rcases Nat.eq_zero_or_pos n with rfl | hp
  · rw [pow_zero] at hn
    exact absurd hn (not_cofinalValueFor_one v H.toSubgroup)
  · exact (cofinalValueFor_pow_iff hp).mp hn

end CommRing

end Valuation
