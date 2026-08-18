/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.IsTrivialOn

/-!
# Places of an algebraic function field

A *place* of a field extension `F/k` is a normalized discrete valuation of `F` that is trivial
on `k`: a valuation `v : Valuation F ℤᵐ⁰` which is surjective and satisfies `v c = 1` for every
nonzero constant `c`. This is the object Stichtenoth introduces in
*Algebraic Function Fields and Codes*, Definitions 1.1.4 and 1.1.9, presented here in the
normalized form: because the value group is pinned to be all of `ℤᵐ⁰`, no quotient by valuation
equivalence is needed and equality of places *is* equality of valuations
(`TauCeti.Place.eq_of_isEquiv`).

## Main definitions

* `TauCeti.Place k F`: a place of `F/k`.
* `TauCeti.Place.integers`: the valuation ring `𝒪_P ⊆ F` of a place.
* `TauCeti.Place.ord`: the additive order function `ord_P : F → ℤ`, normalized so that a prime
  element has order `1`. It has the junk value `ord_P 0 = 0`.
* `TauCeti.Place.ResidueField`: the residue field `F_P = 𝒪_P / 𝔪_P`, a `k`-algebra.
* `TauCeti.Place.degree`: the degree `deg P = [F_P : k]` of a place.

## Main results

* `TauCeti.Place.instIsDiscreteValuationRing`: `𝒪_P` is a discrete valuation ring
  (Stichtenoth, Theorem 1.1.6), with `TauCeti.Place.isUniformizer_iff_ord_eq_one` identifying
  Mathlib's uniformizers as the elements of order one — Stichtenoth's prime elements — and
  `TauCeti.Place.exists_eq_zpow_mul_unit` writing every nonzero `f : F` as `t ^ (ord_P f)` times
  a unit of `𝒪_P`.
* `TauCeti.Place.ord_add_of_ord_ne`: the strict triangle inequality (Stichtenoth,
  Lemma 1.1.11).
* `TauCeti.Place.valuation_eq_one_of_isAlgebraic`: every nonzero element that is algebraic over
  `k` is a unit of `𝒪_P`; equivalently, an element of nonzero order is transcendental over `k`
  (`TauCeti.Place.transcendental_of_ord_ne_zero`). In particular the constant field
  `algebraicClosure k F` is contained in `𝒪_P`
  (`TauCeti.Place.mem_integers_of_mem_algebraicClosure`).
* `TauCeti.Place.integers_injective`: a place is determined by its valuation ring
  (Stichtenoth, Theorem 1.1.13).

## Implementation notes

Mathlib's multiplicative convention is used throughout: `𝒪_P` is `{f | v_P f ≤ 1}` and a prime
element `t` has `v_P t = WithZero.exp (-1)`, so that `ord_P t = 1`. The translation between the
two views is `TauCeti.Place.valuation_eq_exp_neg_ord`. Because `WithZero.log 0 = 0`, the order
function has the junk value `ord_P 0 = 0`; statements about `ord_P f` therefore carry `f ≠ 0`
whenever the junk value would falsify them, and the junk-free multiplicative form is stated
alongside where both are useful.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.1.
-/

public section

open scoped WithZero

open MonoidWithZeroHom Valuation

namespace TauCeti

universe u v

variable (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F]

/-- A **place** of the field extension `F/k` is a normalized discrete valuation of `F` that is
trivial on the constants: a `ℤᵐ⁰`-valued valuation which is surjective — so that its value
group is exactly `ℤ` — and which takes the value `1` on every nonzero element of `k`.

Normalization removes the need to quotient by valuation equivalence: two places are equal as
soon as their valuations are equivalent (`TauCeti.Place.eq_of_isEquiv`). -/
structure Place where
  /-- The normalized valuation of the place. Following Mathlib's multiplicative convention,
  the elements of the valuation ring are those with `valuation f ≤ 1`, and a prime element `t`
  satisfies `valuation t = WithZero.exp (-1)`. -/
  valuation : Valuation F ℤᵐ⁰
  /-- The valuation is surjective, i.e. normalized: its value group is all of `ℤᵐ⁰`. -/
  surjective_valuation : Function.Surjective valuation
  /-- The valuation is trivial on the constants. -/
  isTrivialOn : valuation.IsTrivialOn k

namespace Place

variable {k F}

instance (P : Place k F) : P.valuation.IsTrivialOn k := P.isTrivialOn

variable (P : Place k F)

@[ext]
theorem ext {P Q : Place k F} (h : P.valuation = Q.valuation) : P = Q := by
  cases P; cases Q; congr

theorem valuation_injective : Function.Injective (valuation : Place k F → Valuation F ℤᵐ⁰) :=
  fun _ _ h => ext h

/-- The valuation ring `𝒪_P = {f : F | v_P f ≤ 1}` of a place (Stichtenoth,
Definition 1.1.5). -/
def integers : ValuationSubring F := P.valuation.valuationSubring

@[simp]
theorem mem_integers_iff {f : F} : f ∈ P.integers ↔ P.valuation f ≤ 1 := (Iff.rfl)

/-- The additive order function `ord_P : F → ℤ` of a place, normalized so that a prime element
has order `1`. ⚠ It carries the junk value `ord_P 0 = 0`, inherited from
`WithZero.log 0 = 0`. -/
noncomputable def ord (f : F) : ℤ := -WithZero.log (P.valuation f)

theorem ord_def (f : F) : P.ord f = -WithZero.log (P.valuation f) := (rfl)

/-- The translation between the multiplicative and the additive view of a place. -/
theorem valuation_eq_exp_neg_ord {f : F} (hf : f ≠ 0) :
    P.valuation f = WithZero.exp (-P.ord f) := by
  rw [ord_def, neg_neg, WithZero.exp_log (P.valuation.ne_zero_iff.mpr hf)]

theorem ord_eq_iff_valuation_eq_exp {f : F} (hf : f ≠ 0) {n : ℤ} :
    P.ord f = n ↔ P.valuation f = WithZero.exp (-n) := by
  rw [P.valuation_eq_exp_neg_ord hf, WithZero.exp_inj, neg_inj]

@[simp]
theorem ord_zero : P.ord 0 = 0 := by simp [ord_def]

@[simp]
theorem ord_one : P.ord 1 = 0 := by simp [ord_def]

theorem ord_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) : P.ord (f * g) = P.ord f + P.ord g := by
  rw [ord_def, ord_def, ord_def, map_mul,
    WithZero.log_mul (P.valuation.ne_zero_iff.mpr hf) (P.valuation.ne_zero_iff.mpr hg)]
  ring

@[simp]
theorem ord_inv (f : F) : P.ord f⁻¹ = -P.ord f := by
  simp [ord_def, map_inv₀, WithZero.log_inv]

@[simp]
theorem ord_zpow (f : F) (n : ℤ) : P.ord (f ^ n) = n * P.ord f := by
  simp [ord_def, map_zpow₀, WithZero.log_zpow, mul_neg]

@[simp]
theorem ord_pow (f : F) (n : ℕ) : P.ord (f ^ n) = n * P.ord f := by
  simpa using P.ord_zpow f n

theorem ord_div {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) : P.ord (f / g) = P.ord f - P.ord g := by
  rw [div_eq_mul_inv, P.ord_mul hf (inv_ne_zero hg), ord_inv, sub_eq_add_neg]

@[simp]
theorem ord_neg (f : F) : P.ord (-f) = P.ord f := by simp [ord_def, Valuation.map_neg]

theorem ord_surjective : Function.Surjective P.ord := fun n => by
  obtain ⟨f, hf⟩ := P.surjective_valuation (WithZero.exp (-n))
  have hf0 : f ≠ 0 := P.valuation.ne_zero_iff.mp (by simp [hf])
  exact ⟨f, (P.ord_eq_iff_valuation_eq_exp hf0).mpr hf⟩

theorem mem_integers_iff_ord {f : F} : f ∈ P.integers ↔ 0 ≤ P.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [mem_integers_iff, P.valuation_eq_exp_neg_ord hf, ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    omega

/-- The ultrametric inequality, in additive form. The hypothesis `f + g ≠ 0` guards the junk
value `ord_P 0 = 0`. -/
theorem min_ord_le_ord_add {f g : F} (h : f + g ≠ 0) :
    min (P.ord f) (P.ord g) ≤ P.ord (f + g) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hmono : Monotone (WithZero.exp : ℤ → ℤᵐ⁰) := fun _ _ h => WithZero.exp_le_exp.mpr h
  have hadd := P.valuation.map_add f g
  rw [P.valuation_eq_exp_neg_ord hf, P.valuation_eq_exp_neg_ord hg,
    P.valuation_eq_exp_neg_ord h, ← hmono.map_max, WithZero.exp_le_exp] at hadd
  omega

/-- The **strict triangle inequality** (Stichtenoth, Lemma 1.1.11): if two nonzero elements
have distinct orders, the order of their sum is the smaller of the two. -/
theorem ord_add_of_ord_ne {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : P.ord f ≠ P.ord g) :
    P.ord (f + g) = min (P.ord f) (P.ord g) := by
  have hne : P.valuation f ≠ P.valuation g := by
    rw [P.valuation_eq_exp_neg_ord hf, P.valuation_eq_exp_neg_ord hg]
    simpa using h
  have hsum := P.valuation.map_add_of_distinct_val hne
  have hfg : f + g ≠ 0 := by
    refine P.valuation.ne_zero_iff.mp ?_
    rw [hsum]
    exact ne_of_gt (lt_max_of_lt_left (zero_lt_iff.mpr (P.valuation.ne_zero_iff.mpr hf)))
  have hmono : Monotone (WithZero.exp : ℤ → ℤᵐ⁰) := fun _ _ h => WithZero.exp_le_exp.mpr h
  rw [P.valuation_eq_exp_neg_ord hf, P.valuation_eq_exp_neg_ord hg,
    P.valuation_eq_exp_neg_ord hfg, ← hmono.map_max, WithZero.exp_inj] at hsum
  omega

section Constants

theorem valuation_algebraMap {c : k} (hc : c ≠ 0) : P.valuation (algebraMap k F c) = 1 :=
  P.isTrivialOn.eq_one c hc

@[simp]
theorem ord_algebraMap (c : k) : P.ord (algebraMap k F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · simp [ord_def, P.valuation_algebraMap hc]

theorem algebraMap_mem_integers (c : k) : algebraMap k F c ∈ P.integers :=
  P.mem_integers_iff.mpr (IsTrivialOn.valuation_algebraMap_le_one P.valuation c)

/-- Every nonzero element that is algebraic over the constants is a unit of `𝒪_P`
(Stichtenoth, Corollary 1.1.20: the constants are regular and nonvanishing everywhere). This
is the contrapositive of Mathlib's `Valuation.transcendental_of_ne_one`. -/
theorem valuation_eq_one_of_isAlgebraic {f : F} (hf : IsAlgebraic k f) (hf0 : f ≠ 0) :
    P.valuation f = 1 := by
  by_contra h
  exact P.valuation.transcendental_of_ne_one k f hf0 h hf

/-- Elements algebraic over the constants have order zero at every place. -/
theorem ord_eq_zero_of_isAlgebraic {f : F} (hf : IsAlgebraic k f) : P.ord f = 0 := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · simp [ord_def, P.valuation_eq_one_of_isAlgebraic hf hf0]

/-- An element of nonzero order is transcendental over the constants; in particular a prime
element for `P` is (Stichtenoth, Theorem 1.1.6). -/
theorem transcendental_of_ord_ne_zero {f : F} (hf : P.ord f ≠ 0) : Transcendental k f :=
  fun h => hf (P.ord_eq_zero_of_isAlgebraic h)

/-- The constant field `algebraicClosure k F` is contained in the valuation ring of every
place: constants are everywhere regular. -/
theorem mem_integers_of_mem_algebraicClosure {f : F} (hf : f ∈ algebraicClosure k F) :
    f ∈ P.integers := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  · exact P.mem_integers_iff.mpr
      (le_of_eq (P.valuation_eq_one_of_isAlgebraic (mem_algebraicClosure_iff.mp hf) hf0))

end Constants

section Discrete

/-- Normalization says exactly that the value group of a place is all of `ℤᵐ⁰`. -/
theorem valueGroup_eq_top : valueGroup (.ofClass P.valuation) = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun γ => mem_valueGroup _ (P.surjective_valuation γ)

instance : Nontrivial (valueGroup (.ofClass P.valuation)) := by
  rw [P.valueGroup_eq_top]
  exact (Subgroup.topEquiv (G := ℤᵐ⁰ˣ)).toEquiv.nontrivial

instance : IsCyclic (valueGroup (.ofClass P.valuation)) :=
  have : IsCyclic ℤᵐ⁰ˣ :=
    isCyclic_of_surjective WithZero.unitsWithZeroEquiv.symm
      WithZero.unitsWithZeroEquiv.symm.surjective
  Subgroup.isCyclic _

/-- **The valuation ring of a place is a discrete valuation ring** (Stichtenoth,
Theorem 1.1.6). -/
instance instIsDiscreteValuationRing : IsDiscreteValuationRing P.integers :=
  Valuation.valuationSubring_isDiscreteValuationRing P.valuation

/-- The generator of the value group singled out by Mathlib's discreteness API is
`WithZero.exp (-1)`, because the valuation of a place is normalized. -/
theorem generator_eq_exp_neg_one : IsRankOneDiscrete.generator P.valuation =
    Units.mk0 (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) (by simp) :=
  IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective P.surjective_valuation

/-- Mathlib's uniformizers of `v_P` are exactly the elements of order one: Stichtenoth's prime
elements for `P`. -/
@[simp]
theorem isUniformizer_iff_ord_eq_one {t : F} : P.valuation.IsUniformizer t ↔ P.ord t = 1 := by
  rcases eq_or_ne t 0 with rfl | ht
  · refine iff_of_false ?_ (by simp)
    simp only [Valuation.IsUniformizer, P.generator_eq_exp_neg_one, map_zero, Units.val_mk0]
    exact fun h => WithZero.exp_ne_zero h.symm
  · rw [Valuation.IsUniformizer, P.generator_eq_exp_neg_one, P.ord_eq_iff_valuation_eq_exp ht]
    exact Iff.rfl

theorem exists_isUniformizer : ∃ t : F, P.valuation.IsUniformizer t := by
  obtain ⟨t, ht⟩ := P.ord_surjective 1
  exact ⟨t, P.isUniformizer_iff_ord_eq_one.mpr ht⟩

theorem isUnit_iff_valuation_eq_one {x : P.integers} : IsUnit x ↔ P.valuation (x : F) = 1 :=
  Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.valuationSubring.integers P.valuation)

theorem isUnit_iff_ord_eq_zero {x : P.integers} (hx : (x : F) ≠ 0) :
    IsUnit x ↔ P.ord (x : F) = 0 := by
  rw [P.isUnit_iff_valuation_eq_one, P.ord_eq_iff_valuation_eq_exp hx, neg_zero,
    WithZero.exp_zero]

/-- **Stichtenoth, Theorem 1.1.6(b)**: relative to a prime element `t` for `P`, every nonzero
`f : F` is `t ^ (ord_P f)` times a unit of `𝒪_P`. The exponent is forced, since units have
order zero. -/
theorem exists_eq_zpow_mul_unit {t : F} (ht : P.valuation.IsUniformizer t) {f : F} (hf : f ≠ 0) :
    ∃ u : P.integersˣ, f = t ^ P.ord f * (u : F) := by
  have ht1 : P.ord t = 1 := P.isUniformizer_iff_ord_eq_one.mp ht
  have ht0 : t ≠ 0 := fun h => by simp [h] at ht1
  have hne : f / t ^ P.ord f ≠ 0 := div_ne_zero hf (zpow_ne_zero _ ht0)
  have hord : P.ord (f / t ^ P.ord f) = 0 := by
    rw [P.ord_div hf (zpow_ne_zero _ ht0), ord_zpow, ht1]
    ring
  have hmem : f / t ^ P.ord f ∈ P.integers := P.mem_integers_iff_ord.mpr hord.ge
  have hunit : IsUnit (⟨_, hmem⟩ : P.integers) := (P.isUnit_iff_ord_eq_zero hne).mpr hord
  refine ⟨hunit.unit, ?_⟩
  have : ((hunit.unit : P.integers) : F) = f / t ^ P.ord f := by rw [IsUnit.unit_spec]
  rw [this]
  field_simp

end Discrete

section IntegersOrder

theorem mem_maximalIdeal_iff_valuation_lt_one {f : P.integers} :
    f ∈ IsLocalRing.maximalIdeal P.integers ↔ P.valuation (f : F) < 1 :=
  Valuation.mem_maximalIdeal_iff (v := P.valuation)

theorem mem_maximalIdeal_iff_ord {f : P.integers} (hf : (f : F) ≠ 0) :
    f ∈ IsLocalRing.maximalIdeal P.integers ↔ 0 < P.ord (f : F) := by
  rw [P.mem_maximalIdeal_iff_valuation_lt_one, P.valuation_eq_exp_neg_ord hf,
    ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

/-- The valuation ring of a place is a proper subring of `F` (Stichtenoth,
Definition 1.1.4). -/
theorem integers_ne_top : P.integers ≠ ⊤ := by
  obtain ⟨t, ht⟩ := P.ord_surjective 1
  intro h
  have ht' : t⁻¹ ∈ P.integers := h ▸ ValuationSubring.mem_top _
  rw [P.mem_integers_iff_ord, ord_inv, ht] at ht'
  omega

/-- A place is determined by its valuation: two places whose valuations are equivalent are
equal. This is the payoff of normalizing the value group, and half of Stichtenoth's
Theorem 1.1.13. -/
theorem eq_of_isEquiv {P Q : Place k F} (h : P.valuation.IsEquiv Q.valuation) : P = Q := by
  -- The two valuation rings agree, hence so do the signs of the two order functions.
  have hmem : ∀ f : F, 0 ≤ P.ord f ↔ 0 ≤ Q.ord f := fun f => by
    rw [← P.mem_integers_iff_ord, ← Q.mem_integers_iff_ord, mem_integers_iff, mem_integers_iff]
    exact h.le_one_iff_le_one
  have hle : ∀ f : F, P.ord f ≤ 0 ↔ Q.ord f ≤ 0 := fun f => by
    have := hmem f⁻¹
    rw [ord_inv, ord_inv] at this
    omega
  have hzero : ∀ f : F, P.ord f = 0 ↔ Q.ord f = 0 := fun f => by
    have h₁ := hmem f
    have h₂ := hle f
    omega
  -- A prime element for `P` is a prime element for `Q`.
  obtain ⟨t, ht⟩ := P.ord_surjective 1
  obtain ⟨s, hs⟩ := Q.ord_surjective 1
  have ht0 : t ≠ 0 := fun h => by simp [h] at ht
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have htQ : 1 ≤ Q.ord t := by
    have h₁ := (hmem t).mp (by omega)
    have h₂ := (hzero t).not.mp (by omega)
    omega
  have hsP : 1 ≤ P.ord s := by
    have h₁ := (hmem s).mpr (by omega)
    have h₂ := (hzero s).not.mpr (by omega)
    omega
  have hone : Q.ord t = 1 := by
    have hst : P.ord (s / t ^ P.ord s) = 0 := by
      rw [P.ord_div hs0 (zpow_ne_zero _ ht0), ord_zpow, ht]
      ring
    have hQ := (hzero _).mp hst
    rw [Q.ord_div hs0 (zpow_ne_zero _ ht0), ord_zpow, hs] at hQ
    nlinarith [htQ, hsP]
  -- Hence the two order functions agree, and so do the two valuations.
  refine ext (Valuation.ext fun f => ?_)
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have key : Q.ord f = P.ord f := by
    have h₀ : P.ord (f / t ^ P.ord f) = 0 := by
      rw [P.ord_div hf (zpow_ne_zero _ ht0), ord_zpow, ht]
      ring
    have hQ := (hzero _).mp h₀
    rw [Q.ord_div hf (zpow_ne_zero _ ht0), ord_zpow, hone] at hQ
    omega
  rw [P.valuation_eq_exp_neg_ord hf, Q.valuation_eq_exp_neg_ord hf, key]

/-- A place is determined by its valuation ring (Stichtenoth, Theorem 1.1.13). -/
theorem integers_injective : Function.Injective (integers : Place k F → ValuationSubring F) :=
  fun _ _ h => eq_of_isEquiv ((Valuation.isEquiv_iff_valuationSubring _ _).mpr h)

end IntegersOrder

section ResidueField

/-- Constants are integral at every place, so `𝒪_P` is a `k`-algebra. -/
noncomputable instance : Algebra k P.integers :=
  ((algebraMap k F).codRestrict P.integers P.algebraMap_mem_integers).toAlgebra

instance : IsScalarTower k P.integers F :=
  .of_algebraMap_eq fun _ => rfl

/-- The residue field `F_P = 𝒪_P / 𝔪_P` of a place (Stichtenoth, Definition 1.1.14). The
evaluation map `f ↦ f(P)` is `IsLocalRing.residue P.integers`. -/
noncomputable abbrev ResidueField : Type v := IsLocalRing.ResidueField P.integers

noncomputable instance : Algebra k P.ResidueField :=
  ((IsLocalRing.residue P.integers).comp (algebraMap k P.integers)).toAlgebra

instance : IsScalarTower k P.integers P.ResidueField :=
  .of_algebraMap_eq fun _ => rfl

@[simp]
theorem not_isUnit_iff_valuation_lt_one {f : P.integers} :
    ¬IsUnit f ↔ P.valuation (f : F) < 1 :=
  Valuation.Integer.not_isUnit_iff_valuation_lt_one

/-- The **degree** `deg P = [F_P : k]` of a place (Stichtenoth, Definition 1.1.14). Its
finiteness, which guards the junk value of `Module.finrank`, holds whenever `F/k` is a function
field (Stichtenoth, Proposition 1.1.15). -/
noncomputable def degree : ℕ := Module.finrank k P.ResidueField

@[simp]
theorem degree_eq_finrank : P.degree = Module.finrank k P.ResidueField := (rfl)

theorem one_le_degree [Module.Finite k P.ResidueField] : 1 ≤ P.degree := by
  rw [degree_eq_finrank]
  exact Module.finrank_pos

end ResidueField

end Place

end TauCeti
