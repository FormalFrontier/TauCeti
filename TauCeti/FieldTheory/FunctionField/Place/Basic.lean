/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import TauCeti.RingTheory.Valuation.Discrete.Order

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
* `TauCeti.Place.ord_add_eq_min_of_ord_ne`: the strict triangle inequality (Stichtenoth,
  Lemma 1.1.11).
* `TauCeti.Place.valuation_eq_one_of_isAlgebraic`: every nonzero element that is algebraic over
  `k` is a unit of `𝒪_P`; equivalently, an element of nonzero order is transcendental over `k`
  (`TauCeti.Place.transcendental_of_ord_ne_zero`). In particular the constant field
  `algebraicClosure k F` is contained in `𝒪_P`
  (`TauCeti.Place.mem_integers_of_mem_algebraicClosure`).
* `TauCeti.Place.integers_injective`: a place is determined by its valuation ring
  (Stichtenoth, Theorem 1.1.13).
* `TauCeti.Place.degree_eq_one_iff_algebraMap_surjective` and
  `TauCeti.Place.degree_eq_one_iff_forall_exists_valuation_sub_lt_one`: the rational places are
  those whose residue field is exhausted by the constants, equivalently those at which every
  integral function agrees with a constant to first order;
  `TauCeti.Place.residueFieldEquivOfDegreeEqOne` identifies the residue field of such a place
  with `k`.

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
  valuation_surjective : Function.Surjective valuation
  /-- The valuation is trivial on the constants. -/
  isTrivialOn : valuation.IsTrivialOn k

namespace Place

variable {k F}

instance (P : Place k F) : P.valuation.IsTrivialOn k := P.isTrivialOn

variable (P : Place k F)

@[ext]
theorem ext {P Q : Place k F} (h : P.valuation = Q.valuation) : P = Q := by
  cases P
  cases Q
  congr

theorem valuation_injective : Function.Injective (valuation : Place k F → Valuation F ℤᵐ⁰) :=
  fun _ _ h => ext h

/-- The valuation ring `𝒪_P = {f : F | v_P f ≤ 1}` of a place (Stichtenoth,
Definition 1.1.4). -/
def integers : ValuationSubring F := P.valuation.valuationSubring

@[simp]
theorem mem_integers_iff {f : F} : f ∈ P.integers ↔ P.valuation f ≤ 1 := (Iff.rfl)

/-- The additive order function `ord_P : F → ℤ` of a place, normalized so that a prime element
has order `1`. It has the junk value `ord_P 0 = 0`. -/
noncomputable def ord (f : F) : ℤ := Valuation.ord P.valuation f

theorem ord_def (f : F) : P.ord f = -WithZero.log (P.valuation f) :=
  Valuation.ord_def P.valuation f

/-- The translation between the multiplicative and additive views of a place. -/
theorem valuation_eq_exp_neg_ord {f : F} (hf : f ≠ 0) :
    P.valuation f = WithZero.exp (-P.ord f) :=
  Valuation.valuation_eq_exp_neg_ord P.valuation hf

theorem ord_eq_iff_valuation_eq_exp_neg {f : F} (hf : f ≠ 0) {n : ℤ} :
    P.ord f = n ↔ P.valuation f = WithZero.exp (-n) :=
  Valuation.ord_eq_iff_valuation_eq_exp_neg P.valuation hf

@[simp]
theorem ord_zero : P.ord 0 = 0 := Valuation.ord_zero P.valuation

@[simp]
theorem ord_one : P.ord 1 = 0 := Valuation.ord_one P.valuation

theorem ord_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) : P.ord (f * g) = P.ord f + P.ord g :=
  Valuation.ord_mul P.valuation hf hg

@[simp]
theorem ord_inv (f : F) : P.ord f⁻¹ = -P.ord f := Valuation.ord_inv P.valuation f

@[simp]
theorem ord_zpow (f : F) (n : ℤ) : P.ord (f ^ n) = n * P.ord f :=
  Valuation.ord_zpow P.valuation f n

@[simp]
theorem ord_pow (f : F) (n : ℕ) : P.ord (f ^ n) = n * P.ord f :=
  Valuation.ord_pow P.valuation f n

theorem ord_div {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    P.ord (f / g) = P.ord f - P.ord g := Valuation.ord_div P.valuation hf hg

@[simp]
theorem ord_neg (f : F) : P.ord (-f) = P.ord f := Valuation.ord_neg P.valuation f

/-- The order of a quotient by an integral power. -/
theorem ord_div_zpow {f t : F} (hf : f ≠ 0) (ht : t ≠ 0) (n : ℤ) :
    P.ord (f / t ^ n) = P.ord f - n * P.ord t :=
  Valuation.ord_div_zpow P.valuation hf ht n

theorem ord_surjective : Function.Surjective P.ord :=
  Valuation.ord_surjective P.valuation P.valuation_surjective

theorem mem_integers_iff_ord_nonneg {f : F} : f ∈ P.integers ↔ 0 ≤ P.ord f :=
  Valuation.mem_valuationSubring_iff_ord_nonneg P.valuation

/-- The ultrametric inequality, in additive form. The hypothesis `f + g ≠ 0` guards the junk
value `ord_P 0 = 0`. -/
theorem min_ord_le_ord_add {f g : F} (h : f + g ≠ 0) :
    min (P.ord f) (P.ord g) ≤ P.ord (f + g) :=
  Valuation.min_ord_le_ord_add P.valuation h

/-- The **strict triangle inequality** (Stichtenoth, Lemma 1.1.11): if two nonzero elements
have distinct orders, the order of their sum is the smaller of the two. -/
theorem ord_add_eq_min_of_ord_ne {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : P.ord f ≠ P.ord g) : P.ord (f + g) = min (P.ord f) (P.ord g) :=
  Valuation.ord_add_eq_min_of_ord_ne P.valuation hf hg h

section Constants

@[simp]
theorem ord_algebraMap (c : k) : P.ord (algebraMap k F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · simp [ord_def, P.isTrivialOn.eq_one c hc]

theorem algebraMap_mem_integers (c : k) : algebraMap k F c ∈ P.integers :=
  P.mem_integers_iff.mpr (IsTrivialOn.valuation_algebraMap_le_one P.valuation c)

/-- Every nonzero element algebraic over the constants has valuation one. This is the
contrapositive of Mathlib's `Valuation.transcendental_of_ne_one`. -/
theorem valuation_eq_one_of_isAlgebraic {f : F} (hf : IsAlgebraic k f) (hf0 : f ≠ 0) :
    P.valuation f = 1 := by
  by_contra h
  exact P.valuation.transcendental_of_ne_one k f hf0 h hf

/-- Elements algebraic over the constants have order zero at every place. -/
theorem ord_eq_zero_of_isAlgebraic {f : F} (hf : IsAlgebraic k f) : P.ord f = 0 := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · simp [ord_def, P.valuation_eq_one_of_isAlgebraic hf hf0]

/-- An element of nonzero order is transcendental over the constants. -/
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
  Valuation.valueGroup_eq_top_of_surjective P.valuation P.valuation_surjective

instance : Nontrivial (valueGroup (.ofClass P.valuation)) :=
  Valuation.nontrivial_valueGroup_of_surjective P.valuation P.valuation_surjective

/-- **The valuation ring of a place is a discrete valuation ring** (Stichtenoth,
Theorem 1.1.6). -/
instance instIsDiscreteValuationRing : IsDiscreteValuationRing P.integers :=
  Valuation.valuationSubring_isDiscreteValuationRing_of_surjective
    P.valuation P.valuation_surjective

/-- The generator of the value group singled out by Mathlib's discreteness API is
`WithZero.exp (-1)`, because the valuation of a place is normalized. -/
theorem generator_eq_exp_neg_one : IsRankOneDiscrete.generator P.valuation =
    Units.mk0 (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) (by simp) :=
  Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective P.valuation_surjective

/-- Mathlib's uniformizers of `v_P` are exactly the elements of order one: Stichtenoth's prime
elements for `P`. -/
@[simp]
theorem isUniformizer_iff_ord_eq_one {t : F} : P.valuation.IsUniformizer t ↔ P.ord t = 1 :=
  Valuation.isUniformizer_iff_ord_eq_one_of_surjective
    P.valuation P.valuation_surjective

theorem exists_isUniformizer : ∃ t : F, P.valuation.IsUniformizer t :=
  Valuation.exists_isUniformizer_of_surjective P.valuation P.valuation_surjective

theorem isUnit_iff_valuation_eq_one {x : P.integers} : IsUnit x ↔ P.valuation (x : F) = 1 :=
  Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.valuationSubring.integers P.valuation)

theorem isUnit_iff_ord_eq_zero {x : P.integers} (hx : (x : F) ≠ 0) :
    IsUnit x ↔ P.ord (x : F) = 0 :=
  Valuation.isUnit_iff_ord_eq_zero P.valuation hx

/-- **Existence half of Stichtenoth, Theorem 1.1.6(b)**: relative to a prime element `t` for
`P`, every nonzero `f : F` is `t ^ (ord_P f)` times a unit of `𝒪_P`. -/
theorem exists_eq_zpow_mul_unit {t : F} (ht : P.valuation.IsUniformizer t) {f : F} (hf : f ≠ 0) :
    ∃ u : P.integersˣ, f = t ^ P.ord f * (u : F) :=
  Valuation.exists_eq_zpow_mul_unit_of_surjective
    P.valuation P.valuation_surjective ht hf

end Discrete

section IntegersOrder

theorem mem_maximalIdeal_iff_valuation_lt_one {f : P.integers} :
    f ∈ IsLocalRing.maximalIdeal P.integers ↔ P.valuation (f : F) < 1 :=
  Valuation.mem_maximalIdeal_iff (v := P.valuation)

theorem mem_maximalIdeal_iff_ord_pos {f : P.integers} (hf : (f : F) ≠ 0) :
    f ∈ IsLocalRing.maximalIdeal P.integers ↔ 0 < P.ord (f : F) :=
  Valuation.mem_maximalIdeal_iff_ord_pos P.valuation hf

/-- The valuation ring of a place is a proper subring of `F` (Stichtenoth,
Definition 1.1.4). -/
theorem integers_ne_top : P.integers ≠ ⊤ :=
  Valuation.valuationSubring_ne_top_of_surjective P.valuation P.valuation_surjective

/-- A place is determined by its valuation: two places whose valuations are equivalent are
equal. This is the payoff of normalizing the value group, and half of Stichtenoth's
Theorem 1.1.13. -/
theorem eq_of_isEquiv {P Q : Place k F} (h : P.valuation.IsEquiv Q.valuation) : P = Q :=
  ext (Valuation.eq_of_isEquiv_of_surjective
    P.valuation_surjective Q.valuation_surjective h)

@[simp]
theorem valuation_isEquiv_iff {P Q : Place k F} : P.valuation.IsEquiv Q.valuation ↔ P = Q := by
  refine ⟨eq_of_isEquiv, ?_⟩
  rintro rfl
  exact Valuation.IsEquiv.refl

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

/-- Evaluation at a place vanishes exactly on elements of positive valuation. -/
theorem residue_eq_zero_iff_valuation_lt_one {f : P.integers} :
    IsLocalRing.residue P.integers f = 0 ↔ P.valuation (f : F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, P.mem_maximalIdeal_iff_valuation_lt_one]

/-- Evaluation at a place vanishes on a nonzero function exactly when that function has
positive order: the additive form of `TauCeti.Place.residue_eq_zero_iff_valuation_lt_one`. -/
theorem residue_eq_zero_iff_ord_pos {f : P.integers} (hf : (f : F) ≠ 0) :
    IsLocalRing.residue P.integers f = 0 ↔ 0 < P.ord (f : F) := by
  rw [IsLocalRing.residue_eq_zero_iff, P.mem_maximalIdeal_iff_ord_pos hf]

/-- The **degree** `deg P = [F_P : k]` of a place (Stichtenoth, Definition 1.1.14). Its
finiteness, which guards the junk value of `Module.finrank`, holds whenever `F/k` is a function
field: see `TauCeti.Place.finiteDimensional_residueField` (Stichtenoth,
Proposition 1.1.15). -/
noncomputable def degree : ℕ := Module.finrank k P.ResidueField

theorem degree_eq_finrank : P.degree = Module.finrank k P.ResidueField := (rfl)

theorem one_le_degree [Module.Finite k P.ResidueField] : 1 ≤ P.degree := by
  rw [degree_eq_finrank]
  exact Module.finrank_pos

/-- A place has degree one exactly when every residue is the residue of a constant: the
**rational** places (Stichtenoth, Definition 1.1.14). -/
theorem degree_eq_one_iff_algebraMap_surjective :
    P.degree = 1 ↔ Function.Surjective (algebraMap k P.ResidueField) := by
  rw [degree_eq_finrank, Algebra.finrank_eq_one_iff_bijective_algebraMap]
  exact ⟨And.right, fun h ↦ ⟨FaithfulSMul.algebraMap_injective k _, h⟩⟩

/-- A place is rational exactly when every function integral at `P` agrees with a constant to
first order: this is the sense in which the value `f(P)` of a function at a rational place is
an element of `k`. The multiplicative form avoids the junk value `ord_P 0 = 0`, which occurs
here whenever `f` is itself a constant. -/
theorem degree_eq_one_iff_forall_exists_valuation_sub_lt_one :
    P.degree = 1 ↔
      ∀ f ∈ P.integers, ∃ c : k, P.valuation (f - algebraMap k F c) < 1 := by
  have hsub : ∀ (a : P.integers) (c : k),
      ((a - algebraMap k P.integers c : P.integers) : F) = (a : F) - algebraMap k F c :=
    fun a c ↦ by
      rw [← ValuationSubring.algebraMap_apply P.integers (a - algebraMap k P.integers c),
        _root_.map_sub, ← IsScalarTower.algebraMap_apply k P.integers F,
        ValuationSubring.algebraMap_apply]
  have key : ∀ (a : P.integers) (c : k),
      P.valuation ((a : F) - algebraMap k F c) < 1 ↔
        IsLocalRing.residue P.integers a = algebraMap k P.ResidueField c := by
    intro a c
    rw [← hsub a c, ← P.residue_eq_zero_iff_valuation_lt_one, _root_.map_sub, sub_eq_zero]
    rw [IsScalarTower.algebraMap_apply k P.integers P.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]
  rw [degree_eq_one_iff_algebraMap_surjective]
  constructor
  · intro h f hf
    obtain ⟨c, hc⟩ := h (IsLocalRing.residue P.integers ⟨f, hf⟩)
    exact ⟨c, (key ⟨f, hf⟩ c).mpr hc.symm⟩
  · intro h y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨c, hc⟩ := h (a : F) a.2
    exact ⟨c, ((key a c).mp hc).symm⟩

/-- **A rational place has residue field `k`**: at a place of degree one the constants map
isomorphically onto the residue field, so `f(P)` really is an element of `k`. -/
noncomputable def residueFieldEquivOfDegreeEqOne (h : P.degree = 1) : k ≃ₐ[k] P.ResidueField :=
  AlgEquiv.ofBijective (Algebra.ofId k P.ResidueField)
    ⟨(algebraMap k P.ResidueField).injective,
      (degree_eq_one_iff_algebraMap_surjective P).mp h⟩

@[simp]
theorem residueFieldEquivOfDegreeEqOne_apply (h : P.degree = 1) (c : k) :
    residueFieldEquivOfDegreeEqOne P h c = algebraMap k P.ResidueField c :=
  AlgEquiv.ofBijective_apply _ _ _

/-- If the residue field of a place is algebraic over an algebraically closed field of constants,
then the place is rational (Stichtenoth, Remark 1.1.17). -/
theorem degree_eq_one_of_isAlgClosed_of_isIntegral [IsAlgClosed k]
    [Algebra.IsIntegral k P.ResidueField] : P.degree = 1 :=
  (degree_eq_one_iff_algebraMap_surjective P).mpr
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2

end ResidueField

end Place

end TauCeti
