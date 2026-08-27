/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus

/-!
# Holomorphy rings of an algebraic function field

A set `S` of places of an algebraic function field `F / k` cuts out the ring

`𝒪_S = ⋂_{P ∈ S} 𝒪_P`

of functions regular at every place of `S` — its **holomorphy ring**.  Two extreme cases are
already known: `𝒪_∅ = F`, and `𝒪_{ℙ_F}` is the constant field `algebraicClosure k F`, which is
Stichtenoth's Corollary 1.1.20.  This file constructs `𝒪_S` in general and proves the two
theorems that make the construction a dictionary: `𝒪_S` is integrally closed in `F`, and
*every* `k`-subalgebra of `F` integrally closed in `F` arises this way, from the set of places
at which its functions are regular.  The two constructions are mutually inverse, since `S` is
recovered from `𝒪_S` as the set of places at which every function of `𝒪_S` is regular.

Whenever some place lies outside `S`, the field `F` is the field of fractions of `𝒪_S`, so a
holomorphy ring of a proper set of places is a `k`-subalgebra of `F` with the same function field
— the shape the affine models of `TauCeti/FieldTheory/FunctionField/AffineModel/` are built on.

The mathematics is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section III.2.
None of it needs an exactness hypothesis on the constant field.

## Main definitions

* `TauCeti.holomorphyRing`: the holomorphy ring `𝒪_S` of a set of places, as a `k`-subalgebra
  of `F`.

## Main results

* `TauCeti.isIntegrallyClosedIn_holomorphyRing`: a holomorphy ring is integrally closed in `F`.
* `TauCeti.holomorphyRing_setOf_subset_integers`: **Stichtenoth, Theorem 3.2.6** — a
  `k`-subalgebra of `F` integrally closed in `F` is the holomorphy ring of the set of places at
  which its functions are regular.
* `TauCeti.coe_holomorphyRing_subset_integers_iff`: **Stichtenoth, Corollary 3.2.8** — the
  functions of `𝒪_S` are all regular at `P` exactly when `P ∈ S`, so `S` is recovered from
  `𝒪_S` and the two constructions are mutually inverse.
* `TauCeti.isFractionRing_holomorphyRing`: `F` is the field of fractions of `𝒪_S` as soon as
  some place lies outside `S`.

## Implementation notes

`𝒪_S` is a `Subalgebra k F` rather than a bare `Subring F`: the constants are regular at every
place (`TauCeti.Place.algebraMap_mem_integers`), so the `k`-algebra structure is free, and it is
what the affine-model API consumes.  Mathlib's `Set.integer`, the `S`-integers of the fraction
field of a Dedekind domain, is the same shape for the places of a fixed affine model and with the
complementary indexing convention (integrality is imposed *away* from `S`); it is not general
enough here, where the index is the whole place set of `F / k` and the place at infinity of a
model is a citizen like any other.

Theorem 3.2.6 does not repeat Stichtenoth's Zorn argument.  Mathlib's
`Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn` (Stacks 090P) already separates an
element from a subring integrally closed in a field by a valuation subring; what is specific to
function fields is that the valuation subring so produced is a *place*, and that is
`TauCeti.Place.ofValuationSubring`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.2 (Definition 3.2.2, Theorem 3.2.6, Corollary 3.2.8).
-/

public section

namespace TauCeti

open AlgebraicGeometry

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-! ### The holomorphy ring of a set of places -/

/-- The **holomorphy ring** `𝒪_S = ⋂_{P ∈ S} 𝒪_P` of a set `S` of places of `F / k`
(Stichtenoth, Definition 3.2.2): the functions regular at every place of `S`. -/
def holomorphyRing (S : Set (Place k F)) : Subalgebra k F where
  carrier := {z : F | ∀ P ∈ S, z ∈ P.integers}
  mul_mem' ha hb P hP := mul_mem (ha P hP) (hb P hP)
  one_mem' _ _ := one_mem _
  add_mem' ha hb P hP := add_mem (ha P hP) (hb P hP)
  zero_mem' _ _ := zero_mem _
  algebraMap_mem' c P _ := P.algebraMap_mem_integers c

@[simp]
theorem mem_holomorphyRing_iff {S : Set (Place k F)} {z : F} :
    z ∈ holomorphyRing S ↔ ∀ P ∈ S, z ∈ P.integers :=
  (Iff.rfl)

/-- Membership in `𝒪_S` in additive form: `z` has no pole on `S`. -/
theorem mem_holomorphyRing_iff_forall_ord_nonneg {S : Set (Place k F)} {z : F} :
    z ∈ holomorphyRing S ↔ ∀ P ∈ S, 0 ≤ P.ord z :=
  forall₂_congr fun P _ ↦ P.mem_integers_iff_ord_nonneg

/-- Every function of `𝒪_S` is regular at every place of `S`. -/
theorem coe_holomorphyRing_subset_integers {S : Set (Place k F)} {P : Place k F} (hP : P ∈ S) :
    (holomorphyRing S : Set F) ⊆ P.integers :=
  fun _ hz ↦ hz P hP

/-- Asking for regularity at more places gives a smaller ring. -/
theorem holomorphyRing_antitone :
    Antitone (holomorphyRing : Set (Place k F) → Subalgebra k F) :=
  fun _ _ hST _ hz P hP ↦ hz P (hST hP)

@[simp]
theorem holomorphyRing_empty : holomorphyRing (∅ : Set (Place k F)) = ⊤ := by
  ext z
  simp

/-- **The holomorphy ring of all the places is the constant field** (Stichtenoth,
Corollary 1.1.20): a function regular everywhere is algebraic over `k`. -/
@[simp]
theorem holomorphyRing_univ (hF : IsFunctionField k F) :
    holomorphyRing (Set.univ : Set (Place k F)) = (algebraicClosure k F).toSubalgebra := by
  ext z
  rw [mem_holomorphyRing_iff, IntermediateField.mem_toSubalgebra,
    Place.mem_algebraicClosure_iff_forall_mem_integers hF]
  simp

/-- **A holomorphy ring is integrally closed in `F`**: a function integral over `𝒪_S` is integral
over each `𝒪_P` with `P ∈ S`, and a valuation ring is integrally closed
(`TauCeti.Place.mem_integers_of_isIntegral`). -/
instance isIntegrallyClosedIn_holomorphyRing (S : Set (Place k F)) :
    IsIntegrallyClosedIn ↥(holomorphyRing S) F :=
  Subring.isIntegrallyClosedIn_iff.mpr fun {_} hz P hP ↦
    P.mem_integers_of_isIntegral (fun r ↦ r.2 P hP) hz

/-! ### The field of fractions -/

/-- **Denominators regular on `S`**: if some place `Q` lies outside `S`, every function of `F` is
`(y * z) / y` for a nonzero `y` with `y` and `y * z` both regular on `S`.  Riemann's theorem
supplies `y` inside `L(n·Q - (z)_∞)` for `n` large: such a `y` vanishes on the poles of `z` to at
least their order, and its own only pole is `Q`, which lies outside `S`. -/
theorem exists_ne_zero_mem_holomorphyRing_and_mul_mem (hF : IsFunctionField k F)
    {S : Set (Place k F)} {Q : Place k F} (hQ : Q ∉ S) (z : F) :
    ∃ y : F, y ≠ 0 ∧ y ∈ holomorphyRing S ∧ y * z ∈ holomorphyRing S := by
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨1, one_ne_zero, one_mem _, by rw [mul_zero]; exact zero_mem _⟩
  set A : Divisor k F := Divisor.poles hF (Units.mk0 z hz) with hA
  have hAcoeff : ∀ P : Place k F, A.coeff P = -P.ord z ⊔ 0 := fun P ↦ by
    rw [hA, Divisor.coeff_poles, Units.val_mk0]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Divisor.degree A + genus k F ≤ (n : ℤ) :=
    ⟨(Divisor.degree A + genus k F).toNat, Int.self_le_toNat _⟩
  set D : Divisor k F := Finsupp.single Q (n : ℤ) - A with hD
  have hQdeg : (1 : ℤ) ≤ Q.degree := by
    exact_mod_cast Q.one_le_degree_of_isFunctionField hF
  have hsingle : ∀ P : Place k F, P ≠ Q →
      WeilDivisor.coeff (Finsupp.single Q (n : ℤ) : Divisor k F) P = 0 :=
    fun _ hPQ ↦ Finsupp.single_eq_of_ne hPQ
  have hDcoeff : ∀ P : Place k F, P ≠ Q → D.coeff P = -A.coeff P := fun P hPQ ↦ by
    rw [hD, WeilDivisor.coeff_sub, hsingle P hPQ, zero_sub]
  have hdim : 1 ≤ Divisor.dim D := by
    have hR := Divisor.degree_add_one_sub_genus_le_dim hF D
    rw [hD, Divisor.degree_sub, Divisor.degree_single] at hR
    have hmul : (n : ℤ) ≤ n * Q.degree :=
      le_mul_of_one_le_right (Int.natCast_nonneg n) hQdeg
    have h1 : (1 : ℤ) ≤ (Divisor.dim D : ℤ) := by linarith
    exact_mod_cast h1
  obtain ⟨y, hyD, hy0⟩ := Submodule.ne_bot_iff _ |>.1
    ((Divisor.one_le_dim_iff_riemannRochSpace_ne_bot hF D).mp hdim)
  have hyord : ∀ P : Place k F, P ∈ S → A.coeff P ≤ P.ord y := fun P hP ↦ by
    have hPQ : P ≠ Q := fun hPQ ↦ hQ (hPQ ▸ hP)
    have h := (mem_riemannRochSpace_iff_neg_le_ord hy0).mp hyD P
    rwa [hDcoeff P hPQ, neg_neg] at h
  refine ⟨y, hy0, mem_holomorphyRing_iff_forall_ord_nonneg.mpr fun P hP ↦ ?_,
    mem_holomorphyRing_iff_forall_ord_nonneg.mpr fun P hP ↦ ?_⟩
  · have h1 := hyord P hP
    have h2 := hAcoeff P
    omega
  · rw [P.ord_mul hy0 hz]
    have h1 := hyord P hP
    have h2 := hAcoeff P
    omega

/-- **`F` is the field of fractions of `𝒪_S`** whenever some place lies outside `S`
(Stichtenoth, Section III.2). -/
theorem isFractionRing_holomorphyRing (hF : IsFunctionField k F) {S : Set (Place k F)}
    (hS : Sᶜ.Nonempty) : IsFractionRing ↥(holomorphyRing S) F where
  map_units y :=
    (Units.mk0 (y : F) fun h ↦ nonZeroDivisors.ne_zero y.2 (Subtype.ext h)).isUnit
  surj z := by
    obtain ⟨Q, hQ⟩ := hS
    obtain ⟨y, hy0, hyS, hyzS⟩ := exists_ne_zero_mem_holomorphyRing_and_mul_mem hF hQ z
    refine ⟨⟨⟨y * z, hyzS⟩, ⟨⟨y, hyS⟩, mem_nonZeroDivisors_of_ne_zero fun h ↦ hy0 ?_⟩⟩, ?_⟩
    · exact congrArg Subtype.val h
    · exact mul_comm z y
  exists_of_eq h := ⟨1, by simpa using Subtype.ext h⟩

/-! ### Integrally closed subrings are holomorphy rings -/

/-- **Stichtenoth, Theorem 3.2.6.**  A `k`-subalgebra of `F` that is integrally closed in `F` is
the holomorphy ring of the set of places at which all of its functions are regular.  No hypothesis
on the constant field is needed.

A function outside `R` is separated from `R` by a valuation subring of `F`
(`Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`), which contains the constants and
is proper, hence is the valuation ring of a place. -/
theorem holomorphyRing_setOf_subset_integers (hF : IsFunctionField k F) (R : Subalgebra k F)
    [IsIntegrallyClosedIn ↥R F] :
    holomorphyRing {P : Place k F | (R : Set F) ⊆ P.integers} = R := by
  refine le_antisymm (fun z hz ↦ ?_) fun z hz P hP ↦ hP hz
  by_contra hzR
  have : IsIntegrallyClosedIn ↥R.toSubring F := inferInstanceAs (IsIntegrallyClosedIn ↥R F)
  obtain ⟨V, hRV, hzV⟩ :=
    Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn (R := R.toSubring) hzR
  have hk : ∀ c : k, algebraMap k F c ∈ V := fun c ↦ hRV (R.algebraMap_mem c)
  have hV : V ≠ ⊤ := fun h ↦ hzV (h ▸ ValuationSubring.mem_top _)
  have hmem : (R : Set F) ⊆ (Place.ofValuationSubring hF hk hV).integers := by
    rw [Place.integers_ofValuationSubring]
    exact fun x hx ↦ hRV hx
  exact hzV (Place.integers_ofValuationSubring hF hk hV ▸ hz _ hmem)

/-! ### Recovering the set of places -/

/-- **Stichtenoth, Corollary 3.2.8.**  The functions of `𝒪_S` are all regular at a place `P`
exactly when `P` belongs to `S`, so `S` is recovered from its holomorphy ring: together with
`TauCeti.holomorphyRing_setOf_subset_integers` this makes sets of places and `k`-subalgebras of
`F` integrally closed in `F` correspond antitonely. -/
@[simp]
theorem coe_holomorphyRing_subset_integers_iff (hF : IsFunctionField k F)
    {S : Set (Place k F)} {P : Place k F} :
    (holomorphyRing S : Set F) ⊆ P.integers ↔ P ∈ S := by
  refine ⟨fun h ↦ by_contra fun hP ↦ ?_, coe_holomorphyRing_subset_integers⟩
  obtain ⟨z, hz1, hz2⟩ := Place.exists_ord_neg_and_forall_ne_ord_nonneg hF P
  have hzS : z ∈ holomorphyRing S :=
    mem_holomorphyRing_iff_forall_ord_nonneg.mpr fun Q hQ ↦ hz2 Q fun h ↦ hP (h ▸ hQ)
  have hzP := h hzS
  rw [SetLike.mem_coe, P.mem_integers_iff_ord_nonneg] at hzP
  omega

end TauCeti
