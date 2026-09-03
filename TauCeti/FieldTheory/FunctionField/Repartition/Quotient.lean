/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Repartition.Basic

/-!
# The quotients of the divisor filtration of the repartition space

For two divisors `D ≤ E` of an algebraic function field `F / k`, the two steps `A_F(D)` and
`A_F(E)` of the divisor filtration of the repartition space have a finite-dimensional quotient,
of dimension

`dim_k (A_F(E) / A_F(D)) = deg E - deg D`

(`TauCeti.finrank_quotient_adeleFiltration`).  This is the global half of the local-to-global
engine of Stichtenoth's Section I.5, whose local half — the dimension `(b - a) · deg P` of a
quotient `𝔪_P^a / 𝔪_P^b` of two steps of the order filtration at a single place — is
`TauCeti.Place.finrank_quotient_filtration`.  It is the linear-algebra input of Stichtenoth's
Theorem 1.5.4, which identifies the index of specialty `i(D)` with `dim_k (A_F / (A_F(D) + F))`,
and through it of the one-dimensionality of the space of Weil differentials and of the
Riemann–Roch theorem.

The two halves are joined one place at a time.  When `E - D` is supported at a single place `P`,
reading a repartition off at `P` is an isomorphism

`A_F(E) / A_F(D) ≃ₗ[k] 𝔪_P^(-E P) / 𝔪_P^(-D P)`

(`TauCeti.adeleFiltrationQuotientEquiv`): its kernel is `A_F(D)` because away from `P` the two
bounds agree, and it is surjective because a function prescribed at `P` and extended by zero
elsewhere is a repartition bounded by `E`.  Running the same two arguments over a whole finite
set `s` of places, one containing `supp (E - D)`, identifies

`A_F(E) / A_F(D) ≃ₗ[k] ⨁_{P ∈ s} 𝔪_P^(-E P) / 𝔪_P^(-D P)`

(`TauCeti.adeleFiltrationQuotientEquivPi`); at `s = supp (E - D)` this is the local-to-global
identification of Section I.5.  The dimension count for a general pair `D ≤ E` is instead reached
from the one-place case by walking up the finitely many places in the support of `E - D`, rank
being additive along a tower of submodules (`TauCeti.rank_quotient_submoduleOf_tower`), which
avoids having to sum the local dimensions.

## Main definitions

* `TauCeti.localFiltrationQuotient`: the local quotient `𝔪_P^(-E P) / 𝔪_P^(-D P)` at a place `P`.
* `TauCeti.adeleFiltrationEval`: evaluation of a repartition of `A_F(E)` at a place, landing in
  the step `𝔪_P^(-E P)` of the order filtration there.
* `TauCeti.adeleFiltrationLocalMap`: that evaluation, read modulo `𝔪_P^(-D P)`.
* `TauCeti.adeleFiltrationQuotientEquiv`: the isomorphism
  `A_F(E) / A_F(D) ≃ₗ[k] 𝔪_P^(-E P) / 𝔪_P^(-D P)` for `D` and `E` agreeing away from `P`.
* `TauCeti.adeleFiltrationLocalMapPi`: the reduction read at every place of a finite set `s` at
  once, and `TauCeti.adeleFiltrationQuotientLocalMapPi`: the same map descended to
  `A_F(E) / A_F(D)`.
* `TauCeti.adeleFiltrationQuotientEquivPi`: the isomorphism of `A_F(E) / A_F(D)` with the finite
  direct sum of the local quotients over `s`, for any `s` containing `supp (E - D)`.

## Main results

* `TauCeti.ker_adeleFiltrationLocalMap` and `TauCeti.adeleFiltrationLocalMap_surjective`: the
  local map has kernel `A_F(D)` — when the two divisors agree away from `P` — and is always
  surjective.
* `TauCeti.ker_adeleFiltrationLocalMapPi` and `TauCeti.adeleFiltrationLocalMapPi_surjective`: the
  same two facts for the reduction over `s` — the kernel as soon as `s` contains
  `supp (E - D)`, the surjectivity for any `s`.
* `TauCeti.rank_quotient_adeleFiltration`: the rank form of the dimension formula, whose
  natural-number right-hand side carries the finiteness with it.
* `TauCeti.finiteDimensional_quotient_adeleFiltration`: the quotient is finite-dimensional.
* `TauCeti.finrank_quotient_adeleFiltration`: `dim_k (A_F(E) / A_F(D)) = deg E - deg D`.

## Implementation notes

Relative quotients are spelled with `Submodule.submoduleOf`, as in
`TauCeti.Place.finrank_quotient_filtration` and `TauCeti.rank_quotient_submoduleOf_tower`:
`A_F(D).submoduleOf (A_F(E))` is the trace of `A_F(D)` on `A_F(E)`, which needs no inclusion
`A_F(D) ≤ A_F(E)` to make sense.  That is why the isomorphism above asks only that the two
divisors agree away from `P`, and not that `D ≤ E`; the dimension count does need `D ≤ E`, since
`(b - a) · deg P` is not the dimension of the trivial quotient obtained when `b < a`.

Mathlib has no `mem_submoduleOf` lemma.  Since `Submodule.submoduleOf` is by definition a comap
along the inclusion, membership in it *is* `Submodule.mem_comap`, which the proofs below cite in
a `show`.

`TauCeti.adeleFiltrationQuotientEquivPi` descends to the quotient one factor at a time, as a
`LinearMap.pi` of `Submodule.liftQ`s, and is then turned into an equivalence by
`LinearEquiv.ofBijective`.  The direct route — `Submodule.liftQ` or
`LinearMap.quotKerEquivOfSurjective` applied to `TauCeti.adeleFiltrationLocalMapPi` itself —
elaborates a `LinearMap` whose codomain is a product of quotients, and the unifier does not
finish that within the heartbeat limit; descending factorwise keeps every quotient it meets a
single one.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.5.
-/

public section

open scoped WithZero

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The local quotient at a place `P` attached to two divisors `D` and `E`: the quotient
`𝔪_P^(-E P) / 𝔪_P^(-D P)` of two steps of the order filtration of `F` at `P`.  Its dimension over
`k` is `(E P - D P) · deg P` when `D P ≤ E P` (`TauCeti.Place.finrank_quotient_filtration`). -/
noncomputable abbrev localFiltrationQuotient (D E : Divisor k F) (P : Place k F) : Type _ :=
  ↥(P.filtration (-E.coeff P)) ⧸
    (P.filtration (-D.coeff P)).submoduleOf (P.filtration (-E.coeff P))

/-- Evaluation at a place `P` of the repartitions bounded by `E`: a repartition of `A_F(E)` has
pole order at most `E P` at `P`, so its `P`-th entry lies in the step `𝔪_P^(-E P)` of the order
filtration of `F` at `P`. -/
noncomputable def adeleFiltrationEval (E : Divisor k F) (P : Place k F) :
    adeleFiltration E →ₗ[k] P.filtration (-E.coeff P) :=
  LinearMap.codRestrict _ ((LinearMap.proj P).comp (adeleFiltration E).subtype) fun a ↦ by
    rw [Place.mem_filtration_iff, neg_neg]
    exact mem_adeleFiltration_iff.mp a.2 P

@[simp]
theorem coe_adeleFiltrationEval (E : Divisor k F) (P : Place k F) (a : adeleFiltration E) :
    (adeleFiltrationEval E P a : F) = (a : Place k F → F) P :=
  (rfl)

/-- Reading a repartition of `A_F(E)` at the place `P` modulo `𝔪_P^(-D P)`, that is, modulo the
bound that `A_F(D)` imposes there.  When `D` and `E` agree away from `P` this map is exactly the
projection of `A_F(E)` onto `A_F(E) / A_F(D)`, which is `TauCeti.adeleFiltrationQuotientEquiv`. -/
noncomputable def adeleFiltrationLocalMap (D E : Divisor k F) (P : Place k F) :
    adeleFiltration E →ₗ[k] localFiltrationQuotient D E P :=
  ((P.filtration (-D.coeff P)).submoduleOf (P.filtration (-E.coeff P))).mkQ.comp
    (adeleFiltrationEval E P)

@[simp]
theorem adeleFiltrationLocalMap_apply (D E : Divisor k F) (P : Place k F)
    (a : adeleFiltration E) :
    adeleFiltrationLocalMap D E P a = Submodule.Quotient.mk (adeleFiltrationEval E P a) :=
  (rfl)

/-- The local reduction at `P` vanishes exactly when the bound that `D` imposes at `P` holds. -/
theorem adeleFiltrationLocalMap_eq_zero_iff (D E : Divisor k F) (P : Place k F)
    (a : adeleFiltration E) :
    adeleFiltrationLocalMap D E P a = 0 ↔
      P.valuation ((a : Place k F → F) P) ≤ WithZero.exp (D.coeff P) := by
  rw [adeleFiltrationLocalMap_apply, Submodule.Quotient.mk_eq_zero,
    show (adeleFiltrationEval E P a ∈
        (P.filtration (-D.coeff P)).submoduleOf (P.filtration (-E.coeff P))) ↔
      ((a : Place k F → F) P ∈ P.filtration (-D.coeff P)) from Submodule.mem_comap,
    Place.mem_filtration_iff, neg_neg]

/-- **The kernel of the local reduction at `P`** is the trace of `A_F(D)` on `A_F(E)`, as soon as
the two divisors agree away from `P`: at every other place the bound imposed by `D` is the bound
imposed by `E`, which every element of `A_F(E)` satisfies already. -/
theorem ker_adeleFiltrationLocalMap {D E : Divisor k F} {P : Place k F}
    (hoff : ∀ Q, Q ≠ P → D.coeff Q = E.coeff Q) :
    LinearMap.ker (adeleFiltrationLocalMap D E P) =
      (adeleFiltration D).submoduleOf (adeleFiltration E) := by
  ext a
  rw [LinearMap.mem_ker, adeleFiltrationLocalMap_eq_zero_iff,
    show (a ∈ (adeleFiltration D).submoduleOf (adeleFiltration E)) ↔
      ((a : Place k F → F) ∈ adeleFiltration D) from Submodule.mem_comap,
    mem_adeleFiltration_iff]
  refine ⟨fun h Q ↦ ?_, fun h ↦ h P⟩
  rcases eq_or_ne Q P with rfl | hQ
  · exact h
  · rw [hoff Q hQ]
    exact mem_adeleFiltration_iff.mp a.2 Q

/-- **The local reduction at `P` is surjective**: a function with pole order at most `E P` at `P`,
extended by zero at every other place, is a repartition bounded by `E`. -/
theorem adeleFiltrationLocalMap_surjective (D E : Divisor k F) (P : Place k F) :
    Function.Surjective (adeleFiltrationLocalMap D E P) := by
  classical
  intro y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine ⟨⟨fun Q ↦ if Q = P then (z : F) else 0,
    mem_adeleFiltration_iff.mpr fun Q ↦ ?_⟩, ?_⟩
  · rcases eq_or_ne Q P with rfl | hQ
    · rw [ite_eq_left (rfl : Q = Q)]
      simpa only [Place.mem_filtration_iff, neg_neg] using z.2
    · simp [ite_eq_right hQ]
  · rw [adeleFiltrationLocalMap_apply]
    exact congrArg _ (Subtype.ext (ite_eq_left rfl))

/-- **The local-to-global step**: for two divisors agreeing away from a place `P`, reading a
repartition off at `P` identifies `A_F(E) / A_F(D)` with the local quotient
`𝔪_P^(-E P) / 𝔪_P^(-D P)`.  This is the one-place case of Stichtenoth's computation of the
quotients of the divisor filtration in Section I.5. -/
noncomputable def adeleFiltrationQuotientEquiv {D E : Divisor k F} {P : Place k F}
    (hoff : ∀ Q, Q ≠ P → D.coeff Q = E.coeff Q) :
    (↥(adeleFiltration E) ⧸ (adeleFiltration D).submoduleOf (adeleFiltration E)) ≃ₗ[k]
      localFiltrationQuotient D E P :=
  (Submodule.quotEquivOfEq _ _ (ker_adeleFiltrationLocalMap hoff).symm).trans
    ((adeleFiltrationLocalMap D E P).quotKerEquivOfSurjective
      (adeleFiltrationLocalMap_surjective D E P))

@[simp]
theorem adeleFiltrationQuotientEquiv_mk {D E : Divisor k F} {P : Place k F}
    (hoff : ∀ Q, Q ≠ P → D.coeff Q = E.coeff Q) (a : adeleFiltration E) :
    adeleFiltrationQuotientEquiv hoff (Submodule.Quotient.mk a) =
      adeleFiltrationLocalMap D E P a := by
  simp only [adeleFiltrationQuotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- Reading a repartition of `A_F(E)` at each place of a finite set `s` of places, each entry
taken modulo the bound that `A_F(D)` imposes there.  The index set being finite, the target is
the direct sum of the local quotients over `s`. -/
noncomputable def adeleFiltrationLocalMapPi (D E : Divisor k F) (s : Finset (Place k F)) :
    adeleFiltration E →ₗ[k] ∀ P : ↥s, localFiltrationQuotient D E ↑P :=
  LinearMap.pi fun P ↦ adeleFiltrationLocalMap D E ↑P

@[simp]
theorem adeleFiltrationLocalMapPi_apply (D E : Divisor k F) (s : Finset (Place k F))
    (a : adeleFiltration E) (P : ↥s) :
    adeleFiltrationLocalMapPi D E s a P = adeleFiltrationLocalMap D E ↑P a :=
  LinearMap.pi_apply _ _ _

/-- **The kernel of the place-by-place reduction over `s`** is the trace of `A_F(D)` on `A_F(E)`,
as soon as `s` contains the support of `E - D`: at every place outside that support the bound
imposed by `D` is the bound imposed by `E`, which every element of `A_F(E)` satisfies already. -/
theorem ker_adeleFiltrationLocalMapPi {D E : Divisor k F} {s : Finset (Place k F)}
    (hs : (E - D).support ⊆ s) :
    LinearMap.ker (adeleFiltrationLocalMapPi D E s) =
      (adeleFiltration D).submoduleOf (adeleFiltration E) := by
  ext a
  rw [LinearMap.mem_ker, funext_iff,
    show (a ∈ (adeleFiltration D).submoduleOf (adeleFiltration E)) ↔
      ((a : Place k F → F) ∈ adeleFiltration D) from Submodule.mem_comap,
    mem_adeleFiltration_iff]
  simp only [adeleFiltrationLocalMapPi_apply, Pi.zero_apply, adeleFiltrationLocalMap_eq_zero_iff,
    Subtype.forall]
  refine ⟨fun h Q ↦ ?_, fun h Q _ ↦ h Q⟩
  by_cases hQ : Q ∈ s
  · exact h Q hQ
  · have hQD : D.coeff Q = E.coeff Q := by
      have h0 : (E - D).coeff Q = 0 := by
        by_contra h0
        exact hQ (hs (WeilDivisor.mem_support_iff.mpr h0))
      rw [WeilDivisor.coeff_sub] at h0
      omega
    rw [hQD]
    exact mem_adeleFiltration_iff.mp a.2 Q

/-- **The place-by-place reduction over `s` is surjective**: entries prescribed at the finitely
many places of `s`, extended by zero elsewhere, form a repartition bounded by `E`. -/
theorem adeleFiltrationLocalMapPi_surjective (D E : Divisor k F) (s : Finset (Place k F)) :
    Function.Surjective (adeleFiltrationLocalMapPi D E s) := by
  classical
  intro y
  choose z hz using fun P : ↥s ↦ Submodule.Quotient.mk_surjective _ (y P)
  refine ⟨⟨fun Q ↦ if h : Q ∈ s then (z ⟨Q, h⟩ : F) else 0,
    mem_adeleFiltration_iff.mpr fun Q ↦ ?_⟩, funext fun P ↦ ?_⟩
  · rcases em (Q ∈ s) with h | h
    · rw [dite_eq_left h]
      simpa only [Place.mem_filtration_iff, neg_neg] using (z ⟨Q, h⟩).2
    · simp [dite_eq_right h]
  · rw [adeleFiltrationLocalMapPi_apply, adeleFiltrationLocalMap_apply, ← hz P]
    refine congrArg _ (Subtype.ext ?_)
    rw [coe_adeleFiltrationEval]
    exact dite_eq_left P.2

/-- The place-by-place reduction over `s`, descended to the quotient `A_F(E) / A_F(D)`: it is
well defined because a repartition bounded by `D` satisfies the bound `D` imposes at every place,
so reduces to zero there. -/
noncomputable def adeleFiltrationQuotientLocalMapPi (D E : Divisor k F)
    (s : Finset (Place k F)) :
    (↥(adeleFiltration E) ⧸ (adeleFiltration D).submoduleOf (adeleFiltration E)) →ₗ[k]
      ∀ P : ↥s, localFiltrationQuotient D E ↑P :=
  LinearMap.pi fun P ↦
    Submodule.liftQ ((adeleFiltration D).submoduleOf (adeleFiltration E))
      (adeleFiltrationLocalMap D E ↑P) fun a ha ↦ by
        rw [LinearMap.mem_ker, adeleFiltrationLocalMap_eq_zero_iff]
        exact mem_adeleFiltration_iff.mp (Submodule.mem_comap.mp ha) ↑P

@[simp]
theorem adeleFiltrationQuotientLocalMapPi_mk (D E : Divisor k F) (s : Finset (Place k F))
    (a : adeleFiltration E) (P : ↥s) :
    adeleFiltrationQuotientLocalMapPi D E s (Submodule.Quotient.mk a) P =
      adeleFiltrationLocalMap D E ↑P a := by
  simp only [adeleFiltrationQuotientLocalMapPi, LinearMap.pi_apply, Submodule.liftQ_apply]

/-- The descended place-by-place reduction is bijective as soon as `s` contains the support of
`E - D`: injective by `TauCeti.ker_adeleFiltrationLocalMapPi`, surjective by
`TauCeti.adeleFiltrationLocalMapPi_surjective`. -/
theorem adeleFiltrationQuotientLocalMapPi_bijective {D E : Divisor k F} {s : Finset (Place k F)}
    (hs : (E - D).support ⊆ s) :
    Function.Bijective (adeleFiltrationQuotientLocalMapPi D E s) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Submodule.Quotient.eq, ← ker_adeleFiltrationLocalMapPi hs, LinearMap.mem_ker]
    refine funext fun P ↦ ?_
    rw [map_sub, Pi.sub_apply, Pi.zero_apply, sub_eq_zero, adeleFiltrationLocalMapPi_apply,
      adeleFiltrationLocalMapPi_apply, ← adeleFiltrationQuotientLocalMapPi_mk D E s a P,
      ← adeleFiltrationQuotientLocalMapPi_mk D E s b P, hxy]
  · intro y
    obtain ⟨a, ha⟩ := adeleFiltrationLocalMapPi_surjective D E s y
    exact ⟨Submodule.Quotient.mk a, funext fun P ↦ by
      rw [adeleFiltrationQuotientLocalMapPi_mk, ← adeleFiltrationLocalMapPi_apply, ha]⟩

/-- **The local-to-global identification** (Stichtenoth, Section I.5): whenever a finite set `s`
of places contains the support of `E - D`, reading a repartition of `A_F(E)` off at each place of
`s` identifies

`A_F(E) / A_F(D) ≃ₗ[k] ⨁_{P ∈ s} 𝔪_P^(-E P) / 𝔪_P^(-D P)`,

the index set `s` being finite, so that the product below *is* that direct sum.  The smallest
choice, and the one the local-to-global engine is usually stated with, is `s = supp (E - D)`; its
`P`-th component is `TauCeti.adeleFiltrationLocalMap`
(`TauCeti.adeleFiltrationQuotientEquivPi_mk`). -/
noncomputable def adeleFiltrationQuotientEquivPi {D E : Divisor k F} {s : Finset (Place k F)}
    (hs : (E - D).support ⊆ s) :
    (↥(adeleFiltration E) ⧸ (adeleFiltration D).submoduleOf (adeleFiltration E)) ≃ₗ[k]
      ∀ P : ↥s, localFiltrationQuotient D E ↑P :=
  LinearEquiv.ofBijective (adeleFiltrationQuotientLocalMapPi D E s)
    (adeleFiltrationQuotientLocalMapPi_bijective hs)

@[simp]
theorem adeleFiltrationQuotientEquivPi_mk {D E : Divisor k F} {s : Finset (Place k F)}
    (hs : (E - D).support ⊆ s) (a : adeleFiltration E) (P : ↥s) :
    adeleFiltrationQuotientEquivPi hs (Submodule.Quotient.mk a) P =
      adeleFiltrationLocalMap D E ↑P a := by
  rw [adeleFiltrationQuotientEquivPi, LinearEquiv.ofBijective_apply,
    adeleFiltrationQuotientLocalMapPi_mk]

section Rank

variable (hF : IsFunctionField k F)
include hF

/-- The one-place case of the dimension formula, at the level of `Module.rank`: two divisors
`D ≤ E` agreeing away from `P` have `rank_k (A_F(E) / A_F(D)) = deg E - deg D`, the difference of
the degrees being `(E P - D P) · deg P`. -/
private lemma rank_quotient_adeleFiltration_of_eq_off {D E : Divisor k F} {P : Place k F}
    (hDE : D ≤ E) (hoff : ∀ Q, Q ≠ P → D.coeff Q = E.coeff Q) :
    Module.rank k
        (↥(adeleFiltration E) ⧸ (adeleFiltration D).submoduleOf (adeleFiltration E)) =
      ((Divisor.degree E - Divisor.degree D).toNat : Cardinal) := by
  have hres : FiniteDimensional k P.ResidueField := Place.finiteDimensional_residueField P hF
  have hfd : FiniteDimensional k (localFiltrationQuotient D E P) :=
    Place.finiteDimensional_quotient_filtration P _ _
  have hPE : D.coeff P ≤ E.coeff P := WeilDivisor.coeff_le_coeff hDE P
  have hsingle : E - D = Finsupp.single P (E.coeff P - D.coeff P) := by
    refine Finsupp.ext fun Q ↦ ?_
    rcases eq_or_ne Q P with rfl | hQ
    · simp [WeilDivisor.coeff]
    · have h0 : D Q = E Q := hoff Q hQ
      simp [Ne.symm hQ, h0]
  have hdeg : Divisor.degree E - Divisor.degree D = (E.coeff P - D.coeff P) * P.degree := by
    rw [← Divisor.degree_sub, hsingle, Divisor.degree_single]
  have hfr : (Module.finrank k (localFiltrationQuotient D E P) : ℤ) =
      Divisor.degree E - Divisor.degree D := by
    rw [hdeg, Place.finrank_quotient_filtration P (by omega : -E.coeff P ≤ -D.coeff P)]
    ring
  rw [(adeleFiltrationQuotientEquiv hoff).rank_eq, ← Module.finrank_eq_rank]
  congr 1
  omega

private lemma rank_quotient_adeleFiltration_aux :
    ∀ (n : ℕ) (D E : Divisor k F), D ≤ E → (E - D).support.card ≤ n →
      Module.rank k
          (↥(adeleFiltration E) ⧸ (adeleFiltration D).submoduleOf (adeleFiltration E)) =
        ((Divisor.degree E - Divisor.degree D).toNat : Cardinal) := by
  classical
  intro n
  induction n with
  | zero =>
    intro D E _ hcard
    obtain rfl : E = D :=
      sub_eq_zero.mp (Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)))
    simp [Submodule.submoduleOf_self]
  | succ n ih =>
    intro D E hDE hcard
    rcases eq_or_ne (E - D) 0 with hED | hED
    · obtain rfl : E = D := sub_eq_zero.mp hED
      simp [Submodule.submoduleOf_self]
    obtain ⟨P, hP⟩ : (E - D).support.Nonempty := Finsupp.support_nonempty_iff.mpr hED
    -- `D'` raises `D` to `E` at the single place `P`, and leaves it alone elsewhere
    set D' : Divisor k F := D + Finsupp.single P (E.coeff P - D.coeff P) with hD'def
    have hoff : ∀ Q, Q ≠ P → D.coeff Q = D'.coeff Q := fun Q hQ ↦ by
      simp [hD'def, WeilDivisor.coeff, hQ]
    have hD'P : D'.coeff P = E.coeff P := by
      simp [hD'def, WeilDivisor.coeff]
    have hDD' : D ≤ D' := WeilDivisor.le_iff.mpr fun Q ↦ by
      rcases eq_or_ne Q P with rfl | hQ
      · rw [hD'P]
        exact WeilDivisor.coeff_le_coeff hDE Q
      · exact (hoff Q hQ).le
    have hD'E : D' ≤ E := WeilDivisor.le_iff.mpr fun Q ↦ by
      rcases eq_or_ne Q P with rfl | hQ
      · exact hD'P.le
      · rw [← hoff Q hQ]
        exact WeilDivisor.coeff_le_coeff hDE Q
    have hcard' : (E - D').support.card ≤ n := by
      have hsub : (E - D').support ⊆ (E - D).support.erase P := fun Q hQ ↦ by
        rw [WeilDivisor.mem_support_iff, WeilDivisor.coeff_sub] at hQ
        rcases eq_or_ne Q P with rfl | hQP
        · exact absurd (by rw [hD'P, sub_self]) hQ
        · refine Finset.mem_erase.mpr ⟨hQP, WeilDivisor.mem_support_iff.mpr ?_⟩
          rw [WeilDivisor.coeff_sub, hoff Q hQP]
          exact hQ
      have hle := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hP] at hle
      have hpos : 1 ≤ (E - D).support.card := Finset.card_pos.mpr ⟨P, hP⟩
      omega
    have hdegDD' : Divisor.degree D ≤ Divisor.degree D' := Divisor.degree_le_of_le hDD'
    have hdegD'E : Divisor.degree D' ≤ Divisor.degree E := Divisor.degree_le_of_le hD'E
    -- rank is additive along `A_F(D) ≤ A_F(D') ≤ A_F(E)`: the first step is the one-place case,
    -- the second has a strictly smaller support and is handled by the induction hypothesis
    rw [rank_quotient_submoduleOf_tower (adeleFiltration_mono hDD') (adeleFiltration_mono hD'E),
      rank_quotient_adeleFiltration_of_eq_off hF hDD' hoff, ih D' E hD'E hcard', ← Nat.cast_add]
    congr 1
    omega

/-- **The rank of a quotient of the divisor filtration of the repartition space**
(Stichtenoth, Section I.5): for `D ≤ E`, the quotient `A_F(E) / A_F(D)` has rank `deg E - deg D`
over `k`.  The right-hand side is a natural number, so the statement carries the
finite-dimensionality of the quotient with it
(`TauCeti.finiteDimensional_quotient_adeleFiltration`). -/
theorem rank_quotient_adeleFiltration {D E : Divisor k F} (h : D ≤ E) :
    Module.rank k
        (↥(adeleFiltration E) ⧸ (adeleFiltration D).submoduleOf (adeleFiltration E)) =
      ((Divisor.degree E - Divisor.degree D).toNat : Cardinal) :=
  rank_quotient_adeleFiltration_aux hF (E - D).support.card D E h le_rfl

/-- The quotient of two steps of the divisor filtration of the repartition space is
finite-dimensional. -/
theorem finiteDimensional_quotient_adeleFiltration {D E : Divisor k F} (h : D ≤ E) :
    FiniteDimensional k
      (↥(adeleFiltration E) ⧸ (adeleFiltration D).submoduleOf (adeleFiltration E)) := by
  refine Module.rank_lt_aleph0_iff.mp ?_
  rw [rank_quotient_adeleFiltration hF h]
  exact Cardinal.natCast_lt_aleph0

/-- **The dimension of a quotient of the divisor filtration of the repartition space**
(Stichtenoth, Section I.5): for `D ≤ E`,

`dim_k (A_F(E) / A_F(D)) = deg E - deg D`.

This is one of the two linear-algebra inputs to the later computation of the index of specialty,
the other being the diagonal-intersection lemma `F ∩ A_F(D) = L(D)`
(`TauCeti.diagonalRepartitions_inf_adeleFiltration`).  Turning the two into
`i(D) = dim_k (A_F / (A_F(D) + F))` still needs the exact sequence relating `L(E)/L(D)`,
`A_F(E)/A_F(D)` and the cokernels of `A_F(D) + F → A_F`, which is not established here. -/
theorem finrank_quotient_adeleFiltration {D E : Divisor k F} (h : D ≤ E) :
    (Module.finrank k
        (↥(adeleFiltration E) ⧸ (adeleFiltration D).submoduleOf (adeleFiltration E)) : ℤ) =
      Divisor.degree E - Divisor.degree D := by
  have hdeg : Divisor.degree D ≤ Divisor.degree E := Divisor.degree_le_of_le h
  rw [Module.finrank, rank_quotient_adeleFiltration hF h, Cardinal.toNat_natCast]
  omega

end Rank

end TauCeti
