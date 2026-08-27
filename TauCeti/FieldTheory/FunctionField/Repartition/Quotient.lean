/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Repartition.Basic
public import TauCeti.LinearAlgebra.Dimension.Tower

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
elsewhere is a repartition bounded by `E`.  A general pair `D ≤ E` is reached from that case by
walking up the finitely many places in the support of `E - D`, rank being additive along a tower
of submodules (`TauCeti.rank_quotient_submoduleOf_tower`).

## Main definitions

* `TauCeti.localFiltrationQuotient`: the local quotient `𝔪_P^(-E P) / 𝔪_P^(-D P)` at a place `P`.
* `TauCeti.adeleFiltrationEval`: evaluation of a repartition of `A_F(E)` at a place, landing in
  the step `𝔪_P^(-E P)` of the order filtration there.
* `TauCeti.adeleFiltrationLocalMap`: that evaluation, read modulo `𝔪_P^(-D P)`.
* `TauCeti.adeleFiltrationQuotientEquiv`: the isomorphism
  `A_F(E) / A_F(D) ≃ₗ[k] 𝔪_P^(-E P) / 𝔪_P^(-D P)` for `D` and `E` agreeing away from `P`.

## Main results

* `TauCeti.ker_adeleFiltrationLocalMap` and `TauCeti.adeleFiltrationLocalMap_surjective`: the
  local map has kernel `A_F(D)` — when the two divisors agree away from `P` — and is always
  surjective.
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
      adeleFiltrationLocalMap D E P a :=
  (rfl)

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

Together with the diagonal-intersection lemma `F ∩ A_F(D) = L(D)`
(`TauCeti.diagonalRepartitions_inf_adeleFiltration`) this is what computes the index of
specialty. -/
theorem finrank_quotient_adeleFiltration {D E : Divisor k F} (h : D ≤ E) :
    (Module.finrank k
        (↥(adeleFiltration E) ⧸ (adeleFiltration D).submoduleOf (adeleFiltration E)) : ℤ) =
      Divisor.degree E - Divisor.degree D := by
  have hdeg : Divisor.degree D ≤ Divisor.degree E := Divisor.degree_le_of_le h
  rw [Module.finrank, rank_quotient_adeleFiltration hF h, Cardinal.toNat_natCast]
  omega

end Rank

end TauCeti
