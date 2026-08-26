/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Isomorphisms
public import TauCeti.FieldTheory.FunctionField.Place.Basic

/-!
# The order filtration of a function field at a place

A place `P` of `F / k` filters `F` by the order of vanishing at `P`: for an integer `a` the
functions with `ord_P z ≥ a` form a `k`-subspace

`𝔪_P^a = {z ∈ F | v_P z ≤ exp (-a)}`

of `F`, decreasing in `a`, equal to the valuation ring `𝒪_P` at `a = 0` and to the maximal ideal
`𝔪_P` at `a = 1`.  For negative `a` it is the fractional ideal of functions with a pole of order
at most `-a`, so the whole filtration lives inside `F` and no completion is taken.

This file constructs that filtration and computes its successive quotients.  Multiplication by a
function of order `-a` identifies `𝔪_P^a / 𝔪_P^(a + 1)` with the residue field `F_P`
(`TauCeti.Place.filtrationQuotientEquivResidueField`), and iterating this along the tower gives
the dimension formula

`dim_k (𝔪_P^a / 𝔪_P^b) = (b - a) · deg P`  for  `a ≤ b`

(`TauCeti.Place.finrank_quotient_filtration`).  This is the local half of the local-to-global
engine of Stichtenoth's Section I.5: the global half identifies the quotient `A_F(E) / A_F(D)`
of two members of the divisor filtration of the repartition space with a finite direct sum of
these local quotients, and so computes `dim_k (A_F(E) / A_F(D)) = deg E - deg D`.

## Main definitions

* `TauCeti.Place.filtration`: the subspace `𝔪_P^a ⊆ F`.
* `TauCeti.Place.filtrationResidue`: for `s` of order `-a`, the `k`-linear evaluation
  `𝔪_P^a → F_P`, `z ↦ (s · z)(P)`.
* `TauCeti.Place.filtrationQuotientEquivResidueField`: the induced isomorphism
  `𝔪_P^a / 𝔪_P^(a + 1) ≃ₗ[k] F_P`.

## Main results

* `TauCeti.Place.rank_quotient_filtration_succ`: one step of the filtration has the rank of the
  residue field.
* `TauCeti.Place.finrank_quotient_filtration_add` and
  `TauCeti.Place.finrank_quotient_filtration`: `dim_k (𝔪_P^a / 𝔪_P^b) = (b - a) · deg P`, in the
  form indexed by `b = a + n` with `n : ℕ` and in the integer form.
* `TauCeti.Place.finiteDimensional_quotient_filtration`: those quotients are finite-dimensional
  as soon as the residue field is, which for a function field is
  `TauCeti.Place.finiteDimensional_residueField`.

## Implementation notes

Membership is stated multiplicatively, as `v_P z ≤ exp (-a)`, and never in the additive form
`ord_P z ≥ a`, which the junk value `ord_P 0 = 0` would get wrong at `a ≤ 0`: the additive
carrier would not contain `0` at negative `a` and so would not be a subspace.  This is the
convention of `TauCeti.riemannRochSpace` and `TauCeti.adeleFiltration`, of which this filtration
is the one-place shadow; `TauCeti.Place.mem_filtration_iff_le_ord` is the additive form, guarded
by `z ≠ 0`.

The relative quotients are spelled `↥(P.filtration a) ⧸ (P.filtration b).submoduleOf
(P.filtration a)`, using Mathlib's `Submodule.submoduleOf` for the trace of the smaller subspace
on the larger one.  The dimension formula is proved first as a statement about
`Module.rank`, where it needs no finiteness hypothesis at all, and then transported to
`Module.finrank` through `Cardinal.toNat_mul`; it therefore holds unconditionally, both sides
being zero when the residue field is infinite-dimensional over `k`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.1 and I.5.
-/

public section

open scoped WithZero

namespace TauCeti

namespace Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-! ### The filtration -/

/-- The subspace `𝔪_P^a = {z ∈ F | ord_P z ≥ a}` of functions vanishing to order at least `a`
at `P`, for `a` an arbitrary integer: for `a ≤ 0` it is the space of functions with a pole of
order at most `-a` at `P`, and for `a > 0` the `a`-th power of the maximal ideal of `𝒪_P`.

The defining condition is the multiplicative `v_P z ≤ exp (-a)`, which is junk-free at `z = 0`;
`TauCeti.Place.mem_filtration_iff_le_ord` is the additive form. -/
noncomputable def filtration (P : Place k F) (a : ℤ) : Submodule k F where
  __ := P.valuation.leAddSubgroup (WithZero.exp (-a))
  smul_mem' c z hz := by
    have hz' : P.valuation z ≤ WithZero.exp (-a) := hz
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · have hcz : P.valuation (c • z) ≤ WithZero.exp (-a) := by
        rw [Algebra.smul_def, map_mul, P.isTrivialOn.eq_one c hc, one_mul]
        exact hz'
      exact hcz

variable (P : Place k F)

/-- Membership in `𝔪_P^a`, unfolded. -/
@[simp]
theorem mem_filtration_iff {a : ℤ} {z : F} :
    z ∈ P.filtration a ↔ P.valuation z ≤ WithZero.exp (-a) :=
  (Iff.rfl)

/-- The additive form of membership in `𝔪_P^a`.  The nonvanishing hypothesis guards the junk
value `ord_P 0 = 0`: the zero function lies in `𝔪_P^a` for every `a`, including the negative
ones. -/
theorem mem_filtration_iff_le_ord {a : ℤ} {z : F} (hz : z ≠ 0) :
    z ∈ P.filtration a ↔ a ≤ P.ord z := by
  rw [mem_filtration_iff, P.valuation_eq_exp_neg_ord hz, WithZero.exp_le_exp]
  omega

/-- `𝔪_P^0` is the valuation ring of `P`. -/
theorem mem_filtration_zero_iff {z : F} : z ∈ P.filtration 0 ↔ z ∈ P.integers := by
  simp [mem_integers_iff]

/-- `𝔪_P^1` is the maximal ideal of `𝒪_P`. -/
theorem mem_filtration_one_iff {z : F} (hz : z ≠ 0) :
    z ∈ P.filtration 1 ↔ P.valuation z < 1 := by
  rw [P.mem_filtration_iff_le_ord hz, P.valuation_lt_one_iff_ord_pos hz]
  omega

/-- The filtration decreases: vanishing to higher order is a stronger condition. -/
theorem filtration_antitone : Antitone P.filtration := fun a b hab z hz ↦
  hz.trans (WithZero.exp_le_exp.mpr (by omega))

/-- A function of order at least `a` and one of order at least `b` have a product of order at
least `a + b`. -/
theorem mul_mem_filtration {a b : ℤ} {z w : F} (hz : z ∈ P.filtration a)
    (hw : w ∈ P.filtration b) : z * w ∈ P.filtration (a + b) := by
  have hz' : P.valuation z ≤ WithZero.exp (-a) := hz
  have hw' : P.valuation w ≤ WithZero.exp (-b) := hw
  rw [mem_filtration_iff, map_mul, neg_add, WithZero.exp_add]
  exact mul_le_mul' hz' hw'

/-- A nonzero function lies in the step of the filtration cut out by its own order. -/
theorem mem_filtration_ord {z : F} (hz : z ≠ 0) : z ∈ P.filtration (P.ord z) :=
  (P.mem_filtration_iff_le_ord hz).mpr le_rfl

/-! ### The successive quotients -/

section Residue

variable {P} {a : ℤ} {s : F}

/-- Multiplying a function of order at least `a` by one of order `-a` lands in the valuation
ring: the integrality behind the evaluation map `TauCeti.Place.filtrationResidue`. -/
theorem mul_mem_integers_of_mem_filtration (hs : P.ord s = -a) (hs0 : s ≠ 0) {z : F}
    (hz : z ∈ P.filtration a) : s * z ∈ P.integers := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  · rw [P.mem_integers_iff_ord_nonneg, P.ord_mul hs0 hz0, hs]
    have := (P.mem_filtration_iff_le_ord hz0).mp hz
    omega

/-- Evaluation of `s · z` at `P`, for a fixed function `s` of order `-a`: a `k`-linear map from
`𝔪_P^a` to the residue field `F_P`, whose kernel is `𝔪_P^(a + 1)` and which is surjective.  It
is the local form of the evaluation map in Stichtenoth's proof of Lemma 1.4.8. -/
noncomputable def filtrationResidue (hs : P.ord s = -a) (hs0 : s ≠ 0) :
    P.filtration a →ₗ[k] P.ResidueField where
  toFun z := IsScalarTower.toAlgHom k P.integers P.ResidueField
    ⟨s * (z : F), mul_mem_integers_of_mem_filtration hs hs0 z.2⟩
  map_add' z w := by
    rw [← map_add]
    exact congrArg _ (Subtype.ext (by push_cast; ring))
  map_smul' c z := by
    rw [RingHom.id_apply, ← map_smul]
    exact congrArg _
      (Subtype.ext (by push_cast [Algebra.smul_def, coe_algebraMap_constants]; ring))

theorem filtrationResidue_apply (hs : P.ord s = -a) (hs0 : s ≠ 0) (z : P.filtration a) :
    filtrationResidue hs hs0 z =
      IsLocalRing.residue P.integers
        ⟨s * (z : F), mul_mem_integers_of_mem_filtration hs hs0 z.2⟩ :=
  (rfl)

/-- The evaluation `z ↦ (s · z)(P)` kills exactly the next step of the filtration. -/
theorem ker_filtrationResidue (hs : P.ord s = -a) (hs0 : s ≠ 0) :
    LinearMap.ker (filtrationResidue hs hs0) =
      (P.filtration (a + 1)).submoduleOf (P.filtration a) := by
  have hmem : ∀ z : P.filtration a,
      z ∈ (P.filtration (a + 1)).submoduleOf (P.filtration a) ↔
        (z : F) ∈ P.filtration (a + 1) := fun _ ↦ Iff.rfl
  ext z
  rw [LinearMap.mem_ker, hmem, filtrationResidue_apply]
  rcases eq_or_ne (z : F) 0 with hz0 | hz0
  · have h0 : (⟨s * (z : F), mul_mem_integers_of_mem_filtration hs hs0 z.2⟩ : P.integers) = 0 :=
      Subtype.ext (by simp [hz0])
    rw [h0, map_zero, hz0]
    simp
  · rw [P.residue_eq_zero_iff_ord_pos (mul_ne_zero hs0 hz0), P.ord_mul hs0 hz0, hs,
      P.mem_filtration_iff_le_ord hz0]
    omega

/-- Every residue is attained: `z ↦ (s · z)(P)` maps `𝔪_P^a` onto the residue field. -/
theorem surjective_filtrationResidue (hs : P.ord s = -a) (hs0 : s ≠ 0) :
    Function.Surjective (filtrationResidue hs hs0) := by
  intro ξ
  obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective (R := P.integers) ξ
  have hu : s⁻¹ * (u : F) ∈ P.filtration a := by
    rcases eq_or_ne (u : F) 0 with hu0 | hu0
    · simp [hu0]
    · rw [P.mem_filtration_iff_le_ord (mul_ne_zero (inv_ne_zero hs0) hu0),
        P.ord_mul (inv_ne_zero hs0) hu0, P.ord_inv, hs]
      have := P.mem_integers_iff_ord_nonneg.mp u.2
      omega
  refine ⟨⟨s⁻¹ * (u : F), hu⟩, ?_⟩
  rw [filtrationResidue_apply]
  exact congrArg _ (Subtype.ext (by field_simp))

/-- **The local quotient of the order filtration.**  Multiplication by a function `s` of order
`-a`, followed by evaluation at `P`, identifies `𝔪_P^a / 𝔪_P^(a + 1)` with the residue field
`F_P` as `k`-vector spaces. -/
noncomputable def filtrationQuotientEquivResidueField (hs : P.ord s = -a) (hs0 : s ≠ 0) :
    (↥(P.filtration a) ⧸ (P.filtration (a + 1)).submoduleOf (P.filtration a)) ≃ₗ[k]
      P.ResidueField :=
  (Submodule.quotEquivOfEq _ _ (ker_filtrationResidue hs hs0).symm).trans
    ((filtrationResidue hs hs0).quotKerEquivOfSurjective (surjective_filtrationResidue hs hs0))

end Residue

/-- One step of the order filtration has the rank of the residue field. -/
theorem rank_quotient_filtration_succ (a : ℤ) :
    Module.rank k (↥(P.filtration a) ⧸ (P.filtration (a + 1)).submoduleOf (P.filtration a)) =
      Module.rank k P.ResidueField := by
  obtain ⟨s, hs0, hs⟩ := P.exists_ne_zero_ord_eq (-a)
  exact (filtrationQuotientEquivResidueField hs hs0).rank_eq

/-- Rank is additive along a tower `p ≤ q ≤ r` of subspaces: the relative quotients of the two
steps add up to the relative quotient of the composite.  This is Noether's third isomorphism
theorem together with rank–nullity, and is what turns the one-step computation
`TauCeti.Place.rank_quotient_filtration_succ` into the dimension formula below. -/
private lemma rank_quotient_submoduleOf_tower {M : Type*} [AddCommGroup M] [Module k M]
    {p q r : Submodule k M} (hpq : p ≤ q) (hqr : q ≤ r) :
    Module.rank k (↥r ⧸ p.submoduleOf r) =
      Module.rank k (↥q ⧸ p.submoduleOf q) + Module.rank k (↥r ⧸ q.submoduleOf r) := by
  have hAB : p.submoduleOf r ≤ q.submoduleOf r := Submodule.comap_mono hpq
  set A := p.submoduleOf r with hA
  set f : ↥q →ₗ[k] (↥r ⧸ A) := A.mkQ ∘ₗ Submodule.inclusion hqr with hf
  have hker : LinearMap.ker f = p.submoduleOf q := by
    ext z
    simp [hf, hA, Submodule.submoduleOf, Submodule.inclusion]
  have hrange : LinearMap.range f = (q.submoduleOf r).map A.mkQ := by
    rw [hf, LinearMap.range_comp, Submodule.range_inclusion]
    rfl
  have e₁ : (↥q ⧸ p.submoduleOf q) ≃ₗ[k] ↥((q.submoduleOf r).map A.mkQ) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      ((f.quotKerEquivRange).trans (LinearEquiv.ofEq _ _ hrange))
  have e₂ : ((↥r ⧸ A) ⧸ (q.submoduleOf r).map A.mkQ) ≃ₗ[k] (↥r ⧸ q.submoduleOf r) :=
    Submodule.quotientQuotientEquivQuotient A (q.submoduleOf r) hAB
  have key := Submodule.rank_quotient_add_rank ((q.submoduleOf r).map A.mkQ)
  rw [e₂.rank_eq, ← e₁.rank_eq] at key
  rw [← key, add_comm]

/-- Transport of a relative rank along an equality of indices, which lets the induction below
step from `a + (n + 1 : ℕ)` to `(a + n) + 1` without rewriting inside a quotient type. -/
private lemma rank_quotient_filtration_congr (P : Place k F) {a b b' : ℤ} (h : b = b') :
    Module.rank k (↥(P.filtration a) ⧸ (P.filtration b).submoduleOf (P.filtration a)) =
      Module.rank k (↥(P.filtration a) ⧸ (P.filtration b').submoduleOf (P.filtration a)) := by
  subst h
  rfl

/-- **The dimension of a local quotient of the order filtration**, in the form indexed by a
natural number of steps: `dim_k (𝔪_P^a / 𝔪_P^(a + n)) = n · deg P`, at the level of ranks and so
without any finiteness hypothesis on the residue field. -/
theorem rank_quotient_filtration_add (a : ℤ) (n : ℕ) :
    Module.rank k (↥(P.filtration a) ⧸ (P.filtration (a + n)).submoduleOf (P.filtration a)) =
      n * Module.rank k P.ResidueField := by
  induction n with
  | zero =>
    have : (P.filtration a).submoduleOf (P.filtration a) = ⊤ := Submodule.submoduleOf_self _
    simp [this]
  | succ n ih =>
    have hcast : a + ((n + 1 : ℕ) : ℤ) = a + n + 1 := by push_cast; ring
    have hpq : P.filtration (a + n + 1) ≤ P.filtration (a + n) := P.filtration_antitone (by omega)
    have hqr : P.filtration (a + n) ≤ P.filtration a := P.filtration_antitone (by omega)
    rw [rank_quotient_filtration_congr P hcast, rank_quotient_submoduleOf_tower hpq hqr,
      rank_quotient_filtration_succ, ih]
    push_cast
    ring

/-- **The dimension of a local quotient of the order filtration** (Stichtenoth, Section I.5): the
`k`-dimension of `𝔪_P^a / 𝔪_P^(a + n)` is `n · deg P`.

Both sides are junk — zero — when the residue field is infinite-dimensional over `k`, so no
finiteness hypothesis is needed; for a function field the residue field is always
finite-dimensional (`TauCeti.Place.finiteDimensional_residueField`). -/
theorem finrank_quotient_filtration_add (a : ℤ) (n : ℕ) :
    Module.finrank k (↥(P.filtration a) ⧸ (P.filtration (a + n)).submoduleOf (P.filtration a)) =
      n * P.degree := by
  rw [Module.finrank, rank_quotient_filtration_add, Cardinal.toNat_mul, Cardinal.toNat_natCast,
    degree_eq_finrank, Module.finrank]

/-- **The dimension of a local quotient of the order filtration**, in integer form: for `a ≤ b`,
`dim_k (𝔪_P^a / 𝔪_P^b) = (b - a) · deg P`.  This is the local input of the local-to-global
engine computing `dim_k (A_F(E) / A_F(D)) = deg E - deg D` for the divisor filtration of the
repartition space. -/
theorem finrank_quotient_filtration {a b : ℤ} (hab : a ≤ b) :
    (Module.finrank k (↥(P.filtration a) ⧸ (P.filtration b).submoduleOf (P.filtration a)) : ℤ) =
      (b - a) * P.degree := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  rw [finrank_quotient_filtration_add]
  push_cast
  ring

/-- The local quotients of the order filtration are finite-dimensional as soon as the residue
field is, which for a function field is `TauCeti.Place.finiteDimensional_residueField`.  No
order relation between `a` and `b` is needed: for `b ≤ a` the quotient is trivial. -/
theorem finiteDimensional_quotient_filtration [Module.Finite k P.ResidueField] (a b : ℤ) :
    FiniteDimensional k
      (↥(P.filtration a) ⧸ (P.filtration b).submoduleOf (P.filtration a)) := by
  rcases le_or_gt a b with hab | hab
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
    refine Module.rank_lt_aleph0_iff.mp ?_
    rw [rank_quotient_filtration_add]
    exact Cardinal.mul_lt_aleph0 Cardinal.natCast_lt_aleph0
      (Module.rank_lt_aleph0_iff.mpr ‹Module.Finite k P.ResidueField›)
  · have : (P.filtration b).submoduleOf (P.filtration a) = ⊤ :=
      Submodule.submoduleOf_eq_top.mpr (P.filtration_antitone hab.le)
    rw [this]
    infer_instance

end Place

end TauCeti
