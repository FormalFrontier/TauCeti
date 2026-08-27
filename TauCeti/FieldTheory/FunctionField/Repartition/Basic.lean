/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import TauCeti.FieldTheory.FunctionField.Divisor.Principal
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Basic

/-!
# Repartitions of an algebraic function field

A **repartition** (Chevalley's name; Stichtenoth says *adele*) of an algebraic function field
`F / k` is a family `a : Place k F → F` of elements of `F` itself — no completions are taken —
that is integral at all but finitely many places.  They form the repartition space

`A_F = {a : Place k F → F | ∀ᶠ P in cofinite, v_P (a P) ≤ 1}`,

filtered by the subspaces

`A_F(D) = {a : Place k F → F | ∀ P, v_P (a P) ≤ exp (D P)}`

attached to the divisors `D` of `F / k`.  This file constructs both, embeds `F` diagonally,
and proves the basic calculus of the filtration: it is monotone and directed, it exhausts
`A_F`, and it cuts the diagonal copy of `F` in exactly the Riemann–Roch space `L(D)`.

It is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Definitions 1.5.2 and 1.5.3,
together with the elementary lemmas that Section I.5 uses without numbering them.  The
quotients `A_F(E)/A_F(D)` and `A_F ⧸ (A_F(D) + F)`, the index of specialty, and Weil
differentials are the work that consumes this file.

## Main definitions

* `TauCeti.repartitionSpace`: the repartition space `A_F` (Definition 1.5.2), as a
  `k`-subspace of `Place k F → F`.
* `TauCeti.adeleFiltration`: the subspace `A_F(D)` attached to a divisor (Definition 1.5.3).
* `TauCeti.diagonalRepartitions`: the diagonal copy of `F` inside `Place k F → F`, the image of
  `Pi.constAlgHom`.
* `TauCeti.submoduleOfAdeleFiltrationSupDiagonalRepartitions`: the subspace `(A_F(D) + F) ∩ A_F`
  of `A_F`, whose cokernel computes the index of specialty.
* `TauCeti.repartitionMul`: multiplication of a repartition by a function, as a `k`-algebra map
  to the `k`-linear endomorphisms of `A_F`.

## Main results

* `TauCeti.mem_repartitionSpace_iff_finite` and `TauCeti.mem_adeleFiltration_iff`: the two
  membership conditions, cofinite integrality and the pointwise bound.
* `TauCeti.adeleFiltration_le_repartitionSpace`, `TauCeti.adeleFiltration_mono` and
  `TauCeti.directed_adeleFiltration`: the filtration lands in `A_F`, and is monotone and
  directed.
* `TauCeti.repartitionSpace_eq_iSup` and `TauCeti.coe_repartitionSpace_eq_iUnion`:
  `A_F = ⋃_D A_F(D)`, the exhaustion.
* `TauCeti.diagonalRepartitions_le_repartitionSpace`: the diagonal `F ↪ A_F`, which is where
  the finiteness of the zeros and poles of a function enters.
* `TauCeti.diagonalRepartitions_inf_adeleFiltration`: `F ∩ A_F(D) = L(D)`, the lemma that ties
  the filtration to the Riemann–Roch spaces, and its relative form
  `TauCeti.adeleFiltration_inf_sup_diagonalRepartitions`:
  `A_F(E) ∩ (A_F(D) + F) = A_F(D) + L(E)` for `D ≤ E`.
* `TauCeti.smul_mem_adeleFiltration_iff` and
  `TauCeti.smul_mem_adeleFiltration_sub_principal`: multiplying by a function `z` translates the
  filtration by `div z`, exactly as it does for Riemann–Roch spaces.
* `TauCeti.smul_mem_repartitionSpace` and `TauCeti.smul_mem_diagonalRepartitions`: both `A_F`
  and the diagonal are stable under multiplication by a function.

## Implementation notes

Both membership conditions are stated **multiplicatively**, as `v_P (a P) ≤ exp (D P)`, and never
in the additive form `ord_P (a P) ≥ -D P`.  The additive form is wrong as written: the junk value
`ord_P 0 = 0` would throw the zero entries out of `A_F(D)` at every place where `D P < 0`, so the
additive carrier is not even closed under addition.  With the multiplicative condition,
`v_P 0 = 0 ≤ exp (D P)` holds at every place, so `A_F(D)` contains `0` definitionally.  This is
the same convention as `TauCeti.riemannRochSpace`, entrywise, which is what makes
`TauCeti.diagonalRepartitions_inf_adeleFiltration` hold on the nose.

`A_F` is pinned as a `Submodule k`, because a Weil differential is by definition a `k`-linear
form on it.  Its multiplicative structure is not lost: `TauCeti.one_mem_repartitionSpace` and
`TauCeti.mul_mem_repartitionSpace` record that it is a subring, and
`TauCeti.smul_mem_repartitionSpace` records the `F`-scalar multiplication that the `F`-vector
space structure on the Weil differentials is built from.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.5.
-/

public section

open scoped WithZero

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-! ### The repartition space -/

variable (k F) in
/-- The **repartition space** `A_F` of `F / k` (Stichtenoth, Definition 1.5.2): the families
`a : Place k F → F` whose entries lie in `F` itself — no completions — and are integral at all
but finitely many places.

The integrality condition is the multiplicative `v_P (a P) ≤ 1`, which is junk-free at zero
entries, and the "all but finitely many" is `Filter.cofinite`; the equivalent finite-exceptional-
set form is `TauCeti.mem_repartitionSpace_iff_finite`. -/
noncomputable def repartitionSpace : Submodule k (Place k F → F) where
  carrier := {a : Place k F → F | ∀ᶠ (P : Place k F) in Filter.cofinite, P.valuation (a P) ≤ 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    exact (ha.and hb).mono fun P h ↦
      (P.valuation.map_add (a P) (b P)).trans (max_le h.1 h.2)
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    exact Filter.Eventually.of_forall fun P ↦ by simp
  smul_mem' c a ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rcases eq_or_ne c 0 with rfl | hc
    · exact Filter.Eventually.of_forall fun P ↦ by simp
    · refine ha.mono fun P h ↦ ?_
      rw [Pi.smul_apply, Algebra.smul_def, map_mul, P.isTrivialOn.eq_one c hc, one_mul]
      exact h

/-- Membership in `A_F`, unfolded: the entries are integral at cofinitely many places. -/
@[simp]
theorem mem_repartitionSpace_iff {a : Place k F → F} :
    a ∈ repartitionSpace k F ↔ ∀ᶠ (P : Place k F) in Filter.cofinite, P.valuation (a P) ≤ 1 :=
  (Iff.rfl)

/-- Membership in `A_F` in terms of the finite exceptional set. -/
theorem mem_repartitionSpace_iff_finite {a : Place k F → F} :
    a ∈ repartitionSpace k F ↔ {P : Place k F | ¬ P.valuation (a P) ≤ 1}.Finite :=
  mem_repartitionSpace_iff.trans Filter.eventually_cofinite

/-- Membership in `A_F` in terms of the valuation rings: the entries lie in the local ring at
all but finitely many places. -/
theorem mem_repartitionSpace_iff_integers {a : Place k F → F} :
    a ∈ repartitionSpace k F ↔ ∀ᶠ (P : Place k F) in Filter.cofinite, a P ∈ P.integers := by
  simp only [mem_repartitionSpace_iff, Place.mem_integers_iff]

/-- The constant repartition `1` is a repartition. -/
theorem one_mem_repartitionSpace : (1 : Place k F → F) ∈ repartitionSpace k F := by
  rw [mem_repartitionSpace_iff]
  exact Filter.Eventually.of_forall fun P ↦ by simp

/-- `A_F` is closed under multiplication: it is a subring of `Place k F → F`, not merely a
`k`-subspace. -/
theorem mul_mem_repartitionSpace {a b : Place k F → F} (ha : a ∈ repartitionSpace k F)
    (hb : b ∈ repartitionSpace k F) : a * b ∈ repartitionSpace k F := by
  rw [mem_repartitionSpace_iff] at ha hb ⊢
  refine (Filter.Eventually.and ha hb).mono fun P h ↦ ?_
  rw [Pi.mul_apply, map_mul]
  exact mul_le_one' h.1 h.2

/-! ### The filtration by divisors -/

/-- The subspace `A_F(D)` of the repartition space attached to a divisor `D` (Stichtenoth,
Definition 1.5.3): the repartitions whose pole at each place `P` is bounded by `D P`.

The condition is the multiplicative `v_P (a P) ≤ exp (D P)` at every place, entrywise the
condition defining `TauCeti.riemannRochSpace`.  In particular `0 ∈ A_F(D)` definitionally, for
every `D`, which the additive form `ord_P (a P) ≥ -D P` would get wrong. -/
noncomputable def adeleFiltration (D : Divisor k F) : Submodule k (Place k F → F) where
  carrier := {a | ∀ P : Place k F, P.valuation (a P) ≤ WithZero.exp (D.coeff P)}
  add_mem' {a b} ha hb P := (P.valuation.map_add (a P) (b P)).trans (max_le (ha P) (hb P))
  zero_mem' P := by simp
  smul_mem' c a ha P := by
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · rw [Pi.smul_apply, Algebra.smul_def, map_mul, P.isTrivialOn.eq_one c hc, one_mul]
      exact ha P

/-- Membership in `A_F(D)`, unfolded: the poles of the entries are bounded by `D`. -/
@[simp]
theorem mem_adeleFiltration_iff {D : Divisor k F} {a : Place k F → F} :
    a ∈ adeleFiltration D ↔ ∀ P : Place k F, P.valuation (a P) ≤ WithZero.exp (D.coeff P) :=
  (Iff.rfl)

/-- The additive form of the bound: at each place with a nonzero entry the order is at least
`-D P`.  The nonvanishing guard is not a hypothesis but part of the statement, because
`ord_P 0 = 0` is a junk value: a zero entry satisfies the multiplicative bound at every place,
including those where `D P < 0`. -/
theorem mem_adeleFiltration_iff_neg_le_ord {D : Divisor k F} {a : Place k F → F} :
    a ∈ adeleFiltration D ↔ ∀ P : Place k F, a P ≠ 0 → -D.coeff P ≤ P.ord (a P) := by
  refine forall_congr' fun P ↦ ?_
  rcases eq_or_ne (a P) 0 with h | h
  · simp [h]
  · rw [P.valuation_eq_exp_neg_ord h, WithZero.exp_le_exp]
    exact ⟨fun hle _ ↦ by omega, fun hle ↦ by have := hle h; omega⟩

/-- `A_F(0)` consists of the everywhere integral repartitions. -/
theorem mem_adeleFiltration_zero_iff {a : Place k F → F} :
    a ∈ adeleFiltration (0 : Divisor k F) ↔ ∀ P : Place k F, a P ∈ P.integers := by
  simp [Place.mem_integers_iff]

/-- Enlarging the divisor enlarges the subspace. -/
theorem adeleFiltration_mono {D E : Divisor k F} (h : D ≤ E) :
    adeleFiltration D ≤ adeleFiltration E := fun _ ha P ↦
  (ha P).trans (WithZero.exp_le_exp.mpr (WeilDivisor.coeff_le_coeff h P))

/-- The filtration is directed: any two of its members are contained in a third, namely the one
attached to the pointwise maximum of the two divisors. -/
theorem directed_adeleFiltration :
    Directed (· ≤ ·) (adeleFiltration : Divisor k F → Submodule k (Place k F → F)) :=
  fun D E ↦ ⟨D ⊔ E, adeleFiltration_mono le_sup_left, adeleFiltration_mono le_sup_right⟩

/-- Every `A_F(D)` consists of repartitions: outside the support of `D` its defining bound reads
`v_P (a P) ≤ exp 0 = 1`. -/
theorem adeleFiltration_le_repartitionSpace (D : Divisor k F) :
    adeleFiltration D ≤ repartitionSpace k F := by
  intro a ha
  rw [mem_repartitionSpace_iff_finite]
  refine (D.support.finite_toSet).subset fun P hP ↦ ?_
  rw [Finset.mem_coe, WeilDivisor.mem_support_iff]
  intro hD
  exact hP (by simpa only [hD, WithZero.exp_zero] using ha P)

/-- Every repartition is bounded by some divisor: the exceptional set is finite, and the pole
orders `max 0 (-ord_P (a P))` of the entries there are the coefficients of a divisor that
works. -/
theorem exists_mem_adeleFiltration {a : Place k F → F} (ha : a ∈ repartitionSpace k F) :
    ∃ D : Divisor k F, a ∈ adeleFiltration D := by
  classical
  have hfin : {P : Place k F | ¬ P.valuation (a P) ≤ 1}.Finite :=
    mem_repartitionSpace_iff_finite.mp ha
  refine ⟨Finsupp.onFinset hfin.toFinset (fun P ↦ max 0 (-P.ord (a P))) ?_, ?_⟩
  · intro P hP
    rw [Set.Finite.mem_toFinset]
    have hord : P.ord (a P) < 0 := by
      by_contra hle
      exact hP (max_eq_left (by omega))
    have hne : a P ≠ 0 := fun h ↦ by simp [h, Place.ord_zero] at hord
    intro hcon
    rw [P.valuation_eq_exp_neg_ord hne, ← WithZero.exp_zero, WithZero.exp_le_exp] at hcon
    omega
  · intro P
    rcases eq_or_ne (a P) 0 with h | h
    · simp [h]
    · rw [P.valuation_eq_exp_neg_ord h, WithZero.exp_le_exp]
      exact le_max_right _ _

/-- **The filtration exhausts the repartition space**: `A_F = ⨆_D A_F(D)`. -/
theorem repartitionSpace_eq_iSup :
    ⨆ D : Divisor k F, adeleFiltration D = repartitionSpace k F := by
  refine le_antisymm (iSup_le adeleFiltration_le_repartitionSpace) fun a ha ↦ ?_
  obtain ⟨D, hD⟩ := exists_mem_adeleFiltration ha
  exact le_iSup (fun D : Divisor k F ↦ adeleFiltration D) D hD

/-- **The filtration exhausts the repartition space**, as the literal union of sets:
`A_F = ⋃_D A_F(D)`.  The union is directed by `TauCeti.directed_adeleFiltration`. -/
theorem coe_repartitionSpace_eq_iUnion :
    (repartitionSpace k F : Set (Place k F → F)) =
      ⋃ D : Divisor k F, (adeleFiltration D : Set (Place k F → F)) := by
  ext a
  simp only [SetLike.mem_coe, Set.mem_iUnion]
  exact ⟨exists_mem_adeleFiltration, fun ⟨D, hD⟩ ↦ adeleFiltration_le_repartitionSpace D hD⟩

/-! ### The diagonal copy of `F` -/

variable (k F) in
/-- The diagonal copy of `F` inside `Place k F → F`: the constant families.  Together with
`TauCeti.diagonalRepartitions_le_repartitionSpace` this is the embedding `F ↪ A_F` of
Stichtenoth, Definition 1.5.2. -/
noncomputable def diagonalRepartitions : Submodule k (Place k F → F) :=
  LinearMap.range (Pi.constAlgHom k (Place k F) F).toLinearMap

/-- Membership in the diagonal: a repartition is diagonal exactly when it is constant. -/
theorem mem_diagonalRepartitions_iff {a : Place k F → F} :
    a ∈ diagonalRepartitions k F ↔ ∃ f : F, Function.const (Place k F) f = a := by
  rw [diagonalRepartitions, LinearMap.mem_range]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy⟩, fun ⟨f, hf⟩ ↦ ⟨f, hf⟩⟩

/-- The constant families are diagonal. -/
theorem const_mem_diagonalRepartitions (f : F) :
    Function.const (Place k F) f ∈ diagonalRepartitions k F :=
  mem_diagonalRepartitions_iff.mpr ⟨f, rfl⟩

/-- **The diagonal embedding `F ↪ A_F`** at the level of elements: a function of an algebraic
function field is integral at all but finitely many places, because it has only finitely many
poles (Stichtenoth, Corollary 1.3.4). -/
theorem const_mem_repartitionSpace (hF : IsFunctionField k F) (f : F) :
    Function.const (Place k F) f ∈ repartitionSpace k F := by
  rw [mem_repartitionSpace_iff_finite]
  refine (Place.finite_setOf_ord_ne_zero hF f).subset fun P hP ↦ ?_
  have hf : f ≠ 0 := by
    rintro rfl
    exact hP (by simp)
  have hP' : ¬ P.valuation f ≤ 1 := hP
  rw [P.valuation_eq_exp_neg_ord hf, ← WithZero.exp_zero, WithZero.exp_le_exp] at hP'
  exact fun hcon ↦ hP' (by omega)

/-- **The diagonal embedding `F ↪ A_F`**: the constant families are repartitions. -/
theorem diagonalRepartitions_le_repartitionSpace (hF : IsFunctionField k F) :
    diagonalRepartitions k F ≤ repartitionSpace k F := by
  intro a ha
  obtain ⟨f, rfl⟩ := mem_diagonalRepartitions_iff.mp ha
  exact const_mem_repartitionSpace hF f

/-- A constant family lies in `A_F(D)` exactly when its value lies in `L(D)`: the two
conditions are literally the same, since `A_F(D)` is the entrywise `L(D)` condition. -/
theorem const_mem_adeleFiltration_iff {D : Divisor k F} {f : F} :
    Function.const (Place k F) f ∈ adeleFiltration D ↔ f ∈ riemannRochSpace D := by
  simp only [mem_adeleFiltration_iff, mem_riemannRochSpace_iff, Function.const_apply]

/-- **`F ∩ A_F(D) = L(D)`**: the diagonal meets the `D`-th step of the filtration in exactly
the Riemann–Roch space of `D`.  This is the lemma that makes the repartition quotients compute
the index of specialty. -/
theorem diagonalRepartitions_inf_adeleFiltration (D : Divisor k F) :
    diagonalRepartitions k F ⊓ adeleFiltration D =
      (riemannRochSpace D).map (Pi.constAlgHom k (Place k F) F).toLinearMap := by
  ext a
  rw [Submodule.mem_inf, Submodule.mem_map]
  constructor
  · rintro ⟨hdiag, hfilt⟩
    obtain ⟨f, rfl⟩ := mem_diagonalRepartitions_iff.mp hdiag
    exact ⟨f, const_mem_adeleFiltration_iff.mp hfilt, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨const_mem_diagonalRepartitions f, const_mem_adeleFiltration_iff.mpr hf⟩

/-- **The relative form of `F ∩ A_F(D) = L(D)`** (Stichtenoth, in the proof of Theorem 1.5.4):
for `D ≤ E`, a repartition bounded by `E` that differs from a constant by a repartition bounded
by `D` differs from a constant of `L(E)`, so that

`A_F(E) ∩ (A_F(D) + F) = A_F(D) + L(E)`.

Given `A_F(D) ≤ A_F(E)` this is the modular law for the lattice of subspaces followed by
`TauCeti.diagonalRepartitions_inf_adeleFiltration`. -/
theorem adeleFiltration_inf_sup_diagonalRepartitions {D E : Divisor k F} (h : D ≤ E) :
    adeleFiltration E ⊓ (adeleFiltration D ⊔ diagonalRepartitions k F) =
      adeleFiltration D ⊔
        (riemannRochSpace E).map (Pi.constAlgHom k (Place k F) F).toLinearMap := by
  rw [inf_comm, sup_inf_assoc_of_le _ (adeleFiltration_mono h),
    diagonalRepartitions_inf_adeleFiltration]

/-- The constant repartition of a function of `L(E)` is bounded by `E`, and is a constant, so it
lies in `A_F(E) ∩ (A_F(D) + F)`. -/
theorem const_mem_adeleFiltration_inf_sup_diagonalRepartitions (D : Divisor k F)
    {E : Divisor k F} {f : F} (hf : f ∈ riemannRochSpace E) :
    Function.const (Place k F) f ∈
      adeleFiltration E ⊓ (adeleFiltration D ⊔ diagonalRepartitions k F) :=
  ⟨const_mem_adeleFiltration_iff.mpr hf,
    Submodule.mem_sup_right (const_mem_diagonalRepartitions f)⟩

/-- Membership in `A_F(D) + F`, the subspace whose cokernel in `A_F` computes the index of
specialty: a repartition lies in it exactly when subtracting a single constant brings it into
`A_F(D)`. -/
theorem mem_adeleFiltration_sup_diagonalRepartitions_iff {D : Divisor k F}
    {a : Place k F → F} :
    a ∈ adeleFiltration D ⊔ diagonalRepartitions k F ↔
      ∃ f : F, (fun P ↦ a P - f) ∈ adeleFiltration D := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨f, rfl⟩ := mem_diagonalRepartitions_iff.mp hz
    refine ⟨f, ?_⟩
    have hfun : (fun P ↦ (y + Function.const (Place k F) f) P - f) = y := by
      funext P
      simp
    rw [hfun]
    exact hy
  · rintro ⟨f, hf⟩
    refine ⟨fun P ↦ a P - f, hf, Function.const (Place k F) f,
      const_mem_diagonalRepartitions f, ?_⟩
    funext P
    simp

/-- `A_F(D) + F` is a subspace of the repartition space. -/
theorem adeleFiltration_sup_diagonalRepartitions_le (hF : IsFunctionField k F)
    (D : Divisor k F) :
    adeleFiltration D ⊔ diagonalRepartitions k F ≤ repartitionSpace k F :=
  sup_le (adeleFiltration_le_repartitionSpace D) (diagonalRepartitions_le_repartitionSpace hF)

/-- The subspace `(A_F(D) + F) ∩ A_F` of the repartition space: the repartitions that differ
from a constant by one whose poles are bounded by `D`.  Its cokernel in `A_F` is the index of
specialty of `D`, and a Weil differential bounded by `D` is a `k`-linear form killing it. -/
noncomputable def submoduleOfAdeleFiltrationSupDiagonalRepartitions (D : Divisor k F) :
    Submodule k ↥(repartitionSpace k F) :=
  (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf (repartitionSpace k F)

/-- `(A_F(D) + F) ∩ A_F` is `A_F(D) + F` cut down to `A_F` in the sense of
`Submodule.submoduleOf`, so that combinator's API applies to it. -/
theorem submoduleOfAdeleFiltrationSupDiagonalRepartitions_eq_submoduleOf (D : Divisor k F) :
    submoduleOfAdeleFiltrationSupDiagonalRepartitions D =
      (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf (repartitionSpace k F) := by
  rfl

/-- Membership in `(A_F(D) + F) ∩ A_F` is membership in `A_F(D) + F` of the underlying family. -/
@[simp]
theorem mem_submoduleOfAdeleFiltrationSupDiagonalRepartitions_iff {D : Divisor k F}
    {a : ↥(repartitionSpace k F)} :
    a ∈ submoduleOfAdeleFiltrationSupDiagonalRepartitions D ↔
      (a : Place k F → F) ∈ adeleFiltration D ⊔ diagonalRepartitions k F :=
  (Iff.rfl)

/-- Enlarging the divisor enlarges `(A_F(D) + F) ∩ A_F`. -/
theorem submoduleOfAdeleFiltrationSupDiagonalRepartitions_mono {D E : Divisor k F} (h : D ≤ E) :
    submoduleOfAdeleFiltrationSupDiagonalRepartitions D ≤
      submoduleOfAdeleFiltrationSupDiagonalRepartitions E :=
  Submodule.comap_mono (sup_le_sup_right (adeleFiltration_mono h) _)

/-! ### Translating the filtration by a principal divisor -/

/-- Multiplying a repartition by a nonzero function `z` translates the filtration by `div z`:
the entrywise valuations are all scaled by `v_P z = exp (-ord_P z)`. -/
theorem smul_mem_adeleFiltration_iff (hF : IsFunctionField k F) (z : Fˣ) (D : Divisor k F)
    (a : Place k F → F) :
    (z : F) • a ∈ adeleFiltration D ↔ a ∈ adeleFiltration (D + Divisor.principal hF z) := by
  refine forall_congr' fun P ↦ ?_
  rw [WeilDivisor.coeff_add, Divisor.coeff_principal, Pi.smul_apply, smul_eq_mul, map_mul,
    P.valuation_eq_exp_neg_ord (Units.ne_zero z)]
  rcases eq_or_ne (a P) 0 with h | h
  · simp [h]
  · rw [P.valuation_eq_exp_neg_ord h, ← WithZero.exp_add, WithZero.exp_le_exp,
      WithZero.exp_le_exp]
    omega

/-- Multiplying by `z` carries `A_F(D)` into `A_F(D - div z)`, the repartition analogue of
`TauCeti.mul_mem_riemannRochSpace_sub_principal`. -/
theorem smul_mem_adeleFiltration_sub_principal (hF : IsFunctionField k F) (z : Fˣ)
    {D : Divisor k F} {a : Place k F → F} (ha : a ∈ adeleFiltration D) :
    (z : F) • a ∈ adeleFiltration (D - Divisor.principal hF z) := by
  rw [smul_mem_adeleFiltration_iff hF z, sub_add_cancel]
  exact ha

/-- The repartition space is stable under multiplication by a function: it is an `F`-subspace
of `Place k F → F`, which is what the `F`-vector space structure on the Weil differentials is
built from. -/
theorem smul_mem_repartitionSpace (hF : IsFunctionField k F) (f : F) {a : Place k F → F}
    (ha : a ∈ repartitionSpace k F) : f • a ∈ repartitionSpace k F := by
  have h : f • a = Function.const (Place k F) f * a := by
    funext P
    simp [smul_eq_mul]
  rw [h]
  exact mul_mem_repartitionSpace (const_mem_repartitionSpace hF f) ha

/-- The diagonal copy of `F` is stable under multiplication by a function: a constant times a
constant is a constant. -/
theorem smul_mem_diagonalRepartitions (f : F) {a : Place k F → F}
    (ha : a ∈ diagonalRepartitions k F) : f • a ∈ diagonalRepartitions k F := by
  obtain ⟨g, rfl⟩ := mem_diagonalRepartitions_iff.mp ha
  refine mem_diagonalRepartitions_iff.mpr ⟨f * g, ?_⟩
  funext P
  simp [smul_eq_mul]

/-- Multiplication of repartitions by a function, as a `k`-algebra map to the `k`-linear
endomorphisms of the repartition space.  It lands in the repartition space because a function of
an algebraic function field has only finitely many poles. -/
noncomputable def repartitionMul (hF : IsFunctionField k F) :
    F →ₐ[k] Module.End k ↥(repartitionSpace k F) where
  toFun f :=
    { toFun a := ⟨f • (a : Place k F → F), smul_mem_repartitionSpace hF f a.2⟩
      map_add' a b := Subtype.ext (by simp [smul_add])
      map_smul' c a := Subtype.ext (by simp [smul_comm f c]) }
  map_one' := LinearMap.ext fun a ↦ Subtype.ext (by simp)
  map_mul' f g := LinearMap.ext fun a ↦ Subtype.ext (by simp [mul_smul])
  map_zero' := LinearMap.ext fun a ↦ Subtype.ext (by simp)
  map_add' f g := LinearMap.ext fun a ↦ Subtype.ext (by simp [add_smul])
  commutes' c := LinearMap.ext fun a ↦ Subtype.ext (by simp [algebraMap_smul])

/-- Multiplying a repartition by `f` multiplies each of its entries by `f`. -/
@[simp]
theorem coe_repartitionMul_apply (hF : IsFunctionField k F) (f : F)
    (a : ↥(repartitionSpace k F)) :
    ((repartitionMul hF f a : ↥(repartitionSpace k F)) : Place k F → F) =
      f • (a : Place k F → F) :=
  (rfl)

end TauCeti
