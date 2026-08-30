/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Approximation
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic

/-!
# The places lying over a fixed place: the fundamental inequality

Let `F' / k'` be a finite extension of the field extension `F / k`. Every place of `F' / k'`
restricts to a place of `F / k` (`TauCeti.Place.restrict`), and the places over a fixed place `P`
of `F / k` form the fibre of that map. This file bounds that fibre: for any finite family of
distinct places over `P`,

`∑ e(P' ∣ P) · f(P' ∣ P) ≤ [F' : F]`,

the **fundamental inequality**, one half of Stichtenoth's fundamental identity. Since each
summand is at least `1`, the fibre is finite and has at most `[F' : F]` elements.

The bound at a single place, `e · f ≤ [F' : F]`, is
`TauCeti.Place.ramificationIdx_mul_relativeDegree_le_finrank`, proved by exhibiting `e · f`
elements of `F'` independent over `F`. The passage to several places is weak approximation: the
`e · f` witnesses attached to a place `Q` of the family are replaced by functions agreeing with
them to first order at `Q` and vanishing to order `[F' : F]` at every other place of the family,
so the blocks belonging to different places cannot interfere. Normalizing the coefficients of a
hypothetical relation by one of least order at `P` — which is where the places of the fibre being
restrictions of *the same* `P` is used — makes one block a unit multiple of a power of a prime
element, hence of order less than its ramification index, while every other block has order at
least `[F' : F]`; the strict triangle inequality then forbids the relation.

## Main results

* `TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_le_finrank`: **the fundamental
  inequality** (Stichtenoth, Theorem 3.1.11).
* `TauCeti.Place.finite_setOf_restrict_eq`: a place of `F / k` has only finitely many extensions
  to `F' / k'` (Stichtenoth, Proposition 3.1.7).
* `TauCeti.Place.ncard_setOf_restrict_eq_le_finrank`: it has at most `[F' : F]` of them
  (Stichtenoth, Corollary 3.1.12).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.1.
-/

public section

open scoped WithZero

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']

variable (k F)

/-- Elements of `𝒪_{P'}` whose residues form a basis of the residue field extension: the
`f(P' ∣ P)` witnesses that the fundamental inequality attaches to `P'`. -/
private theorem exists_linearIndependent_residue (P' : Place k' F') :
    ∃ z : Fin (relativeDegree k F P') → P'.integers,
      LinearIndependent (P'.restrict k F).ResidueField
        fun j ↦ IsLocalRing.residue P'.integers (z j) := by
  set B := Module.finBasisOfFinrankEq (P'.restrict k F).ResidueField P'.ResidueField
    (relativeDegree_def k F P').symm
  choose z hz using fun j : Fin (relativeDegree k F P') ↦
    IsLocalRing.residue_surjective (R := P'.integers) (B j)
  exact ⟨z, by simpa only [hz] using B.linearIndependent⟩

/-- **One block of a relation, at its own place.** Take elements `s` of `𝒪_{P'}` with independent
residues, a prime element `t` for `P'`, and coefficients `b` in `𝒪_P` indexed by the pairs
`(j, l)` with `l < e(P' ∣ P)`, one of them — say the one at `(j₀, l₀)` — a unit. Then the
combination `∑ b (j, l) · s j · t ^ l` is nonzero of order at most `l₀` at `P'`: the inner sums
over `j` have order divisible by `e(P' ∣ P)`, so the `e(P' ∣ P)` blocks in `l` have pairwise
distinct orders, and the block of `l₀` has order exactly `l₀`. -/
private theorem sum_block_ne_zero_and_ord_le (P' : Place k' F') {ι : Type*} [Fintype ι]
    (s : ι → P'.integers)
    (hind : LinearIndependent (P'.restrict k F).ResidueField
      fun i ↦ IsLocalRing.residue P'.integers (s i))
    (b : ι × Fin (ramificationIdx F P') → (P'.restrict k F).integers)
    {j₀ : ι} {l₀ : Fin (ramificationIdx F P')} (hb₀ : IsUnit (b (j₀, l₀)))
    {t : F'} (ht : P'.ord t = 1) :
    (∑ q : ι × Fin (ramificationIdx F P'),
        algebraMap F F' ((b q : F)) * ((s q.1 : F') * t ^ (q.2 : ℕ))) ≠ 0 ∧
      P'.ord (∑ q : ι × Fin (ramificationIdx F P'),
        algebraMap F F' ((b q : F)) * ((s q.1 : F') * t ^ (q.2 : ℕ))) ≤ ((l₀ : ℕ) : ℤ) := by
  classical
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hb₀ne : ((b (j₀, l₀) : F)) ≠ 0 := by
    intro h
    refine hb₀.ne_zero ?_
    ext
    simpa using h
  set A : Fin (ramificationIdx F P') → F' := fun l ↦
    ∑ j, algebraMap F F' ((b (j, l) : F)) * (s j : F') with hA
  have hAdvd : ∀ l, (ramificationIdx F P' : ℤ) ∣ P'.ord (A l) := fun l ↦
    ramificationIdx_dvd_ord_sum_of_linearIndependent_residue k F P' s hind _
  have hA₀ne : A l₀ ≠ 0 :=
    sum_ne_zero_of_linearIndependent_residue k F P' s hind (fun j ↦ ((b (j, l₀) : F)))
      (i₁ := j₀) hb₀ne
  have hA₀ord : P'.ord (A l₀) = 0 :=
    ord_sum_eq_zero_of_isUnit k F P' s hind (fun j ↦ b (j, l₀)) (i₀ := j₀) hb₀
  set T : Fin (ramificationIdx F P') → F' := fun l ↦ A l * t ^ (l : ℕ) with hT
  have hTord : ∀ l, T l ≠ 0 →
      ∃ m : ℤ, P'.ord (T l) = (ramificationIdx F P' : ℤ) * m + (l : ℕ) := by
    intro l hl
    have hAl : A l ≠ 0 := fun h ↦ hl (by simp [hT, h])
    obtain ⟨m, hm⟩ := hAdvd l
    exact ⟨m, by rw [hT, P'.ord_mul hAl (pow_ne_zero _ ht0), P'.ord_pow, hm, ht, mul_one]⟩
  have hT₀ : T l₀ ≠ 0 := by rw [hT]; exact mul_ne_zero hA₀ne (pow_ne_zero _ ht0)
  have hsum : (∑ q : ι × Fin (ramificationIdx F P'),
      algebraMap F F' ((b q : F)) * ((s q.1 : F') * t ^ (q.2 : ℕ))) = ∑ l, T l := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [hT, hA]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hsum]
  refine ⟨sum_ne_zero_of_ord_eq_mul_add_natCast P' T hTord hT₀, ?_⟩
  calc P'.ord (∑ l, T l) ≤ P'.ord (T l₀) :=
        ord_sum_le_of_ord_eq_mul_add_natCast P' T hTord hT₀
    _ = ((l₀ : ℕ) : ℤ) := by
        rw [hT, P'.ord_mul hA₀ne (pow_ne_zero _ ht0), P'.ord_pow, hA₀ord, ht, mul_one, zero_add]

/-- **The products `w i j * τ i ^ l` are `F`-linearly independent across the whole fibre.** Given,
at each place `Q i` over `P`, a prime element `τ i` for `Q i` that is integral at the other places
of the family, and lifts `w i j` of a family of residues independent over the residue field of `P`,
each of order at least `e(Q m ∣ P)` at every other place `Q m`, the `e(Q i ∣ P) · f(Q i ∣ P)`
products `w i j * τ i ^ l` are linearly independent over `F` **jointly over all of `i`** — which is
what distinguishes this from the one-place
`TauCeti.Place.linearIndependent_mul_pow_of_linearIndependent_residue` in `Extension/Basic.lean`.
Counting the resulting `∑ i, e(Q i ∣ P) · f(Q i ∣ P)` products is what gives the fundamental
inequality. -/
private theorem linearIndependent_mul_pow_of_forall_linearIndependent_residue {ι : Type*}
    [Finite ι] {Q : ι → Place k' F'} {P : Place k F}
    (hQP : ∀ i, (Q i).restrict k F = P)
    {τ : ι → F'} (hτone : ∀ i, (Q i).ord (τ i) = 1)
    (hτint : ∀ i m, m ≠ i → 0 ≤ (Q m).ord (τ i))
    {w : ∀ i, Fin (relativeDegree k F (Q i)) → F'} (hwmem : ∀ i j, w i j ∈ (Q i).integers)
    (hwN : ∀ (i : ι) (j : Fin (relativeDegree k F (Q i))) (m : ι), m ≠ i →
      (ramificationIdx F (Q m) : ℤ) ≤ (Q m).ord (w i j))
    (hindres : ∀ i, LinearIndependent ((Q i).restrict k F).ResidueField
      fun j ↦ IsLocalRing.residue (Q i).integers (⟨w i j, hwmem i j⟩ : (Q i).integers)) :
    LinearIndependent F
      (fun p : Σ i : ι, Fin (relativeDegree k F (Q i)) × Fin (ramificationIdx F (Q i)) ↦
        w p.1 p.2.1 * τ p.1 ^ (p.2.2 : ℕ)) := by
  classical
  have _ : Fintype ι := Fintype.ofFinite ι
  set V : (Σ i : ι, Fin (relativeDegree k F (Q i)) × Fin (ramificationIdx F (Q i))) → F' :=
    fun p ↦ w p.1 p.2.1 * τ p.1 ^ (p.2.2 : ℕ) with hV
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hex
  obtain ⟨p₁, hp₁⟩ := not_forall.mp hex
  -- Pick a coefficient of least order at `P` among the nonzero ones and divide by it.
  obtain ⟨⟨i₀, j₀, l₀⟩, hg₀, hbP⟩ := P.exists_ne_zero_forall_div_mem_integers g hp₁
  have hbmem : ∀ p, g p / g ⟨i₀, j₀, l₀⟩ ∈ ((Q i₀).restrict k F).integers := fun p ↦ by
    rw [hQP i₀]
    exact hbP p
  set b : (Σ i : ι, Fin (relativeDegree k F (Q i)) × Fin (ramificationIdx F (Q i))) →
    ((Q i₀).restrict k F).integers := fun p ↦ ⟨g p / g ⟨i₀, j₀, l₀⟩, hbmem p⟩
  have hbcoe : ∀ p, ((b p : F)) = g p / g ⟨i₀, j₀, l₀⟩ := fun _ ↦ rfl
  have hb₀ : b ⟨i₀, j₀, l₀⟩ = 1 := Subtype.ext (by simp [hbcoe, div_self hg₀])
  -- The relation splits into one block per place of the family, and the blocks sum to zero.
  set Z : ι → F' := fun i ↦
    ∑ q : Fin (relativeDegree k F (Q i)) × Fin (ramificationIdx F (Q i)),
      algebraMap F F' ((b ⟨i, q⟩ : F)) * V ⟨i, q⟩ with hZ
  have hZsum : ∑ i, Z i = 0 := by
    have hgsum : ∑ p, algebraMap F F' ((b p : F)) * V p = 0 := by
      have hterm : ∑ p, algebraMap F F' ((b p : F)) * V p =
          (algebraMap F F' (g ⟨i₀, j₀, l₀⟩))⁻¹ * ∑ p, g p • V p := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [hbcoe, div_eq_inv_mul, map_mul, map_inv₀, Algebra.smul_def]
        ring
      rw [hterm, hg, mul_zero]
    calc ∑ i, Z i = ∑ p, algebraMap F F' ((b p : F)) * V p := by
          simp only [hZ]
          rw [Finset.sum_sigma', Finset.univ_sigma_univ]
      _ = 0 := hgsum
  -- The block at `i₀` is nonzero of order less than the ramification index there. Unfolding `Z`
  -- and `V` is what puts it in the shape the block lemma speaks about.
  obtain ⟨hZne, hZord⟩ : Z i₀ ≠ 0 ∧ (Q i₀).ord (Z i₀) ≤ ((l₀ : ℕ) : ℤ) := by
    have hblock := sum_block_ne_zero_and_ord_le k F (Q i₀)
      (fun j ↦ (⟨w i₀ j, hwmem i₀ j⟩ : (Q i₀).integers)) (hindres i₀)
      (fun q ↦ b ⟨i₀, q⟩) (j₀ := j₀) (l₀ := l₀) (hb₀ ▸ isUnit_one) (hτone i₀)
    simpa only [hZ, hV] using hblock
  -- Every other block has order at least `e(Q i₀ ∣ P)` at `Q i₀`.
  have hZm : ∀ m, m ≠ i₀ →
      (Q i₀).valuation (Z m) ≤ WithZero.exp (-(ramificationIdx F (Q i₀) : ℤ)) := by
    intro m hm
    simp only [hZ]
    refine Valuation.map_sum_le _ fun q _ ↦ ?_
    have hb1 : (Q i₀).valuation (algebraMap F F' ((b ⟨m, q⟩ : F))) ≤ 1 := by
      refine (Q i₀).mem_integers_iff.mp ((Q i₀).mem_integers_iff_ord_nonneg.mpr ?_)
      rw [ord_algebraMap_restrict k F (Q i₀) ((b ⟨m, q⟩ : F))]
      exact mul_nonneg (by positivity)
        (((Q i₀).restrict k F).mem_integers_iff_ord_nonneg.mp (b ⟨m, q⟩).2)
    have hwval : (Q i₀).valuation (w m q.1) ≤
        WithZero.exp (-(ramificationIdx F (Q i₀) : ℤ)) := by
      have hne : w m q.1 ≠ 0 := by
        intro h
        have hh := hwN m q.1 i₀ (Ne.symm hm)
        have he := ramificationIdx_pos (F := F) (Q i₀)
        rw [h, ord_zero] at hh
        omega
      rw [(Q i₀).valuation_eq_exp_neg_ord hne]
      exact WithZero.exp_le_exp.2 (neg_le_neg (hwN m q.1 i₀ (Ne.symm hm)))
    have hτval : (Q i₀).valuation (τ m ^ (q.2 : ℕ)) ≤ 1 := by
      rw [map_pow]
      exact pow_le_one' ((Q i₀).mem_integers_iff.mp
        ((Q i₀).mem_integers_iff_ord_nonneg.mpr (hτint m i₀ (Ne.symm hm)))) _
    simp only [hV]
    rw [map_mul, map_mul]
    exact (mul_le_of_le_one_left' hb1).trans ((mul_le_of_le_one_right' hτval).trans hwval)
  -- The strict triangle inequality contradicts `∑ i, Z i = 0`.
  have hlt : ∀ m ∈ (Finset.univ : Finset ι) \ {i₀},
      (Q i₀).valuation (Z m) < (Q i₀).valuation (Z i₀) := by
    intro m hmem
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hmem
    refine lt_of_le_of_lt (hZm m hmem.2) ?_
    rw [(Q i₀).valuation_eq_exp_neg_ord hZne, WithZero.exp_lt_exp]
    have hl₀ : (l₀ : ℕ) < ramificationIdx F (Q i₀) := l₀.2
    omega
  have hval := (Q i₀).valuation.map_sum_eq_of_lt (Finset.mem_univ i₀) hlt
  rw [hZsum, map_zero] at hval
  exact ((Valuation.ne_zero_iff _).mpr hZne) hval.symm

/-- **The fundamental inequality**, for a family of places indexed by a finite type. This is the
form the proof produces; `TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_le_finrank` is the
`Finset` restatement used elsewhere. -/
private theorem sum_relativeDegree_mul_ramificationIdx_le_finrank {ι : Type*} [Fintype ι]
    {Q : ι → Place k' F'} (hQ : Function.Injective Q) {P : Place k F}
    (hQP : ∀ i, (Q i).restrict k F = P) :
    ∑ i, relativeDegree k F (Q i) * ramificationIdx F (Q i) ≤ Module.finrank F F' := by
  classical
  set N : ℕ := Module.finrank F F' with hNdef
  -- A function with a simple zero at `Q i` and a unit value at every other place of the family.
  obtain ⟨τ, hτ⟩ : ∃ τ : ι → F', ∀ i m, (Q m).ord (τ i) = if m = i then 1 else 0 := by
    choose τ hτ using fun i : ι ↦ exists_forall_ord_eq hQ fun m ↦ if m = i then (1 : ℤ) else 0
    exact ⟨τ, hτ⟩
  -- Lifts to `𝒪_{Q i}` of a basis of the residue field extension at `Q i`, …
  choose z hz using fun i : ι ↦ exists_linearIndependent_residue k F (Q i)
  -- … moved by weak approximation away from the other places of the family.
  have happrox : ∀ (i : ι) (j : Fin (relativeDegree k F (Q i))), ∃ x : F',
      (Q i).ord (x - (z i j : F')) = 1 ∧ ∀ m, m ≠ i → (Q m).ord x = (N : ℤ) := by
    intro i j
    obtain ⟨x, hx⟩ := exists_forall_ord_sub_eq hQ (fun m ↦ if m = i then (z i j : F') else 0)
      fun m ↦ if m = i then 1 else (N : ℤ)
    exact ⟨x, by simpa using hx i, fun m hm ↦ by simpa [hm] using hx m⟩
  choose w hw hwN using happrox
  have hwmem : ∀ i j, w i j ∈ (Q i).integers := by
    intro i j
    have h1 : (Q i).valuation (w i j - (z i j : F')) ≤ 1 :=
      (Q i).mem_integers_iff.mp ((Q i).mem_integers_iff_ord_nonneg.mpr (by rw [hw i j]; omega))
    have h2 : (Q i).valuation ((z i j : F')) ≤ 1 := (Q i).mem_integers_iff.mp (z i j).2
    have h3 := (Q i).valuation.map_add_le h1 h2
    rw [show w i j - (z i j : F') + (z i j : F') = w i j by ring] at h3
    exact (Q i).mem_integers_iff.mpr h3
  -- Moving the lifts does not change their residues, so they still form a basis.
  have hindres : ∀ i, LinearIndependent ((Q i).restrict k F).ResidueField
      fun j ↦ IsLocalRing.residue (Q i).integers (⟨w i j, hwmem i j⟩ : (Q i).integers) := by
    intro i
    have hwres : ∀ j, IsLocalRing.residue (Q i).integers ⟨w i j, hwmem i j⟩ =
        IsLocalRing.residue (Q i).integers (z i j) := by
      intro j
      have hdord : (Q i).ord (((⟨w i j, hwmem i j⟩ : (Q i).integers) - z i j :
          (Q i).integers) : F') = 1 := hw i j
      have hd0 : (((⟨w i j, hwmem i j⟩ : (Q i).integers) - z i j : (Q i).integers) : F') ≠ 0 := by
        intro h
        rw [h, ord_zero] at hdord
        omega
      have hzero := ((Q i).residue_eq_zero_iff_ord_pos hd0).mpr (by rw [hdord]; omega)
      rwa [map_sub, sub_eq_zero] at hzero
    simpa only [hwres] using hz i
  -- The candidate independent family: `e(Q i ∣ P) · f(Q i ∣ P)` functions for each `i`.
  have hind :=
    linearIndependent_mul_pow_of_forall_linearIndependent_residue k F hQP
      (fun i ↦ by simpa using hτ i i) (fun i m hm ↦ by simp [hτ i m, hm]) hwmem
      (fun i j m hm ↦ by
        rw [hwN i j m hm, hNdef]
        exact_mod_cast ramificationIdx_le_finrank F (Q m)) hindres
  simpa [Fintype.card_sigma, Fintype.card_prod] using hind.fintype_card_le_finrank

/-- **The fundamental inequality** (Stichtenoth, Theorem 3.1.11): the ramification indices and
relative degrees of finitely many distinct places of `F' / k'` lying over one place `P` of
`F / k` satisfy `∑ e(P' ∣ P) · f(P' ∣ P) ≤ [F' : F]`.

The reverse inequality — the fundamental *identity* — is not proved here; it is the affine-model
reconciliation with `Ideal.sum_ramification_inertia`. -/
theorem sum_ramificationIdx_mul_relativeDegree_le_finrank (P : Place k F)
    (s : Finset (Place k' F')) (hs : ∀ P' ∈ s, P'.restrict k F = P) :
    ∑ P' ∈ s, ramificationIdx F P' * relativeDegree k F P' ≤ Module.finrank F F' := by
  have key := sum_relativeDegree_mul_ramificationIdx_le_finrank k F
    (Q := fun P' : {P' // P' ∈ s} ↦ (P' : Place k' F')) Subtype.val_injective
    (P := P) fun P' ↦ hs P' P'.2
  rw [← Finset.sum_coe_sort s fun P' ↦ ramificationIdx F P' * relativeDegree k F P']
  exact le_trans (le_of_eq (Finset.sum_congr rfl fun P' _ ↦ mul_comm _ _)) key

private theorem one_le_ramificationIdx_mul_relativeDegree (P' : Place k' F') :
    1 ≤ ramificationIdx F P' * relativeDegree k F P' := by
  simpa using Nat.mul_le_mul (ramificationIdx_pos F P') (one_le_relativeDegree k F P')

/-- **A place has only finitely many extensions** (Stichtenoth, Proposition 3.1.7): the fibre of
`TauCeti.Place.restrict` over a place of `F / k` is finite, because each of its members
contributes at least `1` to the fundamental inequality. -/
theorem finite_setOf_restrict_eq (P : Place k F) :
    {P' : Place k' F' | P'.restrict k F = P}.Finite := by
  rw [← Set.not_infinite]
  intro hinf
  obtain ⟨t, hts, hcard⟩ := hinf.exists_subset_card_eq (Module.finrank F F' + 1)
  have hle := sum_ramificationIdx_mul_relativeDegree_le_finrank k F P t fun P' hP' ↦ hts hP'
  have hge := Finset.card_nsmul_le_sum t
    (fun P' ↦ ramificationIdx F P' * relativeDegree k F P') 1
    fun P' _ ↦ one_le_ramificationIdx_mul_relativeDegree k F P'
  simp only [smul_eq_mul, mul_one] at hge
  omega

/-- The subtype of places lying over a given place is finite, so a consumer may sum over it. -/
instance finite_restrict_eq (P : Place k F) :
    Finite {P' : Place k' F' // P'.restrict k F = P} :=
  (finite_setOf_restrict_eq k F P).to_subtype

/-- **A place has at most `[F' : F]` extensions** (Stichtenoth, Corollary 3.1.12). -/
theorem ncard_setOf_restrict_eq_le_finrank (P : Place k F) :
    {P' : Place k' F' | P'.restrict k F = P}.ncard ≤ Module.finrank F F' := by
  have hfin := finite_setOf_restrict_eq (k' := k') (F' := F') k F P
  have hle := sum_ramificationIdx_mul_relativeDegree_le_finrank k F P hfin.toFinset
    fun P' hP' ↦ hfin.mem_toFinset.mp hP'
  have hge := Finset.card_nsmul_le_sum hfin.toFinset
    (fun P' ↦ ramificationIdx F P' * relativeDegree k F P') 1
    fun P' _ ↦ one_le_ramificationIdx_mul_relativeDegree k F P'
  simp only [smul_eq_mul, mul_one] at hge
  rw [Set.ncard_eq_toFinset_card _ hfin]
  omega

end Place

end TauCeti
