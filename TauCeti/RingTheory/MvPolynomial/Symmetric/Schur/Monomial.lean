/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Monomial
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric

/-!
# The monomial expansion of a Schur polynomial

The Schur polynomial `s_μ` is a sum of one monomial per semistandard tableau, so its coefficient at
an exponent vector `d` is the Kostka number counting the tableaux of shape `μ` and content `d`
(`TauCeti.coeff_schurPoly`).  That content is a *function* on the alphabet, while the Kostka
numbers `TauCeti.kostkaNumber` are indexed by a *partition*: the two differ by sorting the
exponents into decreasing order.  This file closes that gap and reads off the expansion of a Schur
polynomial in the monomial symmetric polynomials `MvPolynomial.msymm`,

`s_μ = ∑_{ν ⊢ n} K_{μν} m_ν`,

with the Kostka numbers as its coefficients.

The bridge is the symmetry of `s_μ`.  Sorting the exponents of a monomial is a permutation of the
alphabet, and a permutation of the alphabet does not change the coefficients of a symmetric
polynomial, so the coefficient of `s_μ` at an arbitrary exponent vector of total degree `n` is its
coefficient at the sorted one, which `TauCeti.coeff_schurPoly_partWeight` already computes as a
Kostka number.  Concretely, `TauCeti.weightPartition` records the multiset of nonzero exponents of
a monomial, `TauCeti.exists_perm_mapDomain_eq_partWeight` produces the permutation that sorts them,
and `TauCeti.coeff_schurPoly_eq_kostkaNumber` is the resulting coefficient formula.

The sum runs over *all* partitions of `n`, with no bound relating the number of parts of `ν` to the
size of the alphabet: a partition with more parts than the alphabet has letters contributes nothing
because its monomial symmetric polynomial vanishes there (`TauCeti.msymm_eq_zero_of_card_lt`),
exactly as the Schur polynomial itself vanishes for such a shape
(`TauCeti.schurPoly_eq_zero_iff`).

## Main definitions

* `TauCeti.weightSym`: the multiset of letters of a monomial of total degree `n`, as an element of
  `Sym σ n`.
* `TauCeti.weightPartition`: the partition of `n` recording the multiset of nonzero exponents of a
  monomial of total degree `n`.

## Main results

* `TauCeti.exists_perm_mapDomain_eq_partWeight`: a monomial of total degree `n` is a permutation of
  the alphabet away from the sorted monomial `TauCeti.partWeight` of its
  `TauCeti.weightPartition`.
* `TauCeti.coeff_msymm`: a monomial symmetric polynomial has coefficient `1` at the monomials of
  its shape and `0` at every other monomial, and `TauCeti.msymm_eq_zero_of_card_lt`: it vanishes in
  an alphabet with fewer letters than its partition has parts.
* `TauCeti.coeff_schurPoly_eq_kostkaNumber`: **the coefficient of `s_μ` at any monomial of degree
  `n` is a Kostka number**, that of `μ` and the partition of the monomial's exponents.
* `TauCeti.schurPoly_eq_sum_kostkaNumber_smul_msymm`: **the monomial expansion**
  `s_μ = ∑_ν K_{μν} m_ν`, writing a Schur polynomial as the combination of the monomial symmetric
  polynomials whose coefficients are the Kostka numbers.  This is the expansion only: that the two
  families are bases of the symmetric polynomials — which would make the Kostka numbers a genuine
  change-of-basis matrix, as the roadmap target below phrases it — is not proved here, and indeed
  neither family is linearly independent as indexed here, both containing zero terms whenever the
  partition has more parts than the alphabet has letters.

## Implementation notes

One general fact is used and kept `private` here rather than stated for its own sake: that two
families on a finite type taking the same multiset of values differ by a permutation of the index
type.  It is the shape of the sorting argument in this file and has no other consumer yet.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2, where `s_λ = ∑_μ K_{λμ} m_μ` is read off
  the tableau definition.
* R. P. Stanley, *Enumerative Combinatorics*, Volume 2, §7.10.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 7, "the `msymm`-to-`schurPoly` change of basis is the Kostka matrix `Kλμ`".
-/

public section

namespace TauCeti

open Finset MvPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ}

/-! ### Rearranging a family along a permutation -/

omit [DecidableEq σ] in
/-- **Two families on a finite type taking the same multiset of values differ by a permutation** of
the index type: the multiset equality says the fibres are equinumerous, and matching them up is the
permutation. -/
private theorem exists_perm_comp_eq {β : Type*} {f g : σ → β}
    (h : Multiset.map f univ.val = Multiset.map g univ.val) :
    ∃ e : Equiv.Perm σ, g ∘ e = f := by
  classical
  have hcard : ∀ b : β, Fintype.card {x : σ // f x = b} = Fintype.card {x : σ // g x = b} := by
    intro b
    have hb := congrArg (Multiset.count b) h
    rw [Multiset.count_map, Multiset.count_map] at hb
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa only [Finset.card, Finset.filter_val, eq_comm (a := b)] using hb
  exact ⟨Equiv.ofFiberEquiv fun b => Fintype.equivOfCardEq (hcard b),
    funext fun x => Equiv.ofFiberEquiv_map _ x⟩

/-! ### The partition of the exponents of a monomial -/

omit [Fintype σ] [DecidableEq σ] in
/-- The number of letters of the monomial with exponent vector `d` is its total degree.  This is
not a `simp` lemma: `Finsupp.card_toMultiset` already rewrites the left-hand side to
`d.sum fun _ => id`, so tagging it would leave it out of simp-normal form. -/
theorem card_toMultiset_eq_degree (d : σ →₀ ℕ) : Multiset.card d.toMultiset = d.degree := by
  rw [Finsupp.card_toMultiset, Finsupp.degree_apply]
  rfl

/-- **The multiset of letters of a monomial** of total degree `n`, read as an element of
`Sym σ n`: the letter `x` occurs as often as the exponent of `x` prescribes. -/
noncomputable def weightSym (d : σ →₀ ℕ) (h : d.degree = n) : Sym σ n :=
  ⟨d.toMultiset, (card_toMultiset_eq_degree d).trans h⟩

omit [Fintype σ] [DecidableEq σ] in
@[simp]
theorem coe_weightSym (d : σ →₀ ℕ) (h : d.degree = n) :
    (weightSym d h : Multiset σ) = d.toMultiset :=
  (rfl)

/-- **The partition of the exponents of a monomial** of total degree `n`: its parts are the nonzero
exponents, so it is the shape of the monomial once its exponents are sorted decreasingly. -/
noncomputable def weightPartition (d : σ →₀ ℕ) (h : d.degree = n) : n.Partition :=
  Nat.Partition.ofSym (weightSym d h)

omit [Fintype σ] in
/-- The parts of the partition of the exponents of a monomial are the exponents of the letters that
actually occur in it. -/
@[simp]
theorem weightPartition_parts (d : σ →₀ ℕ) (h : d.degree = n) :
    (weightPartition d h).parts = Multiset.map d d.support.val := by
  have hdedup : d.toMultiset.dedup = d.support.val :=
    congrArg Finset.val (Finsupp.toFinset_toMultiset d)
  -- `Nat.Partition.ofSym` is a bare structure instance, carrying no lemma for its `parts` field,
  -- so the only way in is to unfold it (and `weightPartition`) definitionally.
  change d.toMultiset.dedup.map (fun a => Multiset.count a d.toMultiset) = _
  rw [hdedup]
  exact Multiset.map_congr rfl fun a _ => Finsupp.count_toMultiset d a

/-- A monomial has one nonzero exponent per letter occurring in it, so the partition of its
exponents has no more parts than the alphabet has letters. -/
theorem card_parts_weightPartition_le (d : σ →₀ ℕ) (h : d.degree = n) :
    (weightPartition d h).parts.card ≤ Fintype.card σ := by
  rw [weightPartition_parts, Multiset.card_map]
  exact Finset.card_le_univ d.support

/-! ### Sorting the exponents of a monomial -/

omit [DecidableEq σ] in
/-- **The exponents of a monomial**, as a multiset: the exponents of the letters that occur,
together with a zero for each letter that does not. -/
private theorem map_univ_val (d : σ →₀ ℕ) :
    Multiset.map d univ.val
      = Multiset.map d d.support.val
        + Multiset.replicate (Fintype.card σ - d.support.card) 0 := by
  classical
  have hval : (univ : Finset σ).val = d.support.val + d.supportᶜ.val := by
    rw [Finset.compl_eq_univ_sdiff, Finset.sdiff_val,
      add_tsub_cancel_of_le (Finset.val_le_iff.mpr d.support.subset_univ)]
  have hzero : Multiset.map d d.supportᶜ.val
      = Multiset.replicate (Fintype.card σ - d.support.card) 0 := by
    rw [Multiset.map_congr rfl (g := fun _ => (0 : ℕ)) fun x hx =>
      Finsupp.notMem_support_iff.mp (Finset.mem_compl.mp hx), Multiset.map_const']
    exact congrArg (Multiset.replicate · 0) (Finset.card_compl d.support)
  rw [hval, Multiset.map_add, hzero]

omit [DecidableEq σ] in
/-- **The exponents of a sorted monomial**, as a multiset: the parts of the partition, together
with a zero for each letter beyond them.  The hypothesis is what keeps every part inside the
alphabet. -/
private theorem map_univ_val_partWeight (ν : n.Partition)
    (hν : ν.parts.card ≤ Fintype.card σ) :
    Multiset.map (partWeight σ ν) univ.val
      = ν.parts + Multiset.replicate (Fintype.card σ - ν.parts.card) 0 := by
  have hlen : (ν.parts.sort (· ≥ ·)).length = ν.parts.card := Multiset.length_sort _
  have hle : (ν.parts.sort (· ≥ ·)).length ≤ Fintype.card σ := hlen.trans_le hν
  -- The alphabet is indexed by `Fin (Fintype.card σ)`, hence by `List.range (Fintype.card σ)`.
  have hval : Multiset.map (Fin.val : Fin (Fintype.card σ) → ℕ) (univ : Finset _).val
      = Multiset.range (Fintype.card σ) := by
    rw [← Finset.range_val, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_univ, Finset.map_val]
    rfl
  have hreindex : Multiset.map (partWeight σ ν) univ.val
      = ((List.range (Fintype.card σ)).map
          fun i => (ν.parts.sort (· ≥ ·)).getD i 0 : List ℕ) := by
    calc Multiset.map (partWeight σ ν) univ.val
        = Multiset.map ((fun i : ℕ => (ν.parts.sort (· ≥ ·)).getD i 0) ∘
            ((Fin.val : Fin (Fintype.card σ) → ℕ) ∘ (Fintype.equivFin σ))) univ.val :=
          Multiset.map_congr rfl fun x _ => by
            rw [partWeight_apply, rowLen_diagramOf]; rfl
      _ = ((List.range (Fintype.card σ)).map
            fun i => (ν.parts.sort (· ≥ ·)).getD i 0 : List ℕ) := by
          rw [← Multiset.map_map, ← Multiset.map_map, Multiset.map_univ_val_equiv, hval]
          rfl
  -- Sorted decreasingly, the exponents are the parts of `ν` followed by zeros.
  have hlist : ((List.range (Fintype.card σ)).map fun i => (ν.parts.sort (· ≥ ·)).getD i 0)
      = ν.parts.sort (· ≥ ·)
        ++ List.replicate (Fintype.card σ - (ν.parts.sort (· ≥ ·)).length) 0 := by
    refine List.ext_getElem (by simp; omega) fun i h₁ h₂ => ?_
    rw [List.getElem_map, List.getElem_range]
    rcases lt_or_ge i (ν.parts.sort (· ≥ ·)).length with hi | hi
    · rw [List.getElem_append_left hi, List.getD_eq_getElem _ _ hi]
    · rw [List.getElem_append_right hi, List.getElem_replicate,
        List.getD_eq_default _ _ hi]
  rw [hreindex, hlist, ← Multiset.coe_add, Multiset.sort_eq, Multiset.coe_replicate, hlen]

/-- **A monomial of total degree `n` is a rearrangement of the sorted monomial of its shape**: some
permutation of the alphabet carries it to the exponent vector `TauCeti.partWeight` recording the
parts of its `TauCeti.weightPartition`. -/
theorem exists_perm_mapDomain_eq_partWeight (d : σ →₀ ℕ) (h : d.degree = n) :
    ∃ e : Equiv.Perm σ, Finsupp.mapDomain e d = partWeight σ (weightPartition d h) := by
  obtain ⟨e, he⟩ := exists_perm_comp_eq (f := ⇑d) (g := ⇑(partWeight σ (weightPartition d h)))
    (by rw [map_univ_val d, map_univ_val_partWeight _ (card_parts_weightPartition_le d h),
      weightPartition_parts, Multiset.card_map]; rfl)
  refine ⟨e, Finsupp.ext fun y => ?_⟩
  rw [← Finsupp.equivMapDomain_eq_mapDomain (e : σ ≃ σ) d, Finsupp.equivMapDomain_apply]
  have hy := congrFun he (e.symm y)
  rw [Function.comp_apply, Equiv.apply_symm_apply] at hy
  exact hy.symm

/-! ### The coefficients of a monomial symmetric polynomial -/

variable (R : Type*) [CommSemiring R]

/-- **A monomial symmetric polynomial is homogeneous**: it has no monomial whose total degree is
not that of its partition. -/
@[simp]
theorem coeff_msymm_eq_zero_of_degree_ne (ν : n.Partition) {d : σ →₀ ℕ} (h : d.degree ≠ n) :
    coeff d (msymm σ R ν) = 0 := by
  rw [msymm, coeff_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [prod_map_X_eq_monomial, coeff_monomial, ite_eq_right]
  rintro rfl
  exact h (by rw [← card_toMultiset_eq_degree, Multiset.toFinsupp_toMultiset]; exact s.1.2)

/-- **The coefficients of a monomial symmetric polynomial are `0` and `1`**: `m_ν` is the sum of
the monomials of total degree `n` whose nonzero exponents are the parts of `ν`, each occurring
once. -/
@[simp]
theorem coeff_msymm (ν : n.Partition) {d : σ →₀ ℕ} (h : d.degree = n) :
    coeff d (msymm σ R ν) = if weightPartition d h = ν then 1 else 0 := by
  have hinj : ∀ s : Sym σ n, Multiset.toFinsupp (s : Multiset σ) = d ↔ s = weightSym d h :=
    fun s => by rw [Multiset.toFinsupp_eq_iff, ← Sym.coe_inj, coe_weightSym]
  rw [msymm, coeff_sum]
  simp only [prod_map_X_eq_monomial, coeff_monomial]
  by_cases hν : weightPartition d h = ν
  · rw [ite_eq_left hν,
      Finset.sum_eq_single (⟨weightSym d h, hν⟩ : {a : Sym σ n // Nat.Partition.ofSym a = ν})]
    · exact ite_eq_left ((hinj _).mpr rfl)
    · rintro ⟨s, hs⟩ - hne
      exact ite_eq_right fun hcoeff => hne (Subtype.ext ((hinj s).mp hcoeff))
    · exact fun hmem => absurd (Finset.mem_univ _) hmem
  · refine (Finset.sum_eq_zero fun s _ => ite_eq_right fun hcoeff => hν ?_).trans
      (ite_eq_right hν).symm
    -- `weightPartition d h` is `Nat.Partition.ofSym (weightSym d h)` by definition, and `s` ranges
    -- over the multisets of letters whose partition is `ν`.
    exact (congrArg (fun t : Sym σ n => Nat.Partition.ofSym t)
      ((hinj s.1).mp hcoeff)).symm.trans s.2

/-- **A monomial symmetric polynomial vanishes when its partition has more parts than the alphabet
has letters**: no monomial in that alphabet uses that many distinct letters. -/
@[simp]
theorem msymm_eq_zero_of_card_lt (ν : n.Partition) (h : Fintype.card σ < ν.parts.card) :
    msymm σ R ν = 0 := by
  rw [msymm]
  refine Finset.sum_eq_zero fun s _ => absurd h (not_lt.mpr ?_)
  obtain ⟨t, rfl⟩ := s
  exact le_of_eq_of_le (Multiset.card_map _ _) (Finset.card_le_univ (t : Multiset σ).toFinset)

/-! ### The monomial expansion -/

variable (μ : n.Partition)

/-- **The coefficient of a Schur polynomial at any monomial of degree `n` is a Kostka number**:
that of the shape `μ` and the partition of the monomial's exponents.  The exponents need not be
sorted, since sorting them is a permutation of the alphabet, which a symmetric polynomial does not
see. -/
@[simp]
theorem coeff_schurPoly_eq_kostkaNumber {d : σ →₀ ℕ} (h : d.degree = n) :
    coeff d (schurPoly σ R μ) = (kostkaNumber μ (weightPartition d h) : R) := by
  obtain ⟨e, he⟩ := exists_perm_mapDomain_eq_partWeight d h
  have hsymm : coeff (Finsupp.mapDomain e d) (schurPoly σ R μ) = coeff d (schurPoly σ R μ) := by
    conv_lhs => rw [← schurPoly_isSymmetric (R := R) μ e]
    exact coeff_rename_mapDomain _ e.injective _ _
  rw [← hsymm, he, coeff_schurPoly_partWeight μ _
    (by rw [colLen_zero_diagramOf]; exact card_parts_weightPartition_le d h)]

/-- **The monomial expansion of a Schur polynomial**: `s_μ = ∑_ν K_{μν} m_ν`, expanding `s_μ` in
the monomial symmetric polynomials with the Kostka numbers as its coefficients.  The sum runs over
every partition of `n`: those with more parts than the alphabet has letters contribute nothing,
their monomial symmetric polynomial vanishing there.  (Being an expansion, this does not by itself
say that the Kostka numbers are a change-of-basis matrix: no basis result is proved here.) -/
theorem schurPoly_eq_sum_kostkaNumber_smul_msymm :
    schurPoly σ R μ = ∑ ν : n.Partition, (kostkaNumber μ ν : R) • msymm σ R ν := by
  ext d
  rw [coeff_sum]
  simp only [coeff_smul, smul_eq_mul]
  by_cases hd : d.degree = n
  · rw [coeff_schurPoly_eq_kostkaNumber R μ hd, Finset.sum_eq_single (weightPartition d hd)]
    · rw [coeff_msymm R _ hd, ite_eq_left rfl, mul_one]
    · exact fun ν _ hne => by
        rw [coeff_msymm R ν hd, ite_eq_right fun hw => hne hw.symm, mul_zero]
    · exact fun hmem => absurd (Finset.mem_univ _) hmem
  · rw [(isHomogeneous_schurPoly (σ := σ) (R := R) μ).coeff_eq_zero hd]
    exact (Finset.sum_eq_zero fun ν _ => by
      rw [coeff_msymm_eq_zero_of_degree_ne R ν hd, mul_zero]).symm

end TauCeti
