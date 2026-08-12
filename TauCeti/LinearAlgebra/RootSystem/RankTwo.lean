/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.G2
public import TauCeti.LinearAlgebra.RootSystem.Classification
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit

public section

/-!
# The Cartan-Killing classification in rank at most two

The classification of finite-type Cartan matrices proceeds by induction on the number of nodes, and
its base cases are the diagrams with one and with two nodes. This file settles them: an
indecomposable finite-type matrix on two indices is, after a single simultaneous relabelling of its
rows and columns, exactly one of the three standard rank-two Cartan matrices `A₂`, `B₂`, `G₂`, and
on one index it is `A₁`.

Producing the type turns on one invariant. The **Cartan product** `AᵢⱼAⱼᵢ` of the two nodes is
unchanged by relabelling, is at least `1` because the diagram is connected, and is at most `3`
because the matrix is of finite type (`TauCeti.IsFiniteType.apply_mul_apply_mem_of_ne`). Its three
possible values `1`, `2`, `3` separate the three types, and each value pins the pair of off-diagonal
entries to `(-1, -1)`, to `(-1, -2)` and to `(-1, -3)` respectively. What is left to the
relabelling is then only the *orientation* of the multiple edge, which is what
`TauCeti.HasCartanType` records and why the equivalence produced below is not always the one the
ambient indexing suggests. That the type so produced is the only valid one is not proved here: it is
`TauCeti.DynkinType.eq_of_valid_of_forall_eq`, which says that of any rank.

Two remarks on what the statements say. First, `C 2` is absent from the list, and must be: it is the
transpose of `B 2` and names the same root system, so `TauCeti.DynkinType.Valid` keeps only the name
`B 2` (see `TauCeti.hasCartanType_dual_iff_of_rank_le_two`). Uniqueness of the type would be false
without that exclusion. Second, connectedness is a genuine hypothesis at the matrix level, and is
supplied by irreducibility at the root-system level through
`TauCeti.cartanMatrix_ne_zero_of_card_support_eq_two`: a matrix whose two nodes are orthogonal is
the Cartan matrix of `A₁ × A₁`, of finite type but not irreducible.

## Main results

* `TauCeti.DynkinType.valid_and_rank_eq_two_iff`: the valid Dynkin types of rank two are exactly
  `A 2`, `B 2` and `G2`.
* `TauCeti.IsFiniteType.existsUnique_dynkinType_of_card_eq_two`: **an indecomposable finite-type
  matrix on two indices has exactly one valid Dynkin type.**
* `TauCeti.cartanMatrix_ne_zero_of_card_support_eq_two`: the Cartan matrix of a base of an
  irreducible reduced pairing with two simple roots has no off-diagonal zero entry.
* `TauCeti.existsUnique_dynkinType_of_card_support_eq_two`: **an irreducible reduced
  crystallographic finite root system with two simple roots is of exactly one of the types `A₂`,
  `B₂`, `G₂`**; `TauCeti.hasCartanType_of_card_support_eq_two` is the same statement as a three-way
  disjunction.
* `TauCeti.isG2_of_hasCartanType_G2`: a base of type `G₂` makes its pairing Mathlib's
  `RootPairing.IsG2`.
* `TauCeti.hasCartanType_G2_of_isG2`: **conversely, a base of an `IsG2` pairing is of type `G₂`**,
  so the two conditions agree (`TauCeti.hasCartanType_G2_iff_isG2`). This is the direction that
  needs the roots away from the base, and it closes the recognition step that Mathlib's `G₂` file
  lists as a TODO.
* `TauCeti.existsUnique_dynkinType_of_card_support_eq_one`: the rank-one case, which turns on the
  diagonal entry `2` alone and so needs neither finiteness, finite type nor irreducibility.

## References

This file supplies the rank-one and rank-two cases of the Layer 5 milestone "the classification of
finite-type Cartan matrices" of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, whose
statement `existsUnique_dynkinType` these theorems specialize. See Bourbaki, *Lie Groups and Lie
Algebras, Chapters 4-6*, Ch. VI §4, and Humphreys, *Introduction to Lie Algebras and Representation
Theory*, §11.1, where the rank-two diagrams are enumerated first for exactly this reason.
-/

open scoped Matrix

namespace TauCeti

namespace DynkinType

/-- **The valid Dynkin types of rank two are `A₂`, `B₂` and `G₂`.** The type `C 2` is excluded by
`TauCeti.DynkinType.Valid`, being `B 2` transposed; every other type either has a different rank or
fails validity at rank two. -/
@[simp]
theorem valid_and_rank_eq_two_iff {t : DynkinType} :
    t.Valid ∧ t.rank = 2 ↔ t = .A 2 ∨ t = .B 2 ∨ t = .G2 := by
  constructor
  · rintro ⟨hv, hr⟩
    cases t with
    | A n => rw [rank_A] at hr; subst hr; exact Or.inl rfl
    | B n => rw [rank_B] at hr; subst hr; exact Or.inr (Or.inl rfl)
    | C n => rw [rank_C] at hr; subst hr; exact absurd (valid_C.mp hv) (by omega)
    | D n => rw [rank_D] at hr; subst hr; exact absurd (valid_D.mp hv) (by omega)
    | G2 => exact Or.inr (Or.inr rfl)
    | _ => simp at hr
  · rintro (rfl | rfl | rfl) <;> exact ⟨by simp, rfl⟩

/-- The standard Cartan matrix of type `A₂`. -/
theorem cartanMatrix_A_two_eq : (A 2).cartanMatrix = !![2, -1; -1, 2] := by
  ext i j
  rw [cartanMatrix_A]
  fin_cases i <;> fin_cases j <;> simp [CartanMatrix.A]

/-- The standard Cartan matrix of type `B₂`: the arrow of the double edge runs from the long simple
root at Bourbaki node `1` to the short simple root at node `2`. -/
theorem cartanMatrix_B_two_eq : (B 2).cartanMatrix = !![2, -2; -1, 2] := by
  ext i j
  rw [cartanMatrix_B]
  fin_cases i <;> fin_cases j <;> simp [CartanMatrix.B]

/-- The standard Cartan matrix of type `G₂` in the Bourbaki numbering, node `1` short and node `2`
long. -/
theorem cartanMatrix_G2_eq : G2.cartanMatrix = !![2, -1; -3, 2] := by
  ext i j
  rw [cartanMatrix_G2]
  fin_cases i <;> fin_cases j <;> simp [CartanMatrix.G₂]

end DynkinType

/-! ### The classification of matrices on at most two indices -/

/-- **Entrywise agreement with a two-node matrix is four equations, and two of them are automatic.**
The two diagonal equations follow from the two matrices having constant diagonal `2`, so only the
two off-diagonal entries have to be matched by hand. Like
`TauCeti.existsUnique_dynkinType_of_card_eq_one`, this takes the diagonal equation itself rather
than `TauCeti.IsFiniteType`, which is what the root-system-level callers have available. -/
private theorem forall_eq_of_apply_offDiag {B : Type*} {A : Matrix B B ℤ}
    {C : Matrix (Fin 2) (Fin 2) ℤ} (hA : ∀ i, A i i = 2) (e : B ≃ Fin 2) (hC : ∀ i, C i i = 2)
    (h01 : A (e.symm 0) (e.symm 1) = C 0 1) (h10 : A (e.symm 1) (e.symm 0) = C 1 0) (i j : B) :
    A i j = C (e i) (e j) := by
  suffices key : ∀ i j : Fin 2, A (e.symm i) (e.symm j) = C i j by simpa using key (e i) (e j)
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using (hA _).trans (hC 0).symm
  · simpa using h01
  · simpa using h10
  · simpa using (hA _).trans (hC 1).symm

private theorem exists_equiv_fin_two_apply_eq {B : Type*} [Fintype B]
    (hcard : Fintype.card B = 2) {x y : B} (hxy : x ≠ y) :
    ∃ e : B ≃ Fin 2, e x = 0 ∧ e y = 1 := by
  let e₀ : B ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  let e : B ≃ Fin 2 := e₀.trans (Equiv.swap (e₀ x) 0)
  have hx : e x = 0 := by simp [e]
  refine ⟨e, hx, Fin.eq_one_of_ne_zero _ fun hy ↦ ?_⟩
  exact hxy (e.injective (hx.trans hy.symm))

namespace Matrix

variable {B : Type*} {A : Matrix B B ℤ}

/-- **The Cartan product is the invariant of a two-node diagram.** A relabelling matching `A` with
`C` carries the product of the two off-diagonal entries of `A` to that of `C`, whichever way round
it sends the two indices, because the product is symmetric. -/
theorem mul_apply_mul_apply_eq_of_equiv_fin_two {C : Matrix (Fin 2) (Fin 2) ℤ} (e : B ≃ Fin 2)
    (he : ∀ i j, A i j = C (e i) (e j)) {x y : B} (hxy : x ≠ y) :
    A x y * A y x = C 0 1 * C 1 0 := by
  have hne : e x ≠ e y := fun hc ↦ hxy (e.injective hc)
  rw [he x y, he y x]
  revert hne
  generalize e x = a
  generalize e y = b
  intro hne
  fin_cases a <;> fin_cases b <;> simp_all [mul_comm]

end Matrix

namespace IsFiniteType

variable {B : Type*} [Fintype B] {A : Matrix B B ℤ}

/-- **Two integers at most `-1` satisfy `ac + a + c + 1 ≥ 0`,** being `(a + 1)(c + 1) ≥ 0` expanded.
Applied to the two off-diagonal entries of a connected finite-type matrix on two indices, it bounds
their sum below by the negative of the Cartan product minus two, which together with the value of
that product pins both entries. -/
private theorem zero_le_mul_add_add_add {a c : ℤ} (ha : a ≤ -1) (hc : c ≤ -1) :
    0 ≤ a * c + a + c + 1 := by
  have hmul : 0 ≤ (a + 1) * (c + 1) := mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  nlinarith [hmul]

/-- **The rank-two classification of finite-type matrices.** A finite-type matrix on two indices
whose off-diagonal entries are nonzero — that is, whose diagram is connected — has exactly one
valid Dynkin type: it is `A₂`, `B₂` or `G₂` according as the Cartan product of its two nodes is
`1`, `2` or `3`. -/
theorem existsUnique_dynkinType_of_card_eq_two (h : IsFiniteType A) (hcard : Fintype.card B = 2)
    (hconn : ∀ i j : B, i ≠ j → A i j ≠ 0) :
    ∃! t : DynkinType, t.Valid ∧
      ∃ e : B ≃ Fin t.rank, ∀ i j, A i j = t.cartanMatrix (e i) (e j) := by
  classical
  set e₀ : B ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  set x := e₀.symm 0 with hx
  set y := e₀.symm 1 with hy
  have hxy : x ≠ y := fun hc ↦ by simpa using e₀.symm.injective hc
  have hxy0 : A x y ≤ -1 := by
    have := h.apply_le_zero_of_ne hxy
    have := hconn x y hxy
    omega
  have hyx0 : A y x ≤ -1 := by
    have := h.apply_le_zero_of_ne hxy.symm
    have := hconn y x hxy.symm
    omega
  have hsum := zero_le_mul_add_add_add hxy0 hyx0
  have hprod : 1 ≤ A x y * A y x := h.one_le_apply_mul_apply (hconn x y hxy)
  have hmem := h.apply_mul_apply_mem_of_ne hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  -- The relabelling that reverses the two nodes, used when the multiple edge points the other way.
  set e₁ : B ≃ Fin 2 := e₀.trans (Equiv.swap 0 1) with he₁
  have he₁0 : e₁.symm 0 = y := by simp [he₁, hy]
  have he₁1 : e₁.symm 1 = x := by simp [he₁, hx]
  -- Existence: the Cartan product names the type, and its two entries orient the edge.
  have hex : ∃ t : DynkinType, (t = .A 2 ∨ t = .B 2 ∨ t = .G2) ∧
      ∃ e : B ≃ Fin t.rank, ∀ i j, A i j = t.cartanMatrix (e i) (e j) := by
    have hcases : A x y * A y x = 1 ∨ A x y * A y x = 2 ∨ A x y * A y x = 3 := by omega
    rcases hcases with hp | hp | hp
    · rw [hp] at hsum
      refine ⟨.A 2, Or.inl rfl, e₀, ?_⟩
      have h01 : A x y = -1 := by omega
      have h10 : A y x = -1 := by omega
      rw [DynkinType.cartanMatrix_A_two_eq]
      exact forall_eq_of_apply_offDiag h.apply_self e₀ (by decide) (by rw [← hx, ← hy, h01]; decide)
        (by rw [← hx, ← hy, h10]; decide)
    · rw [hp] at hsum
      have hchoice : A x y = -1 ∨ A x y = -2 := by omega
      rcases hchoice with hc | hc
      · -- The short root is at `x`, so the relabelling has to reverse the two nodes.
        have h10 : A y x = -2 := by rw [hc] at hp; omega
        refine ⟨.B 2, Or.inr (Or.inl rfl), e₁, ?_⟩
        rw [DynkinType.cartanMatrix_B_two_eq]
        exact forall_eq_of_apply_offDiag h.apply_self e₁ (by decide)
          (by rw [he₁0, he₁1, h10]; decide) (by rw [he₁0, he₁1, hc]; decide)
      · have h10 : A y x = -1 := by rw [hc] at hp; omega
        refine ⟨.B 2, Or.inr (Or.inl rfl), e₀, ?_⟩
        rw [DynkinType.cartanMatrix_B_two_eq]
        exact forall_eq_of_apply_offDiag h.apply_self e₀ (by decide)
          (by rw [← hx, ← hy, hc]; decide) (by rw [← hx, ← hy, h10]; decide)
    · rw [hp] at hsum
      have hchoice : A x y = -1 ∨ A x y = -2 ∨ A x y = -3 := by omega
      rcases hchoice with hc | hc | hc
      · have h10 : A y x = -3 := by rw [hc] at hp; omega
        refine ⟨.G2, Or.inr (Or.inr rfl), e₀, ?_⟩
        rw [DynkinType.cartanMatrix_G2_eq]
        exact forall_eq_of_apply_offDiag h.apply_self e₀ (by decide)
          (by rw [← hx, ← hy, hc]; decide) (by rw [← hx, ← hy, h10]; decide)
      · exact absurd hp (by rw [hc]; omega)
      · -- The short root is at `y`, so the relabelling has to reverse the two nodes.
        have h10 : A y x = -1 := by rw [hc] at hp; omega
        refine ⟨.G2, Or.inr (Or.inr rfl), e₁, ?_⟩
        rw [DynkinType.cartanMatrix_G2_eq]
        exact forall_eq_of_apply_offDiag h.apply_self e₁ (by decide)
          (by rw [he₁0, he₁1, h10]; decide) (by rw [he₁0, he₁1, hc]; decide)
  -- Uniqueness is the general fact that a matrix has at most one valid Dynkin type.
  obtain ⟨t, ht, et, het⟩ := hex
  have htv : t.Valid := by rcases ht with rfl | rfl | rfl <;> simp
  exact ⟨t, ⟨htv, et, het⟩, fun s ⟨hsv, es, hes⟩ ↦
    DynkinType.eq_of_valid_of_forall_eq hsv htv es et hes het⟩

end IsFiniteType

/-- **A matrix on one index with diagonal entry `2` is `A₁`.** Only that entry is in play, so the
hypothesis is the diagonal equation itself rather than `TauCeti.IsFiniteType`: neither the
finite-type inequalities nor connectedness are used. -/
theorem existsUnique_dynkinType_of_card_eq_one {B : Type*} [Fintype B] {A : Matrix B B ℤ}
    (hdiag : ∀ i, A i i = 2) (hcard : Fintype.card B = 1) :
    ∃! t : DynkinType, t.Valid ∧
      ∃ e : B ≃ Fin t.rank, ∀ i j, A i j = t.cartanMatrix (e i) (e j) := by
  have hsub : Subsingleton B := Fintype.card_le_one_iff_subsingleton.mp hcard.le
  obtain ⟨e₀, he₀⟩ : ∃ e : B ≃ Fin (DynkinType.A 1).rank,
      ∀ i j, A i j = (DynkinType.A 1).cartanMatrix (e i) (e j) := by
    refine ⟨Fintype.equivFinOfCardEq hcard, fun i j ↦ ?_⟩
    rw [Subsingleton.elim i j, DynkinType.cartanMatrix_apply_same, hdiag]
  -- Uniqueness is the general fact that a matrix has at most one valid Dynkin type.
  exact ⟨.A 1, ⟨by simp, e₀, he₀⟩, fun s ⟨hsv, es, hes⟩ ↦
    DynkinType.eq_of_valid_of_forall_eq hsv (by simp) es e₀ hes he₀⟩

/-! ### The classification of root systems of rank at most two -/

section RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic]

/-- **A rank-two irreducible diagram is connected.** With only two simple roots, irreducibility
leaves no room for the diagram to split: the single off-diagonal pair of Cartan entries cannot
vanish. This is the hypothesis that `TauCeti.IsFiniteType.existsUnique_dynkinType_of_card_eq_two`
asks for, and the reason `A₁ × A₁` is not a counterexample to the classification. -/
theorem cartanMatrix_ne_zero_of_card_support_eq_two [Finite ι] [CharZero R] [IsDomain R]
    [P.IsReduced] [P.IsIrreducible] (b : P.Base)
    (hb : b.support.card = 2) {i j : b.support} (hij : i ≠ j) :
    b.cartanMatrix i j ≠ 0 := by
  classical
  intro hzero
  -- Every index is `i` or `j`, so the indices reachable from `j` form the singleton `{j}`;
  -- irreducibility makes every index reachable, so `i = j`.
  have hcard : Fintype.card b.support = 2 := by simpa using hb
  obtain ⟨e, hei, hej⟩ := exists_equiv_fin_two_apply_eq hcard hij
  have hmem (k : b.support) : k = i ∨ k = j := by
    have h2 : ∀ m : Fin 2, m = 0 ∨ m = 1 := by decide
    rcases h2 (e k) with hk | hk
    · exact Or.inl (e.injective (hk.trans hei.symm))
    · exact Or.inr (e.injective (hk.trans hej.symm))
  have hreach : ∀ k : b.support, k = j := fun k ↦
    b.induction_on_cartanMatrix (p := fun m ↦ m = j) (i := j) (j := k) rfl (by
      rintro u v rfl huv
      rcases hmem v with rfl | rfl
      · exact absurd hzero huv
      · rfl)
  exact hij ((hreach i).trans (hreach j).symm)

/-- **A root system with two simple roots is of type `A₂`, `B₂` or `G₂`, and of exactly one of
them.** This is the rank-two case of the Cartan-Killing classification: existence and uniqueness of
a valid Dynkin type for an irreducible reduced crystallographic finite root system. -/
theorem existsUnique_dynkinType_of_card_support_eq_two [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] [P.IsReduced] [P.IsIrreducible] (b : P.Base) (hb : b.support.card = 2) :
    ∃! t : DynkinType, t.Valid ∧ HasCartanType P b t := by
  simp only [hasCartanType_iff]
  exact (isFiniteType_cartanMatrix b).existsUnique_dynkinType_of_card_eq_two (by simpa using hb)
    fun i j hij ↦ cartanMatrix_ne_zero_of_card_support_eq_two b hb hij

/-- **The rank-two classification, as a three-way disjunction.** -/
theorem hasCartanType_of_card_support_eq_two [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] [P.IsReduced] [P.IsIrreducible] (b : P.Base) (hb : b.support.card = 2) :
    HasCartanType P b (.A 2) ∨ HasCartanType P b (.B 2) ∨ HasCartanType P b .G2 := by
  obtain ⟨t, ⟨htv, ht⟩, -⟩ := existsUnique_dynkinType_of_card_support_eq_two b hb
  have hrank : t.rank = 2 := by simpa [hb] using ht.card_support.symm
  rcases DynkinType.valid_and_rank_eq_two_iff.mp ⟨htv, hrank⟩ with rfl | rfl | rfl
  · exact Or.inl ht
  · exact Or.inr (Or.inl ht)
  · exact Or.inr (Or.inr ht)

/-- **A base of Cartan type `G₂` makes its root pairing Mathlib's `RootPairing.IsG2`.** The entry
`-3` of the standard `G₂` Cartan matrix is the pairing of two simple roots, which is exactly the
datum `RootPairing.IsG2` asks for; `RootPairing.IsG2.card_base_support_eq_two` is the matching fact
that an `IsG2` pairing has a rank-two base. `TauCeti.hasCartanType_G2_of_isG2` is the converse, and
needs more: excluding type `A₂` turns on the pairings of *all* roots, not only the simple ones. -/
theorem isG2_of_hasCartanType_G2 [P.IsReduced] [P.IsIrreducible] {b : P.Base}
    (h : HasCartanType P b .G2) : P.IsG2 := by
  obtain ⟨e, he⟩ : ∃ e : b.support ≃ Fin 2, ∀ i j,
      b.cartanMatrix i j = (!![2, -1; -3, 2] : Matrix (Fin 2) (Fin 2) ℤ) (e i) (e j) := by
    obtain ⟨e, he⟩ := (hasCartanType_iff b .G2).mp h
    exact ⟨e, fun i j ↦ by rw [he i j, DynkinType.cartanMatrix_G2_eq]; rfl⟩
  refine (RootPairing.isG2_iff P).mpr ⟨e.symm 1, e.symm 0, ?_⟩
  have hentry := he (e.symm 1) (e.symm 0)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hentry
  simpa [RootPairing.Base.cartanMatrixIn_def] using hentry

/-- **An `IsG2` root pairing has Cartan type `G₂`.** This is the converse of
`TauCeti.isG2_of_hasCartanType_G2`, and it is the harder direction, because `RootPairing.IsG2` asks
only that *some* pair of roots pair to `-3`, while the conclusion is about the two simple roots of
the given base.

The bridge is root length. A pair of roots pairing to `-3` has its transposed pairing `-1`, so the
two differ in squared length by the factor `3`; every root has the length of a simple root
(`TauCeti.RootPairing.RootPositiveForm.exists_mem_support_rootLength_eq`), so two of the simple
roots already differ by that factor, and reading the ratio back off the Cartan matrix makes their
two off-diagonal entries `-3` and `-1`. Since the base has two elements, these entries and the
diagonal entries `2` identify its Cartan matrix with the standard matrix of `G₂`. -/
theorem hasCartanType_G2_of_isG2 [Finite ι] [CharZero R] [IsDomain R]
    (hG2 : P.IsG2) (b : P.Base) : HasCartanType P b .G2 := by
  classical
  have _i : Fintype ι := Fintype.ofFinite ι
  have hcard : b.support.card = 2 := RootPairing.IsG2.card_base_support_eq_two b
  set Bf := P.posRootForm ℤ
  have _iEmbeddedG2 : P.EmbeddedG2 := RootPairing.IsG2.toEmbeddedG2 P
  have hkl := RootPairing.EmbeddedG2.pairingIn_long_short (P := P)
  have hlk := RootPairing.EmbeddedG2.pairingIn_short_long (P := P)
  -- So the two differ in squared length by the factor three.
  have hkl_len : Bf.rootLength (RootPairing.EmbeddedG2.long P) =
      3 * Bf.rootLength (RootPairing.EmbeddedG2.short P) := by
    have hswap := Bf.pairingIn_mul_eq_pairingIn_mul_swap
      (RootPairing.EmbeddedG2.long P) (RootPairing.EmbeddedG2.short P)
    rw [hkl, hlk] at hswap
    omega
  -- Every root has the length of a simple root, so two simple roots already differ by that factor.
  obtain ⟨p, hp, hpk⟩ := RootPairing.RootPositiveForm.exists_mem_support_rootLength_eq Bf b
    (RootPairing.EmbeddedG2.long P)
  obtain ⟨q, hq, hql⟩ := RootPairing.RootPositiveForm.exists_mem_support_rootLength_eq Bf b
    (RootPairing.EmbeddedG2.short P)
  have hpos : 0 < Bf.rootLength q := Bf.rootLength_pos q
  have hlen : Bf.rootLength p = 3 * Bf.rootLength q := by omega
  have hpq : p ≠ q := by rintro rfl; omega
  have hne : (⟨p, hp⟩ : b.support) ≠ ⟨q, hq⟩ := fun hc ↦ hpq (congrArg Subtype.val hc)
  -- Reading the ratio back off the Cartan matrix makes the two pairings `-3` and `-1`.
  have hratio : P.pairingIn ℤ p q = 3 * P.pairingIn ℤ q p := by
    have hswap := Bf.pairingIn_mul_eq_pairingIn_mul_swap p q
    rw [hlen] at hswap
    refine (mul_right_cancel₀ hpos.ne' ?_).symm
    rw [← hswap]; ring
  have hnz : P.pairingIn ℤ q p ≠ 0 := by
    have hzero := cartanMatrix_ne_zero_of_card_support_eq_two b hcard hne.symm
    simpa only [RootPairing.Base.cartanMatrixIn_def] using hzero
  have hqp : P.pairingIn ℤ q p = -1 := by
    have hmem := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed p q
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    have hunit : P.pairingIn ℤ q p = 1 ∨ P.pairingIn ℤ q p = -1 := by omega
    rcases hunit with h1 | h1
    · have hnonpos := b.cartanMatrix_le_zero_of_ne ⟨q, hq⟩ ⟨p, hp⟩ hne.symm
      simp only [RootPairing.Base.cartanMatrixIn_def] at hnonpos
      omega
    · exact h1
  have hpq' : P.pairingIn ℤ p q = -3 := by rw [hratio, hqp]; norm_num
  -- The two chosen simple roots exhaust the base, and their order gives the standard `G₂` matrix.
  let p' : b.support := ⟨p, hp⟩
  let q' : b.support := ⟨q, hq⟩
  have hcard' : Fintype.card b.support = 2 := by simp [hcard]
  -- Relabel so that the short root `q'` sits at node `0` and the long root `p'` at node `1`, the
  -- Bourbaki orientation of the standard `G₂` matrix.
  obtain ⟨e, heq, hep⟩ := exists_equiv_fin_two_apply_eq hcard' hne.symm
  have hsymm0 : e.symm 0 = q' := by rw [← heq, Equiv.symm_apply_apply]
  have hsymm1 : e.symm 1 = p' := by rw [← hep, Equiv.symm_apply_apply]
  -- Only the two off-diagonal entries are left to match, the diagonal being constant `2`.
  rw [hasCartanType_iff]
  refine ⟨e, fun i j ↦ ?_⟩
  rw [DynkinType.cartanMatrix_G2_eq]
  refine forall_eq_of_apply_offDiag b.cartanMatrix_apply_same e (by decide) ?_ ?_ i j
  · -- Expose the Cartan entry as `pairingIn`, the form in which `hqp` is stated.
    rw [hsymm0, hsymm1]
    calc
      b.cartanMatrix q' p' = P.pairingIn ℤ q p := RootPairing.Base.cartanMatrixIn_def _ _ _ _
      _ = _ := by rw [hqp]; decide
  · -- Expose the Cartan entry as `pairingIn`, the form in which `hpq'` is stated.
    rw [hsymm0, hsymm1]
    calc
      b.cartanMatrix p' q' = P.pairingIn ℤ p q := RootPairing.Base.cartanMatrixIn_def _ _ _ _
      _ = _ := by rw [hpq']; decide

/-- **Cartan type `G₂` and Mathlib's `RootPairing.IsG2` are the same condition.** The right-hand
side does not mention the base, so an irreducible reduced crystallographic finite root pairing with
one base of type `G₂` has every base of type `G₂`. The `IsG2` hypothesis of
`TauCeti.hasCartanType_G2_of_isG2` is taken as an argument rather than as an instance, so that it
can be supplied by the right-hand side here. -/
@[simp] theorem hasCartanType_G2_iff_isG2 [Finite ι] [CharZero R] [IsDomain R]
    [P.IsReduced] [P.IsIrreducible] (b : P.Base) :
    HasCartanType P b .G2 ↔ P.IsG2 :=
  ⟨isG2_of_hasCartanType_G2, fun h ↦ hasCartanType_G2_of_isG2 h b⟩

/-- **A pairing with a single simple root is of type `A₁`.** Neither finiteness nor irreducibility
is needed, nor even that the pairing is a root system: the Cartan matrix is the `1 × 1` matrix `[2]`
by `RootPairing.Base.cartanMatrix_apply_same`, which is all the rank-one classification consumes. -/
theorem existsUnique_dynkinType_of_card_support_eq_one [CharZero R] (b : P.Base)
    (hb : b.support.card = 1) :
    ∃! t : DynkinType, t.Valid ∧ HasCartanType P b t := by
  simp only [hasCartanType_iff]
  exact existsUnique_dynkinType_of_card_eq_one b.cartanMatrix_apply_same (by simpa using hb)

end RootPairing

end TauCeti
