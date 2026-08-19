/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.Combinatorics.Young.Kostka

public section

/-!
# Schur polynomials

The **Schur polynomial** `s_μ` of a Young diagram `μ` in `N` variables is the generating function
of the semistandard Young tableaux of shape `μ` whose entries are drawn from the `N`-letter
alphabet: each such tableau contributes the monomial `∏ᵢ xᵢ ^ (number of cells filled with i)`.
This file defines it, `TauCeti.diagramSchurPoly`, reads off the basic structure that the
definition alone gives, and transports it to the partition-indexed Schur polynomial
`TauCeti.schurPoly` in an arbitrary finite alphabet.

The tableaux summed over are the bounded ones, `TauCeti.BoundedSSYT`: Mathlib's
`SemistandardYoungTableau μ` fills cells with arbitrary natural numbers, and it is the bound that
makes the sum finite. The alphabet is `0, 1, …, N - 1` rather than the classical `1, …, N`,
matching `SemistandardYoungTableau.content`.

The load-bearing statement is `TauCeti.coeff_diagramSchurPoly`: the coefficient of a monomial
`x^d` in `s_μ` is the image in the coefficient semiring of the Kostka number `K_{μ d}`, the number
of semistandard tableaux of shape `μ` and content `d`. Every other result here is read off it
together with the Kostka theory of `TauCeti.Combinatorics.Young.Kostka`:

* `TauCeti.diagramSchurPoly_eq_zero_iff`: `s_μ` vanishes exactly when `μ` is taller than the
  alphabet, since columns are strict and the entry in row `i` is at least `i`.
* `TauCeti.coeff_diagramSchurPoly_rowLenWeight`: the coefficient at the exponent recording the row
  lengths of `μ` is `1`, the highest-weight tableau being the unique one of that content.
* `TauCeti.coeff_diagramSchurPoly_diagramOf_eq_zero_of_not_dominates`: for partitions, the
  exponent recording the parts of `ν` occurs in `s_μ` only if `μ` dominates `ν`. Together with the
  previous item this is the triangularity of the Schur polynomials against the dominance order,
  and `TauCeti.coeff_diagramSchurPoly_eq_zero_of_sum_lt` is the partial-sum form it comes from.
* `TauCeti.isHomogeneous_diagramSchurPoly`: `s_μ` is homogeneous of degree the number of cells of
  `μ`, every tableau of shape `μ` having that many entries.

An arbitrary finite alphabet `σ` is ordered by `Fintype.equivFin σ`, and `TauCeti.schurPoly σ R μ`
is `TauCeti.diagramSchurPoly` renamed along that ordering. The result does not depend on the
ordering, but that is the symmetry of `s_μ`, which is *not* proved here: it is the Bender-Knuth
involution, and it lives downstream in
`TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric`.  None of the results below need it.

## Main definitions

* `TauCeti.BoundedSSYT.weight`: the content of a bounded tableau, packaged as an exponent vector
  on the alphabet.
* `TauCeti.diagramSchurPoly`: the Schur polynomial of a Young diagram in the alphabet `Fin N`.
* `TauCeti.rowLenWeight`: the exponent vector recording the row lengths of a shape, the exponent
  of the monomial contributed by the highest-weight tableau.
* `TauCeti.schurPoly`: the Schur polynomial of a partition in a finite alphabet.
* `TauCeti.partWeight`: the exponent vector on a finite alphabet recording the parts of a
  partition.

## Main results

* `TauCeti.coeff_diagramSchurPoly`: the coefficients of a Schur polynomial are the images of the
  Kostka numbers, `TauCeti.coeff_schurPoly` is its form in an arbitrary finite alphabet, and
  `TauCeti.coeff_schurPoly_partWeight` reads it at the exponent of a partition.
* `TauCeti.eval_diagramSchurPoly`: evaluating a Schur polynomial sums the monomials of its
  tableaux.
* `TauCeti.diagramSchurPoly_eq_zero_iff` and `TauCeti.schurPoly_eq_zero_iff`: a Schur polynomial
  vanishes exactly for a shape taller than its alphabet.
* `TauCeti.isHomogeneous_diagramSchurPoly` and `TauCeti.isHomogeneous_schurPoly`: a Schur
  polynomial is homogeneous of degree the number of cells of its shape.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 5.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 7.
-/

namespace TauCeti

open Finset MvPolynomial

namespace BoundedSSYT

variable {N : ℕ} {μ : YoungDiagram}

/-- The letters a bounded tableau uses all come from the alphabet, so its content is supported on
the image of `Fin N`. -/
private theorem support_content_subset_range (T : BoundedSSYT N μ) :
    ↑(SemistandardYoungTableau.content T.1).support ⊆ Set.range (Fin.val : Fin N → ℕ) := by
  intro x hx
  simp only [Finset.mem_coe, SemistandardYoungTableau.support_content, Finset.mem_image] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  exact ⟨⟨_, entry_lt T ((YoungDiagram.mem_cells _).mp hc)⟩, rfl⟩

/-- The **weight** of a bounded tableau: its content, read as an exponent vector indexed by the
alphabet `Fin N`. This is the exponent of the monomial the tableau contributes to
`TauCeti.diagramSchurPoly`. -/
noncomputable def weight (T : BoundedSSYT N μ) : Fin N →₀ ℕ :=
  Finsupp.comapDomain Fin.val (SemistandardYoungTableau.content T.1) Fin.val_injective.injOn

@[simp]
theorem weight_apply (T : BoundedSSYT N μ) (i : Fin N) :
    weight T i = SemistandardYoungTableau.content T.1 i :=
  Finsupp.comapDomain_apply _ _ _ _

/-- Extending the weight of a bounded tableau by zero recovers its content: no letter outside the
alphabet occurs. -/
theorem mapDomain_weight (T : BoundedSSYT N μ) :
    Finsupp.mapDomain Fin.val (weight T) = SemistandardYoungTableau.content T.1 :=
  Finsupp.mapDomain_comapDomain _ Fin.val_injective _ (support_content_subset_range T)

/-- The sum of the weight of a bounded tableau of shape `μ` is the number of cells of `μ`: every
cell carries exactly one letter. -/
theorem sum_weight (T : BoundedSSYT N μ) : ∑ i, weight T i = μ.card := by
  simp only [weight_apply]
  rw [Fin.sum_univ_eq_sum_range fun i => SemistandardYoungTableau.content T.1 i]
  exact SemistandardYoungTableau.sum_content_eq_card fun c hc =>
    entry_lt T ((YoungDiagram.mem_cells _).mp hc)

/-- **Boundedness is not an extra condition on a content extended by zero**: a letter outside the
alphabet would have to occur in the content, where the extension puts a zero. -/
private theorem lt_of_content_eq {T : _root_.SemistandardYoungTableau μ} {d : Fin N →₀ ℕ}
    (h : ⇑(SemistandardYoungTableau.content T) = ⇑(Finsupp.mapDomain Fin.val d))
    {i c : ℕ} (hic : (i, c) ∈ μ) : T i c < N := by
  by_contra hlt
  have hmem : SemistandardYoungTableau.content T (T i c) ≠ 0 := by
    rw [← Finsupp.mem_support_iff, SemistandardYoungTableau.support_content]
    exact Finset.mem_image.mpr ⟨(i, c), (YoungDiagram.mem_cells _).mpr hic, rfl⟩
  refine hmem ((congrFun h (T i c)).trans (Finsupp.mapDomain_of_notMem_range _ _ ?_))
  rintro ⟨y, hy⟩
  exact hlt (hy ▸ y.isLt)

/-- The weight of a bounded tableau whose content is an exponent vector extended by zero is that
exponent vector. -/
private theorem weight_eq_of_content_eq (T : BoundedSSYT N μ) {d : Fin N →₀ ℕ}
    (h : ⇑(SemistandardYoungTableau.content T.1) = ⇑(Finsupp.mapDomain Fin.val d)) :
    weight T = d := by
  ext i
  rw [weight_apply, congrFun h i, Finsupp.mapDomain_apply Fin.val_injective]

/-- **The bounded tableaux of a given weight are the tableaux of the corresponding content.**
Boundedness is not an extra condition on the right-hand side: a letter outside the alphabet would
have to occur in the content, where the extension by zero puts a zero. -/
private noncomputable def weightFiberEquivContentFiber (N : ℕ) (μ : YoungDiagram)
    (d : Fin N →₀ ℕ) :
    {T : BoundedSSYT N μ // weight T = d} ≃
      {T : _root_.SemistandardYoungTableau μ //
        ⇑(SemistandardYoungTableau.content T) = ⇑(Finsupp.mapDomain Fin.val d)} where
  toFun T := ⟨T.1.1, by rw [← mapDomain_weight T.1, T.2]⟩
  invFun T := ⟨⟨T.1, fun _ _ hic => lt_of_content_eq T.2 hic⟩, weight_eq_of_content_eq _ T.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The number of bounded tableaux of a given weight is a Kostka number. -/
theorem card_weight_eq (d : Fin N →₀ ℕ) :
    Nat.card {T : BoundedSSYT N μ // weight T = d}
      = diagramKostkaNumber μ (Finsupp.mapDomain Fin.val d) :=
  (Nat.card_congr (weightFiberEquivContentFiber N μ d)).trans (diagramKostkaNumber_def _ _).symm

end BoundedSSYT

variable (N : ℕ) (R : Type*) [CommSemiring R] (μ : YoungDiagram)

/-- **The Schur polynomial** `s_μ` of a Young diagram `μ` in the `N` variables `x₀, …, x_{N-1}`:
the generating function of the semistandard Young tableaux of shape `μ` in the alphabet
`{0, …, N - 1}`, each contributing the monomial `∏ᵢ xᵢ ^ (number of cells filled with i)`. -/
noncomputable def diagramSchurPoly : MvPolynomial (Fin N) R :=
  ∑ T : BoundedSSYT N μ, monomial (BoundedSSYT.weight T) 1

/-- The defining sum of a Schur polynomial, one weight monomial per bounded tableau of the
shape.  `TauCeti.diagramSchurPoly` is public, but its *body* is not exposed — this file's
`public section` carries no `@[expose]` — so no equation lemma for it reaches a downstream module;
this restatement is what such a module rewrites with. -/
theorem diagramSchurPoly_eq_sum :
    diagramSchurPoly N R μ = ∑ T : BoundedSSYT N μ, monomial (BoundedSSYT.weight T) 1 :=
  (rfl)

variable {N R μ}

/-- **The coefficients of a Schur polynomial are the Kostka numbers**: the coefficient of `x^d` in
`s_μ` is the image in `R` of the number of semistandard tableaux of shape `μ` whose content
is `d`. -/
theorem coeff_diagramSchurPoly (d : Fin N →₀ ℕ) :
    coeff d (diagramSchurPoly N R μ)
      = (diagramKostkaNumber μ (Finsupp.mapDomain Fin.val d) : R) := by
  classical
  rw [diagramSchurPoly, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_boole, ← BoundedSSYT.card_weight_eq d, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

/-- **A Schur polynomial is the generating function of its tableaux**, in the literal sense: at any
family of values it is the sum, over the bounded tableaux of its shape, of the product of the
values raised to the multiplicities of the corresponding letters. -/
theorem eval_diagramSchurPoly (y : Fin N → R) :
    eval y (diagramSchurPoly N R μ)
      = ∑ T : BoundedSSYT N μ, ∏ i, y i ^ BoundedSSYT.weight T i := by
  rw [diagramSchurPoly, map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [eval_monomial, one_mul]
  exact Finsupp.prod_fintype _ _ fun _ => pow_zero _

/-- Scalars pass through a Schur polynomial: every coefficient is the cast of a natural number,
namely of a Kostka number, and casts of natural numbers are preserved by semiring homomorphisms. -/
theorem map_diagramSchurPoly {S : Type*} [CommSemiring S] (f : R →+* S) :
    MvPolynomial.map f (diagramSchurPoly N R μ) = diagramSchurPoly N S μ := by
  ext d
  rw [coeff_map, coeff_diagramSchurPoly, coeff_diagramSchurPoly, map_natCast]

/-- **A Schur polynomial of a shape taller than its alphabet vanishes**, there being no tableau to
sum over. -/
theorem diagramSchurPoly_eq_zero_of_lt_colLen (h : N < μ.colLen 0) :
    diagramSchurPoly N R μ = 0 := by
  have := BoundedSSYT.isEmpty_of_lt_colLen h
  simp [diagramSchurPoly]

/-- **The Schur polynomial of the empty shape is `1`**, the empty tableau contributing the empty
monomial. -/
@[simp]
theorem diagramSchurPoly_bot : diagramSchurPoly N R (⊥ : YoungDiagram) = 1 := by
  have hw : BoundedSSYT.weight (default : BoundedSSYT N (⊥ : YoungDiagram)) = 0 := by
    ext i
    rw [BoundedSSYT.weight_apply, Finsupp.coe_zero, Pi.zero_apply,
      SemistandardYoungTableau.content_apply]
    simp
  rw [diagramSchurPoly, Finset.univ_unique, Finset.sum_singleton, hw, monomial_zero']
  exact map_one C

variable (N μ)

/-- The exponent vector on the alphabet `Fin N` recording the row lengths of `μ`: the content of
the highest-weight tableau of shape `μ`, and the exponent of the monomial it contributes to
`TauCeti.diagramSchurPoly`. -/
noncomputable def rowLenWeight : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i : Fin N => μ.rowLen i

@[simp]
theorem rowLenWeight_apply (i : Fin N) : rowLenWeight N μ i = μ.rowLen i :=
  (rfl)

variable {N μ}

/-- Extending the row lengths of a shape no taller than the alphabet by zero recovers them. -/
theorem mapDomain_rowLenWeight (h : μ.colLen 0 ≤ N) :
    ⇑(Finsupp.mapDomain Fin.val (rowLenWeight N μ)) = μ.rowLen := by
  funext j
  by_cases hj : j < N
  · exact Finsupp.mapDomain_apply Fin.val_injective _ (⟨j, hj⟩ : Fin N)
  · have hzero : μ.rowLen j = 0 := by
      by_contra hne
      exact hj (lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.mp
        (YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne))) h)
    rw [hzero]
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨y, hy⟩
    exact hj (hy ▸ y.isLt)

/-- For a shape taller than the alphabet the row-length exponent records only the rows the
alphabet reaches, so its degree falls short of the number of cells. -/
private theorem degree_rowLenWeight_lt (h : N < μ.colLen 0) :
    (rowLenWeight N μ).degree < μ.card := by
  rw [Finsupp.degree_eq_sum]
  simp only [rowLenWeight_apply]
  rw [Fin.sum_univ_eq_sum_range fun i => μ.rowLen i,
    YoungDiagram.sum_range_rowLen_eq_card_filter_fst]
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
    ⟨(N, 0), (YoungDiagram.mem_cells _).mpr (YoungDiagram.mem_iff_lt_colLen.mpr h), ?_⟩)
  simp

/-- **The coefficient of a Schur polynomial at the row lengths of its shape is `1`**: the
highest-weight tableau, whose `i`-th row consists of `i`s, is the unique tableau of shape `μ`
whose content is the row lengths of `μ`. -/
theorem coeff_diagramSchurPoly_rowLenWeight (h : μ.colLen 0 ≤ N) :
    coeff (rowLenWeight N μ) (diagramSchurPoly N R μ) = 1 := by
  rw [coeff_diagramSchurPoly, mapDomain_rowLenWeight h, diagramKostkaNumber_rowLen, Nat.cast_one]

/-- **A Schur polynomial of a shape no taller than its alphabet is nonzero.** -/
theorem diagramSchurPoly_ne_zero [Nontrivial R] (h : μ.colLen 0 ≤ N) :
    diagramSchurPoly N R μ ≠ 0 := by
  intro hz
  have h1 := coeff_diagramSchurPoly_rowLenWeight (R := R) h
  rw [hz, coeff_zero] at h1
  exact zero_ne_one h1

/-- **A Schur polynomial vanishes exactly for a shape taller than its alphabet.** -/
theorem diagramSchurPoly_eq_zero_iff [Nontrivial R] :
    diagramSchurPoly N R μ = 0 ↔ N < μ.colLen 0 :=
  ⟨fun h => not_le.mp fun hle => diagramSchurPoly_ne_zero hle h,
    diagramSchurPoly_eq_zero_of_lt_colLen⟩

/-- **Triangularity of the Schur polynomials**: an exponent whose partial sums overshoot those of
the row lengths of `μ` does not occur in `s_μ`. For partitions this is the vanishing of `s_μ`
outside the dominance order, `TauCeti.kostkaNumber_eq_zero_of_not_dominates`. -/
theorem coeff_diagramSchurPoly_eq_zero_of_sum_lt {d : Fin N →₀ ℕ} {k : ℕ}
    (h : (μ.rowLens.take k).sum < ∑ i ∈ Finset.range k, Finsupp.mapDomain Fin.val d i) :
    coeff d (diagramSchurPoly N R μ) = 0 := by
  have hzero : diagramKostkaNumber μ (Finsupp.mapDomain Fin.val d) = 0 := by
    by_contra hne
    exact absurd (sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero hne k) (not_le.mpr h)
  rw [coeff_diagramSchurPoly, hzero, Nat.cast_zero]

/-- **A Schur polynomial is homogeneous** of degree the number of cells of its shape: a tableau of
shape `μ` has one entry per cell. -/
theorem isHomogeneous_diagramSchurPoly : (diagramSchurPoly N R μ).IsHomogeneous μ.card :=
  IsHomogeneous.sum _ _ _ fun T _ =>
    isHomogeneous_monomial _ ((Finsupp.degree_eq_sum _).trans (BoundedSSYT.sum_weight T))

/-- The total degree of a nonzero Schur polynomial is the number of cells of its shape. -/
theorem totalDegree_diagramSchurPoly [Nontrivial R] (h : μ.colLen 0 ≤ N) :
    (diagramSchurPoly N R μ).totalDegree = μ.card :=
  isHomogeneous_diagramSchurPoly.totalDegree (diagramSchurPoly_ne_zero h)

section Partition

variable {n : ℕ} (μ ν : n.Partition)

/-- **The coefficients of a Schur polynomial are the Kostka numbers of partitions**: the
coefficient of `s_μ` at the exponent recording the parts of `ν` is the image in `R` of `K_{μν}`.
The row bound is what makes the exponent record all of `ν`: an alphabet shorter than the number of
parts of `ν` would truncate it. -/
theorem coeff_diagramSchurPoly_diagramOf (h : (diagramOf ν).colLen 0 ≤ N) :
    coeff (rowLenWeight N (diagramOf ν)) (diagramSchurPoly N R (diagramOf μ))
      = (kostkaNumber μ ν : R) := by
  rw [coeff_diagramSchurPoly, mapDomain_rowLenWeight h, kostkaNumber_def]

/-- **The Schur polynomials are triangular for the dominance order**: the exponent recording the
parts of `ν` occurs in `s_μ` only if `μ` dominates `ν`. No row bound is needed: an alphabet too
short to record all of `ν` truncates the exponent to one of degree less than `n`, where `s_μ`
vanishes by homogeneity. -/
theorem coeff_diagramSchurPoly_diagramOf_eq_zero_of_not_dominates (hd : ¬ Dominates μ ν) :
    coeff (rowLenWeight N (diagramOf ν)) (diagramSchurPoly N R (diagramOf μ)) = 0 := by
  rcases le_or_gt ((diagramOf ν).colLen 0) N with h | h
  · rw [coeff_diagramSchurPoly_diagramOf μ ν h, kostkaNumber_eq_zero_of_not_dominates hd,
      Nat.cast_zero]
  · refine isHomogeneous_diagramSchurPoly.coeff_eq_zero ?_
    rw [card_diagramOf]
    exact ((degree_rowLenWeight_lt h).trans_eq (card_diagramOf ν)).ne

end Partition

section Alphabet

variable {σ : Type*} [Fintype σ] {n : ℕ}

/-- **The Schur polynomial** `s_μ` of a partition `μ` in the finite alphabet `σ`: the Schur
polynomial `TauCeti.diagramSchurPoly` of the Young diagram of `μ` in the alphabet
`Fin (Fintype.card σ)`, renamed along the ordering `Fintype.equivFin σ` of `σ`. The ordering does
not matter, `s_μ` being symmetric (`TauCeti.schurPoly_isSymmetric`, proved downstream). -/
noncomputable def schurPoly (σ : Type*) [Fintype σ] (R : Type*) [CommSemiring R] {n : ℕ}
    (μ : n.Partition) : MvPolynomial σ R :=
  rename (Fintype.equivFin σ).symm (diagramSchurPoly (Fintype.card σ) R (diagramOf μ))

/-- The Schur polynomial of a partition is the Schur polynomial of its Young diagram, renamed
along the chosen ordering of the alphabet.  As for `TauCeti.diagramSchurPoly_eq_sum`, the body of
`TauCeti.schurPoly` is not exposed outside this module, so this restatement is what a downstream
module rewrites with. -/
theorem schurPoly_eq_rename (μ : n.Partition) :
    schurPoly σ R μ
      = rename (Fintype.equivFin σ).symm (diagramSchurPoly (Fintype.card σ) R (diagramOf μ)) :=
  (rfl)

/-- The exponent vector on the alphabet `σ` recording the parts of `ν`, read through the ordering
`Fintype.equivFin σ`: the image of `TauCeti.rowLenWeight` of the Young diagram of `ν`. -/
noncomputable def partWeight (σ : Type*) [Fintype σ] {n : ℕ} (ν : n.Partition) : σ →₀ ℕ :=
  Finsupp.mapDomain (Fintype.equivFin σ).symm (rowLenWeight (Fintype.card σ) (diagramOf ν))

@[simp]
theorem partWeight_apply (ν : n.Partition) (x : σ) :
    partWeight σ ν x = (diagramOf ν).rowLen (Fintype.equivFin σ x) := by
  conv_lhs => rw [partWeight, ← (Fintype.equivFin σ).symm_apply_apply x]
  rw [Finsupp.mapDomain_apply (Fintype.equivFin σ).symm.injective, rowLenWeight_apply]

variable (μ ν : n.Partition)

/-- **The coefficients of a Schur polynomial in a finite alphabet are the Kostka numbers**: at the
exponent obtained from `d` by the ordering of the alphabet, the coefficient of `s_μ` is the image
in `R` of the Kostka number of `μ` and the content that `d` extends to by zero. -/
theorem coeff_schurPoly_mapDomain (d : Fin (Fintype.card σ) →₀ ℕ) :
    coeff (Finsupp.mapDomain (Fintype.equivFin σ).symm d) (schurPoly σ R μ)
      = (diagramKostkaNumber (diagramOf μ) (Finsupp.mapDomain Fin.val d) : R) := by
  rw [schurPoly, coeff_rename_mapDomain _ (Fintype.equivFin σ).symm.injective,
    coeff_diagramSchurPoly]

/-- **The coefficients of a Schur polynomial in a finite alphabet are the Kostka numbers**: the
coefficient of `s_μ` at an arbitrary exponent `d` is the image in `R` of the Kostka number of `μ`
and the content obtained from `d` by numbering the alphabet with `Fintype.equivFin`. -/
theorem coeff_schurPoly (d : σ →₀ ℕ) :
    coeff d (schurPoly σ R μ)
      = (diagramKostkaNumber (diagramOf μ)
          (Finsupp.mapDomain (fun x => (Fintype.equivFin σ x : ℕ)) d) : R) := by
  have hd : Finsupp.mapDomain (Fintype.equivFin σ).symm
      (Finsupp.mapDomain (Fintype.equivFin σ) d) = d := by
    rw [← Finsupp.mapDomain_comp]
    simp
  conv_lhs => rw [← hd]
  rw [coeff_schurPoly_mapDomain, ← Finsupp.mapDomain_comp]
  rfl

/-- **The coefficient of a Schur polynomial at a partition is a Kostka number**: the coefficient
of `s_μ` at the exponent recording the parts of `ν` is the image in `R` of `K_{μν}`. The row bound
is what makes the exponent record all of `ν`: an alphabet with fewer letters than `ν` has parts
would truncate the record. -/
theorem coeff_schurPoly_partWeight (h : (diagramOf ν).colLen 0 ≤ Fintype.card σ) :
    coeff (partWeight σ ν) (schurPoly σ R μ) = (kostkaNumber μ ν : R) := by
  rw [partWeight, coeff_schurPoly_mapDomain, mapDomain_rowLenWeight h, kostkaNumber_def]

/-- **The Schur polynomials are triangular for the dominance order**: the exponent recording the
parts of `ν` occurs in `s_μ` only if `μ` dominates `ν`. No row bound is needed: an alphabet too
short to record all of `ν` truncates the exponent to one of degree less than `n`, where `s_μ`
vanishes by homogeneity. -/
theorem coeff_schurPoly_partWeight_eq_zero_of_not_dominates (hd : ¬ Dominates μ ν) :
    coeff (partWeight σ ν) (schurPoly σ R μ) = 0 := by
  rw [partWeight, schurPoly, coeff_rename_mapDomain _ (Fintype.equivFin σ).symm.injective]
  exact coeff_diagramSchurPoly_diagramOf_eq_zero_of_not_dominates μ ν hd

/-- Scalars pass through a Schur polynomial: every coefficient is the cast of a natural number,
namely of a Kostka number, and casts of natural numbers are preserved by semiring homomorphisms. -/
theorem map_schurPoly {S : Type*} [CommSemiring S] (f : R →+* S) :
    MvPolynomial.map f (schurPoly σ R μ) = schurPoly σ S μ := by
  rw [schurPoly, schurPoly, map_rename, map_diagramSchurPoly]

/-- **The Schur polynomial of the partition of `0` is `1`**, its Young diagram being empty and the
empty tableau contributing the empty monomial. -/
@[simp]
theorem schurPoly_partition_zero (p : Nat.Partition 0) : schurPoly σ R p = 1 := by
  have hbot : diagramOf p = ⊥ :=
    YoungDiagram.ext ((Finset.card_eq_zero.mp (card_diagramOf p)).trans
      YoungDiagram.cells_bot.symm)
  rw [schurPoly, hbot, diagramSchurPoly_bot, map_one]

/-- **A Schur polynomial vanishes exactly for a partition with more parts than the alphabet has
letters.** -/
theorem schurPoly_eq_zero_iff [Nontrivial R] :
    schurPoly σ R μ = 0 ↔ Fintype.card σ < (diagramOf μ).colLen 0 := by
  rw [schurPoly, map_eq_zero_iff _ (rename_injective _ (Fintype.equivFin σ).symm.injective),
    diagramSchurPoly_eq_zero_iff]

/-- **A Schur polynomial is homogeneous** of degree the natural number its partition partitions: a
tableau of that shape has one entry per cell. -/
theorem isHomogeneous_schurPoly : (schurPoly σ R μ).IsHomogeneous n := by
  have h := isHomogeneous_diagramSchurPoly (N := Fintype.card σ) (R := R) (μ := diagramOf μ)
  rw [card_diagramOf μ] at h
  rw [schurPoly]
  exact h.rename_isHomogeneous

end Alphabet

end TauCeti
