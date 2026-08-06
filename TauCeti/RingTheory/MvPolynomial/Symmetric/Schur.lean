/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.Combinatorics.Young.Kostka

public section

/-!
# Schur polynomials

The **Schur polynomial** `s_μ` of a Young diagram `μ` in `N` variables is the generating function
of the semistandard Young tableaux of shape `μ` whose entries are drawn from the `N`-letter
alphabet: each such tableau contributes the monomial `∏ᵢ xᵢ ^ (number of cells filled with i)`.
This file defines it, `TauCeti.schurPoly`, and reads off the basic structure that the definition
alone gives.

Mathlib's `SemistandardYoungTableau μ` fills cells with arbitrary natural numbers, so the alphabet
is cut out here as a subtype, `TauCeti.BoundedSSYT`, of the tableaux whose entries are smaller
than `N`; the alphabet is `0, 1, …, N - 1` rather than the classical `1, …, N`, matching
`TauCeti.SemistandardYoungTableau.content`. That subtype is finite
(`TauCeti.finite_ssyt_lt`), which is what makes the generating function a polynomial.

The load-bearing statement is `TauCeti.coeff_schurPoly`: the coefficient of a monomial `x^d` in
`s_μ` is the Kostka number `K_{μ d}`, the number of tableaux of shape `μ` and content `d`. Every
other result here is read off it together with the Kostka theory of
`TauCeti.Combinatorics.Young.Kostka`:

* `TauCeti.schurPoly_eq_zero_iff`: `s_μ` vanishes exactly when `μ` is taller than the alphabet,
  since columns are strict and the entry in row `i` is at least `i`.
* `TauCeti.coeff_schurPoly_rowLenWeight`: the coefficient at the exponent recording the row
  lengths of `μ` is `1`, the highest-weight tableau being the unique one of that content.
* `TauCeti.coeff_schurPoly_diagramOf_eq_zero_of_not_dominates`: for partitions, the exponent
  recording the parts of `ν` occurs in `s_μ` only if `μ` dominates `ν`. Together with the previous
  item this is the triangularity of the Schur polynomials against the dominance order, and
  `TauCeti.coeff_schurPoly_eq_zero_of_sum_lt` is the partial-sum form it comes from.
* `TauCeti.isHomogeneous_schurPoly`: `s_μ` is homogeneous of degree the number of cells of `μ`,
  every tableau of shape `μ` having that many entries.

Symmetry of `s_μ` is *not* proved here: it is the Bender-Knuth involution, a separate target of
the Schur-Weyl roadmap, and none of the results below need it.

## Main definitions

* `TauCeti.BoundedSSYT`: the semistandard Young tableaux of a given shape whose entries lie below
  a given bound.
* `TauCeti.BoundedSSYT.weight`: the content of such a tableau, packaged as an exponent vector on
  the alphabet.
* `TauCeti.schurPoly`: the Schur polynomial of a Young diagram in a finite alphabet.
* `TauCeti.rowLenWeight`: the exponent vector recording the row lengths of a shape, the leading
  exponent of its Schur polynomial.

## Main results

* `TauCeti.coeff_schurPoly`: the coefficients of a Schur polynomial are the Kostka numbers, and
  `TauCeti.coeff_schurPoly_diagramOf` is its partition-indexed form.
* `TauCeti.schurPoly_eq_zero_iff`: a Schur polynomial vanishes exactly for a shape taller than
  its alphabet.
* `TauCeti.isHomogeneous_schurPoly`: a Schur polynomial is homogeneous of degree the number of
  cells of its shape.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 5.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 7.
-/

namespace TauCeti

open Finset MvPolynomial

/-- The semistandard Young tableaux of shape `μ` written in the alphabet `{0, …, N - 1}`, that is,
those all of whose entries are smaller than `N`. Mathlib's `SemistandardYoungTableau μ` allows
arbitrary natural-number entries and is infinite for a nonempty `μ`; bounding the alphabet is what
makes the generating function `TauCeti.schurPoly` a polynomial. -/
abbrev BoundedSSYT (N : ℕ) (μ : YoungDiagram) : Type :=
  {T : _root_.SemistandardYoungTableau μ // ∀ i c : ℕ, (i, c) ∈ μ → T i c < N}

instance (N : ℕ) (μ : YoungDiagram) : Finite (BoundedSSYT N μ) := finite_ssyt_lt N μ

noncomputable instance (N : ℕ) (μ : YoungDiagram) : Fintype (BoundedSSYT N μ) := .ofFinite _

namespace BoundedSSYT

variable {N : ℕ} {μ : YoungDiagram}

/-- The entries of a tableau written in the alphabet `{0, …, N - 1}` all use letters of that
alphabet. -/
theorem entry_lt (T : BoundedSSYT N μ) {i c : ℕ} (h : (i, c) ∈ μ) : T.1 i c < N :=
  T.2 i c h

/-- The letters a bounded tableau uses all come from the alphabet, so its content is supported on
the image of `Fin N`. -/
theorem support_content_subset_range (T : BoundedSSYT N μ) :
    ↑(SemistandardYoungTableau.content T.1).support ⊆ Set.range (Fin.val : Fin N → ℕ) := by
  intro x hx
  simp only [Finset.mem_coe, SemistandardYoungTableau.support_content, Finset.mem_image] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  exact ⟨⟨_, entry_lt T ((YoungDiagram.mem_cells _).mp hc)⟩, rfl⟩

/-- The **weight** of a bounded tableau: its content, read as an exponent vector indexed by the
alphabet `Fin N`. This is the exponent of the monomial the tableau contributes to
`TauCeti.schurPoly`. -/
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
theorem lt_of_content_eq {T : _root_.SemistandardYoungTableau μ} {d : Fin N →₀ ℕ}
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
theorem weight_eq_of_content_eq (T : BoundedSSYT N μ) {d : Fin N →₀ ℕ}
    (h : ⇑(SemistandardYoungTableau.content T.1) = ⇑(Finsupp.mapDomain Fin.val d)) :
    weight T = d := by
  ext i
  rw [weight_apply, congrFun h i, Finsupp.mapDomain_apply Fin.val_injective]

/-- **The bounded tableaux of a given weight are the tableaux of the corresponding content.**
Boundedness is not an extra condition on the right-hand side, by
`TauCeti.BoundedSSYT.lt_of_content_eq`. -/
noncomputable def weightEquiv (N : ℕ) (μ : YoungDiagram) (d : Fin N →₀ ℕ) :
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
  (Nat.card_congr (weightEquiv N μ d)).trans (diagramKostkaNumber_def _ _).symm

/-- **A shape taller than its alphabet admits no tableau**: entries increase strictly down a
column, so a column of more than `N` cells cannot be filled from an `N`-letter alphabet. -/
theorem isEmpty_of_lt_colLen (h : N < μ.colLen 0) : IsEmpty (BoundedSSYT N μ) := by
  refine ⟨fun T => absurd (entry_lt T (YoungDiagram.mem_iff_lt_colLen.mpr h)) (not_lt.mpr ?_)⟩
  exact SemistandardYoungTableau.le_entry T.1 (YoungDiagram.mem_iff_lt_colLen.mpr h)

/-- The empty shape has a unique tableau, the empty one. -/
instance (N : ℕ) : Unique (BoundedSSYT N (⊥ : YoungDiagram)) where
  default := ⟨_root_.SemistandardYoungTableau.highestWeight ⊥, fun _ _ hic => absurd hic (by simp)⟩
  uniq T := Subtype.ext <| _root_.SemistandardYoungTableau.ext fun _ _ => by
    rw [T.1.zeros (by simp), _root_.SemistandardYoungTableau.highestWeight_apply, if_neg (by simp)]

end BoundedSSYT

variable (N : ℕ) (R : Type*) [CommSemiring R] (μ : YoungDiagram)

/-- **The Schur polynomial** `s_μ` of a Young diagram `μ` in the `N` variables `x₀, …, x_{N-1}`:
the generating function of the semistandard Young tableaux of shape `μ` in the alphabet
`{0, …, N - 1}`, each contributing the monomial `∏ᵢ xᵢ ^ (number of cells filled with i)`. -/
noncomputable def schurPoly : MvPolynomial (Fin N) R :=
  ∑ T : BoundedSSYT N μ, monomial (BoundedSSYT.weight T) 1

variable {N R μ}

/-- **The coefficients of a Schur polynomial are the Kostka numbers**: the coefficient of `x^d` in
`s_μ` counts the semistandard tableaux of shape `μ` whose content is `d`. -/
theorem coeff_schurPoly (d : Fin N →₀ ℕ) :
    coeff d (schurPoly N R μ) = (diagramKostkaNumber μ (Finsupp.mapDomain Fin.val d) : R) := by
  classical
  rw [schurPoly, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_boole, ← BoundedSSYT.card_weight_eq d, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

/-- Scalars pass through a Schur polynomial: its coefficients are natural numbers, so it is the
image of the integral one under any ring homomorphism. -/
theorem map_schurPoly {S : Type*} [CommSemiring S] (f : R →+* S) :
    MvPolynomial.map f (schurPoly N R μ) = schurPoly N S μ := by
  ext d
  rw [coeff_map, coeff_schurPoly, coeff_schurPoly, map_natCast]

/-- **A Schur polynomial of a shape taller than its alphabet vanishes**, there being no tableau to
sum over. -/
theorem schurPoly_eq_zero_of_lt_colLen (h : N < μ.colLen 0) : schurPoly N R μ = 0 := by
  have := BoundedSSYT.isEmpty_of_lt_colLen h
  simp [schurPoly]

/-- **The Schur polynomial of the empty shape is `1`**, the empty tableau contributing the empty
monomial. -/
@[simp]
theorem schurPoly_bot : schurPoly N R (⊥ : YoungDiagram) = 1 := by
  have hw : BoundedSSYT.weight (default : BoundedSSYT N (⊥ : YoungDiagram)) = 0 := by
    ext i
    rw [BoundedSSYT.weight_apply, Finsupp.coe_zero, Pi.zero_apply,
      SemistandardYoungTableau.content_apply]
    simp
  rw [schurPoly, Finset.univ_unique, Finset.sum_singleton, hw, monomial_zero']
  exact map_one C

variable (N μ)

/-- The exponent vector on the alphabet `Fin N` recording the row lengths of `μ`: the content of
the highest-weight tableau of shape `μ`, and the leading exponent of `TauCeti.schurPoly`. -/
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

/-- **The leading coefficient of a Schur polynomial is `1`**: the highest-weight tableau, whose
`i`-th row consists of `i`s, is the unique tableau of shape `μ` whose content is the row lengths
of `μ`. -/
theorem coeff_schurPoly_rowLenWeight (h : μ.colLen 0 ≤ N) :
    coeff (rowLenWeight N μ) (schurPoly N R μ) = 1 := by
  rw [coeff_schurPoly, mapDomain_rowLenWeight h, diagramKostkaNumber_rowLen, Nat.cast_one]

/-- **A Schur polynomial of a shape no taller than its alphabet is nonzero.** -/
theorem schurPoly_ne_zero [Nontrivial R] (h : μ.colLen 0 ≤ N) : schurPoly N R μ ≠ 0 := by
  intro hz
  have h1 := coeff_schurPoly_rowLenWeight (R := R) h
  rw [hz, coeff_zero] at h1
  exact zero_ne_one h1

/-- **A Schur polynomial vanishes exactly for a shape taller than its alphabet.** -/
theorem schurPoly_eq_zero_iff [Nontrivial R] : schurPoly N R μ = 0 ↔ N < μ.colLen 0 :=
  ⟨fun h => not_le.mp fun hle => schurPoly_ne_zero hle h, schurPoly_eq_zero_of_lt_colLen⟩

/-- **Triangularity of the Schur polynomials**: an exponent whose partial sums overshoot those of
the row lengths of `μ` does not occur in `s_μ`. For partitions this is the vanishing of `s_μ`
outside the dominance order, `TauCeti.kostkaNumber_eq_zero_of_not_dominates`. -/
theorem coeff_schurPoly_eq_zero_of_sum_lt {d : Fin N →₀ ℕ} {k : ℕ}
    (h : (μ.rowLens.take k).sum < ∑ i ∈ Finset.range k, Finsupp.mapDomain Fin.val d i) :
    coeff d (schurPoly N R μ) = 0 := by
  have hzero : diagramKostkaNumber μ (Finsupp.mapDomain Fin.val d) = 0 := by
    by_contra hne
    exact absurd (sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero hne k) (not_le.mpr h)
  rw [coeff_schurPoly, hzero, Nat.cast_zero]

/-- **A Schur polynomial is homogeneous** of degree the number of cells of its shape: a tableau of
shape `μ` has one entry per cell. -/
theorem isHomogeneous_schurPoly : (schurPoly N R μ).IsHomogeneous μ.card :=
  IsHomogeneous.sum _ _ _ fun T _ =>
    isHomogeneous_monomial _ ((Finsupp.degree_eq_sum _).trans (BoundedSSYT.sum_weight T))

/-- The total degree of a nonzero Schur polynomial is the number of cells of its shape. -/
theorem totalDegree_schurPoly [Nontrivial R] (h : μ.colLen 0 ≤ N) :
    (schurPoly N R μ).totalDegree = μ.card :=
  isHomogeneous_schurPoly.totalDegree (schurPoly_ne_zero h)

section Partition

variable {n : ℕ} (μ ν : n.Partition)

/-- **The coefficients of a Schur polynomial are the Kostka numbers of partitions**: the
coefficient of `s_μ` at the exponent recording the parts of `ν` is `K_{μν}`. The row bound is
what makes the exponent record all of `ν`: an alphabet shorter than the number of parts of `ν`
would truncate it. -/
theorem coeff_schurPoly_diagramOf (h : (diagramOf ν).colLen 0 ≤ N) :
    coeff (rowLenWeight N (diagramOf ν)) (schurPoly N R (diagramOf μ))
      = (kostkaNumber μ ν : R) := by
  rw [coeff_schurPoly, mapDomain_rowLenWeight h, kostkaNumber_def]

/-- **The Schur polynomials are triangular for the dominance order**: the exponent recording the
parts of `ν` occurs in `s_μ` only if `μ` dominates `ν`. -/
theorem coeff_schurPoly_diagramOf_eq_zero_of_not_dominates (h : (diagramOf ν).colLen 0 ≤ N)
    (hd : ¬ Dominates μ ν) :
    coeff (rowLenWeight N (diagramOf ν)) (schurPoly N R (diagramOf μ)) = 0 := by
  rw [coeff_schurPoly_diagramOf μ ν h, kostkaNumber_eq_zero_of_not_dominates hd, Nat.cast_zero]

end Partition

end TauCeti
