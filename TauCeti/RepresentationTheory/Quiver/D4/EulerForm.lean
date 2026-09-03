/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.D4.Basic
public import TauCeti.RepresentationTheory.Quiver.EulerForm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The Euler and Tits forms of the `D₄` quiver

This file evaluates the Euler and Tits forms of the `D₄` quiver in the coordinates of its four
vertices and reads off their positive roots. Writing `c` for the value at the centre and `aᵢ` for
the values at the three outer vertices,

* `titsForm d = c ^ 2 + ∑ᵢ aᵢ ^ 2 - c * ∑ᵢ aᵢ`, and four times it is the sum of squares
  `c ^ 2 + ∑ᵢ (2 aᵢ - c) ^ 2`, so the form is **positive definite**: `D₄` is a Dynkin quiver;
* consequently a dimension vector `d ≥ 0` of Tits norm one has `c ≤ 2`, and the **nonnegative**
  vectors of Tits norm one are exactly **twelve** in number -- the three outer simple roots, the
  eight vectors with a `1` at the centre and an arbitrary `0/1` pattern outside (`s = ∅` being the
  central simple root), and the highest root `(1,1,1;2)`.

Twelve is the number of positive roots of the root system `D₄`, so this is the standard check that
the positive-root count of a quiver is correct beyond type `A`, where
`TauCeti.Quiver.Kronecker.EulerForm` already tests it.

## Main definitions

* `TauCeti.Quiver.D4.rootVector`: the dimension vector with a given value at the centre and a `1`
  at each outer vertex of a given set. Every positive root has this shape.
* `TauCeti.Quiver.D4.posRoot`: the twelve positive roots, indexed by
  `Fin 3 ⊕ Finset (Fin 3) ⊕ Unit`.

## Main results

* `TauCeti.Quiver.D4.eulerForm_apply` and `TauCeti.Quiver.D4.titsForm_apply`: the two forms in
  coordinates, and `TauCeti.Quiver.D4.four_mul_titsForm` the sum-of-squares identity behind
  everything else.
* `TauCeti.Quiver.D4.titsForm_posDef`: the Tits form of `D₄` is positive definite.
* `TauCeti.Quiver.D4.titsForm_eq_one_iff_of_nonneg`: a nonnegative dimension vector has Tits norm
  one exactly when it is one of the listed positive roots.
* `TauCeti.Quiver.D4.card_positiveRoots`: there are exactly twelve of them.

## References

This file supplies the “`D₄` quiver” worked example of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, which asks for the twelve
positive roots of `D₄` -- the four simple roots, those with a `1` at the centre and a `1` on a
subset of the outer vertices, and the highest root with coefficient `2` at the centre. See
Derksen--Weyman, *An Introduction to Quiver Representations*, and Assem--Simson--Skowroński,
*Elements of the Representation Theory of Associative Algebras I*, Ch. VII.
-/

public section

namespace TauCeti

open _root_.Quiver

namespace Quiver.D4

/-! ### The two forms in coordinates -/

/-- The Euler form of the `D₄` quiver in the coordinates of its four vertices: the three arrows
contribute the single term `(∑ᵢ dᵢ) · e_center`. -/
-- Deliberately not `@[simp]`: `TauCeti.eulerForm_def` is already `simp` and rewrites `eulerForm`
-- to its defining sums, which is the normal form this lemma also produces.
theorem eulerForm_apply (d e : D4 → ℤ) :
    eulerForm D4 d e =
      d center * e center + ∑ i, d (outer i) * e (outer i) - (∑ i, d (outer i)) * e center := by
  rw [eulerForm_eq_sum_card]
  simp [Finset.sum_mul]

/-- The Tits form of the `D₄` quiver: `q(d) = c ^ 2 + ∑ᵢ aᵢ ^ 2 - c * ∑ᵢ aᵢ` for `c` the value at
the centre and `aᵢ` the values at the outer vertices. -/
-- Deliberately not `@[simp]`, for the same reason as `eulerForm_apply`.
theorem titsForm_apply (d : D4 → ℤ) :
    titsForm D4 d = d center ^ 2 + ∑ i, d (outer i) ^ 2 - d center * ∑ i, d (outer i) := by
  rw [titsForm_def, eulerForm_apply]
  simp only [← pow_two]
  ring

/-- **Four times the Tits form of `D₄` is a sum of four squares.** This single identity carries the
positive definiteness of the form and the bound `c ≤ 2` on the central coordinate of a root. -/
theorem four_mul_titsForm (d : D4 → ℤ) :
    4 * titsForm D4 d = d center ^ 2 + ∑ i, (2 * d (outer i) - d center) ^ 2 := by
  rw [titsForm_apply]
  simp only [Fin.sum_univ_three]
  ring

/-- The Tits form of `D₄` is positive semidefinite. -/
theorem titsForm_nonneg (d : D4 → ℤ) : 0 ≤ titsForm D4 d := by
  have hsum : 0 ≤ ∑ i, (2 * d (outer i) - d center) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hc := sq_nonneg (d center)
  have h := four_mul_titsForm d
  linarith

/-- **The Tits form of `D₄` is positive definite**, so `D₄` is a Dynkin quiver and, by Gabriel's
dichotomy, of finite representation type. -/
theorem titsForm_posDef : (titsForm D4).PosDef := by
  intro d hd
  rcases (titsForm_nonneg d).lt_or_eq with h | h
  · exact h
  refine absurd ?_ hd
  have h4 := four_mul_titsForm d
  rw [← h] at h4
  have hsum : 0 ≤ ∑ i, (2 * d (outer i) - d center) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcsq : d center ^ 2 = 0 := by
    have := sq_nonneg (d center)
    linarith
  have hzero : ∑ i, (2 * d (outer i) - d center) ^ 2 = 0 := by linarith
  have hc : d center = 0 := pow_eq_zero_iff two_ne_zero |>.mp hcsq
  refine eq_zero_iff.mpr ⟨hc, fun i => ?_⟩
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
    sq_nonneg (2 * d (outer j) - d center)).mp hzero i (Finset.mem_univ i)
  have h2 : 2 * d (outer i) - d center = 0 := pow_eq_zero_iff two_ne_zero |>.mp hi
  omega

/-! ### The shape of a positive root -/

/-- The dimension vector of `D₄` with the value `c` at the centre and a `1` at each outer vertex
lying in `s`. Every nonnegative dimension vector of Tits norm one has this shape. -/
def rootVector (c : ℤ) (s : Finset (Fin 3)) : D4 → ℤ
  | .center => c
  | .outer j => if j ∈ s then 1 else 0

@[simp]
theorem rootVector_center (c : ℤ) (s : Finset (Fin 3)) : rootVector c s center = c :=
  -- The parentheses keep this an ordinary proof term rather than an exported `rfl` theorem, which
  -- would force `rootVector` to be `@[expose]`.
  (rfl)

@[simp]
theorem rootVector_outer (c : ℤ) (s : Finset (Fin 3)) (j : Fin 3) :
    rootVector c s (outer j) = if j ∈ s then 1 else 0 := (rfl)

/-- A root vector with a nonnegative central coordinate is a nonnegative dimension vector. -/
theorem rootVector_nonneg {c : ℤ} (hc : 0 ≤ c) (s : Finset (Fin 3)) : 0 ≤ rootVector c s := by
  rw [Pi.le_def]
  intro v
  cases v with
  | center => simpa using hc
  | outer j =>
      rw [Pi.zero_apply, rootVector_outer]
      split <;> norm_num

/-- The sum of a root vector over the outer vertices is the size of its defining set. -/
theorem sum_rootVector_outer (c : ℤ) (s : Finset (Fin 3)) :
    ∑ j, rootVector c s (outer j) = (s.card : ℤ) := by
  simp only [rootVector_outer]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The Tits form on a root vector.** Because the outer coordinates are `0` or `1`, they are
their own squares, and `q(rootVector c s) = c ^ 2 + (1 - c) * #s`. -/
theorem titsForm_rootVector (c : ℤ) (s : Finset (Fin 3)) :
    titsForm D4 (rootVector c s) = c ^ 2 + (1 - c) * s.card := by
  have hsq : ∀ j : Fin 3, rootVector c s (outer j) ^ 2 = rootVector c s (outer j) := by
    intro j
    rw [rootVector_outer]
    split <;> ring
  rw [titsForm_apply, rootVector_center, Finset.sum_congr rfl fun j _ => hsq j,
    sum_rootVector_outer]
  ring

/-- Two root vectors agree exactly when both of their data do: the central coordinate is read off
at the centre, and the defining set from the outer coordinates. -/
theorem rootVector_eq_iff {c c' : ℤ} {s s' : Finset (Fin 3)} :
    rootVector c s = rootVector c' s' ↔ c = c' ∧ s = s' := by
  refine ⟨fun h => ⟨by simpa using congrFun h center, ?_⟩, ?_⟩
  · ext j
    have hj := congrFun h (outer j)
    rw [rootVector_outer, rootVector_outer] at hj
    by_cases h₁ : j ∈ s <;> by_cases h₂ : j ∈ s' <;> simp_all
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A dimension vector all of whose outer coordinates are `0` or `1` is the root vector at its own
central coordinate and the set of outer vertices where it takes the value `1`. -/
private theorem eq_rootVector_filter {d : D4 → ℤ}
    (hbin : ∀ i, d (outer i) = 0 ∨ d (outer i) = 1) :
    d = rootVector (d center) (Finset.univ.filter fun i => d (outer i) = 1) := by
  funext v
  cases v with
  | center => rw [rootVector_center]
  | outer j =>
      rw [rootVector_outer]
      rcases hbin j with h | h <;> simp [h]

/-- For such a vector the size of that set is the sum of the outer coordinates. -/
private theorem card_filter_eq_sum {d : D4 → ℤ}
    (hbin : ∀ i, d (outer i) = 0 ∨ d (outer i) = 1) :
    (((Finset.univ.filter fun i => d (outer i) = 1).card : ℤ)) = ∑ i, d (outer i) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hbin i with h | h <;> simp [h]

/-! ### The twelve positive roots -/

/-- **The positive roots of the `D₄` Tits form.** A nonnegative dimension vector has Tits norm one
exactly when it is a root vector of one of three kinds: an outer simple root (`0` at the centre and
a single outer `1`), a vector with a `1` at the centre and an arbitrary `0/1` pattern outside, or
the highest root (`2` at the centre and a `1` at every outer vertex). -/
theorem titsForm_eq_one_iff_of_nonneg {d : D4 → ℤ} (hd : 0 ≤ d) :
    titsForm D4 d = 1 ↔ ∃ (c : ℤ) (s : Finset (Fin 3)),
      d = rootVector c s ∧ ((c = 0 ∧ s.card = 1) ∨ c = 1 ∨ (c = 2 ∧ s = Finset.univ)) := by
  rw [Pi.le_def] at hd
  simp only [Pi.zero_apply] at hd
  constructor
  · intro h
    -- The central coordinate is bounded by the sum-of-squares identity.
    have h4 := four_mul_titsForm d
    rw [h] at h4
    have hsum : 0 ≤ ∑ i, (2 * d (outer i) - d center) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hcsq : d center ^ 2 ≤ 4 := by linarith
    have hc2 : d center ≤ 2 := by nlinarith [hd center]
    have ht := titsForm_apply d
    rw [h] at ht
    have hcases : d center = 0 ∨ d center = 1 ∨ d center = 2 := by
      have := hd center
      omega
    -- In each case the outer coordinates are forced to be `0` or `1`.
    have main : ∀ hbin : ∀ i, d (outer i) = 0 ∨ d (outer i) = 1,
        ∃ (c : ℤ) (s : Finset (Fin 3)), d = rootVector c s ∧ c = d center ∧
          ((s.card : ℤ) = ∑ i, d (outer i)) :=
      fun hbin => ⟨d center, _, eq_rootVector_filter hbin, rfl, card_filter_eq_sum hbin⟩
    rcases hcases with hc | hc | hc
    · -- `c = 0`: the outer coordinates square-sum to one, so exactly one of them is `1`.
      rw [hc] at ht
      have hle : ∀ i : Fin 3, d (outer i) ^ 2 ≤ 1 := by
        intro i
        have hsingle := Finset.single_le_sum (f := fun j : Fin 3 => d (outer j) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        linarith
      have hbin : ∀ i : Fin 3, d (outer i) = 0 ∨ d (outer i) = 1 := by
        intro i
        have h₀ := hd (outer i)
        have h₁ : d (outer i) ≤ 1 := by nlinarith [hle i]
        omega
      have hsq : ∀ i : Fin 3, d (outer i) ^ 2 = d (outer i) := by
        intro i
        rcases hbin i with h' | h' <;> rw [h'] <;> ring
      have hsumone : ∑ i, d (outer i) = 1 := by
        rw [← Finset.sum_congr rfl fun i _ => hsq i]
        linarith
      obtain ⟨c, s, hds, hcc, hcard⟩ := main hbin
      refine ⟨c, s, hds, Or.inl ⟨by rw [hcc, hc], ?_⟩⟩
      have : (s.card : ℤ) = 1 := by rw [hcard, hsumone]
      exact_mod_cast this
    · -- `c = 1`: each outer coordinate satisfies `aᵢ ^ 2 = aᵢ`.
      rw [hc] at ht
      have hnn : ∀ i : Fin 3, (0 : ℤ) ≤ d (outer i) ^ 2 - d (outer i) := by
        intro i
        have h₀ := hd (outer i)
        rcases eq_or_lt_of_le h₀ with h' | h'
        · rw [← h']
          norm_num
        · have h₁ : 1 ≤ d (outer i) := by omega
          nlinarith
      have hz : ∑ i, (d (outer i) ^ 2 - d (outer i)) = 0 := by
        rw [Finset.sum_sub_distrib]
        linarith
      have hbin : ∀ i : Fin 3, d (outer i) = 0 ∨ d (outer i) = 1 := by
        intro i
        have hi := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn j).mp hz i (Finset.mem_univ i)
        have hfac : d (outer i) * (d (outer i) - 1) = 0 := by linear_combination hi
        rcases mul_eq_zero.mp hfac with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by omega)
      obtain ⟨c, s, hds, hcc, -⟩ := main hbin
      exact ⟨c, s, hds, Or.inr (Or.inl (by rw [hcc, hc]))⟩
    · -- `c = 2`: the outer coordinates square-sum to their doubles less three, forcing each to
      -- be `1`.
      rw [hc] at ht
      have hz : ∑ i, (d (outer i) - 1) ^ 2 = 0 := by
        simp only [Fin.sum_univ_three] at ht ⊢
        linarith
      have hone : ∀ i : Fin 3, d (outer i) = 1 := by
        intro i
        have hi := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
          sq_nonneg (d (outer j) - 1)).mp hz i (Finset.mem_univ i)
        have := pow_eq_zero_iff two_ne_zero |>.mp hi
        omega
      obtain ⟨c, s, hds, hcc, hcard⟩ := main fun i => Or.inr (hone i)
      refine ⟨c, s, hds, Or.inr (Or.inr ⟨by rw [hcc, hc], ?_⟩)⟩
      refine Finset.eq_univ_of_card s ?_
      have : (s.card : ℤ) = 3 := by
        rw [hcard]
        simp [hone]
      simp only [Fintype.card_fin]
      exact_mod_cast this
  · rintro ⟨c, s, rfl, hcond⟩
    rw [titsForm_rootVector]
    rcases hcond with ⟨rfl, hcard⟩ | rfl | ⟨rfl, rfl⟩
    · rw [hcard]
      norm_num
    · ring
    · simp

/-- The twelve positive roots of `D₄`, indexed: `inl i` is the simple root at the `i`-th outer
vertex, `inr (inl s)` carries a `1` at the centre and a `1` at each outer vertex of `s` (so
`s = ∅` gives the simple root at the centre), and `inr (inr ())` is the highest root. -/
def posRoot : Fin 3 ⊕ Finset (Fin 3) ⊕ Unit → D4 → ℤ
  | .inl i => rootVector 0 {i}
  | .inr (.inl s) => rootVector 1 s
  | .inr (.inr _) => rootVector 2 Finset.univ

@[simp]
theorem posRoot_inl (i : Fin 3) : posRoot (.inl i) = rootVector 0 {i} :=
  -- The parentheses keep this an ordinary proof term rather than an exported `rfl` theorem, which
  -- would force `posRoot` to be `@[expose]`.
  (rfl)

@[simp]
theorem posRoot_inr_inl (s : Finset (Fin 3)) : posRoot (.inr (.inl s)) = rootVector 1 s := (rfl)

@[simp]
theorem posRoot_inr_inr (u : Unit) : posRoot (.inr (.inr u)) = rootVector 2 Finset.univ := (rfl)

/-- Each of the twelve listed vectors is nonnegative. -/
theorem posRoot_nonneg (x : Fin 3 ⊕ Finset (Fin 3) ⊕ Unit) : 0 ≤ posRoot x := by
  rcases x with i | s | u <;> simp only [posRoot_inl, posRoot_inr_inl, posRoot_inr_inr] <;>
    exact rootVector_nonneg (by norm_num) _

/-- Each of the twelve listed vectors has Tits norm one. -/
theorem titsForm_posRoot (x : Fin 3 ⊕ Finset (Fin 3) ⊕ Unit) : titsForm D4 (posRoot x) = 1 := by
  rcases x with i | s | u <;>
    simp only [posRoot_inl, posRoot_inr_inl, posRoot_inr_inr, titsForm_rootVector]
  · simp
  · ring
  · simp

/-- The twelve listed vectors are pairwise distinct. -/
theorem posRoot_injective : Function.Injective posRoot := by
  rintro (i | s | ⟨⟩) (j | t | ⟨⟩) h
  · rw [posRoot_inl, posRoot_inl, rootVector_eq_iff] at h
    rw [Finset.singleton_inj.mp h.2]
  · rw [posRoot_inl, posRoot_inr_inl, rootVector_eq_iff] at h
    exact absurd h.1 (by norm_num)
  · rw [posRoot_inl, posRoot_inr_inr, rootVector_eq_iff] at h
    exact absurd h.1 (by norm_num)
  · rw [posRoot_inr_inl, posRoot_inl, rootVector_eq_iff] at h
    exact absurd h.1 (by norm_num)
  · rw [posRoot_inr_inl, posRoot_inr_inl, rootVector_eq_iff] at h
    rw [h.2]
  · rw [posRoot_inr_inl, posRoot_inr_inr, rootVector_eq_iff] at h
    exact absurd h.1 (by norm_num)
  · rw [posRoot_inr_inr, posRoot_inl, rootVector_eq_iff] at h
    exact absurd h.1 (by norm_num)
  · rw [posRoot_inr_inr, posRoot_inr_inl, rootVector_eq_iff] at h
    exact absurd h.1 (by norm_num)
  · rfl

/-- **The positive roots of `D₄`, as the range of the indexing map.** -/
theorem titsForm_eq_one_iff_exists_posRoot {d : D4 → ℤ} (hd : 0 ≤ d) :
    titsForm D4 d = 1 ↔ ∃ x, posRoot x = d := by
  rw [titsForm_eq_one_iff_of_nonneg hd]
  constructor
  · rintro ⟨c, s, rfl, ⟨rfl, hcard⟩ | rfl | ⟨rfl, rfl⟩⟩
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
      exact ⟨.inl i, rfl⟩
    · exact ⟨.inr (.inl s), rfl⟩
    · exact ⟨.inr (.inr ()), rfl⟩
  · rintro ⟨x, rfl⟩
    rcases x with i | s | u
    · exact ⟨0, {i}, rfl, Or.inl ⟨rfl, Finset.card_singleton i⟩⟩
    · exact ⟨1, s, rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨2, Finset.univ, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

/-- **The `D₄` quiver has exactly twelve positive roots**, matching the twelve positive roots of
the root system `D₄`: the four simple roots, the six further vectors with a `1` at the centre and
a `1` at one or two outer vertices, the vector `(1,1,1;1)`, and the highest root `(1,1,1;2)`. -/
theorem card_positiveRoots :
    Nat.card {d : D4 → ℤ // 0 ≤ d ∧ titsForm D4 d = 1} = 12 := by
  have hbij : Function.Bijective
      (fun x : Fin 3 ⊕ Finset (Fin 3) ⊕ Unit =>
        (⟨posRoot x, posRoot_nonneg x, titsForm_posRoot x⟩ :
          {d : D4 → ℤ // 0 ≤ d ∧ titsForm D4 d = 1})) := by
    constructor
    · exact fun x y hxy => posRoot_injective (Subtype.ext_iff.mp hxy)
    · rintro ⟨d, hd, h1⟩
      obtain ⟨x, hx⟩ := (titsForm_eq_one_iff_exists_posRoot hd).mp h1
      exact ⟨x, Subtype.ext hx⟩
  rw [← Nat.card_eq_of_bijective _ hbij]
  simp

end Quiver.D4

end TauCeti
