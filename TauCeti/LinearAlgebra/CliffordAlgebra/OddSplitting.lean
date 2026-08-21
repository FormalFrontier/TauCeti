/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.FieldTheory.IsSepClosed

-- Private: the grade involution is used only inside proofs.
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Splitting a Clifford algebra along a central odd square root of one

An element `ω` of `CliffordAlgebra Q` which is **central**, **odd**, and squares to `1` splits the
algebra in two. The elements

`e₊ = ½ (1 + ω)`,  `e₋ = ½ (1 - ω)`

are complementary orthogonal central idempotents, and the resulting decomposition
`Cliff(Q) = e₊ Cliff(Q) ⊕ e₋ Cliff(Q)` has both summands isomorphic to the **even subalgebra**: the
map

`CliffordAlgebra.evenProdToClifford : even Q × even Q →ₐ[R] CliffordAlgebra Q`,
`(x, y) ↦ e₊ x + e₋ y`

is an isomorphism of `R`-algebras. That is the content of this file, and it needs nothing beyond
`2` being invertible — no field, no finiteness, no nondegeneracy.

Both halves of the proof are short once the grade involution `CliffordAlgebra.involute` is brought
in. *Injectivity* is the statement that an even `x` with `e₊ x = 0` vanishes: from `x + ω x = 0`,
applying `involute` (which fixes `x` and negates `ω`) gives `x - ω x = 0`, and adding the two kills
`ω` and leaves `2 x = 0`. *Surjectivity* never mentions dimensions either: the image of an algebra
map is a subalgebra, the generators `ι Q v` are in it because

`e₊ (ω · ι Q v) + e₋ (-(ω · ι Q v)) = (e₊ - e₋) · ω · ι Q v = ω² · ι Q v = ι Q v`

with `ω · ι Q v` even, and `CliffordAlgebra.adjoin_range_ι` says the generators generate.

The element the theorem is meant for is the **volume element** of
`TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement.lean`: the ordered product `ω = v₁ ⋯ vₙ` of a
pairwise orthogonal spanning list of **odd** length is central
(`CliffordAlgebra.prod_map_ι_mem_center_of_odd_length`) and odd, and its square is the scalar
`(-1) ^ (n.choose 2) ∏ᵢ Q vᵢ` (`CliffordAlgebra.prod_map_ι_sq_scalar`). Rescaling `ω` by a scalar
`s` whose square inverts that constant normalizes the square to `1`, which is what
`CliffordAlgebra.nonempty_algEquiv_even_prod_of_odd_length` asks for; over a separably closed field
of characteristic not two the rescaling always exists, and
`CliffordAlgebra.nonempty_algEquiv_even_prod_of_isSepClosed` drops the hypothesis in favour of the
orthogonal basis having no isotropic vector.

Only the odd case splits. For a list of even length the volume element anticommutes with the
generators rather than commuting with them, and the two idempotents are not central; the even-
dimensional Clifford algebra over a separably closed field is a matrix algebra, proved from the
spin module in `TauCeti/RepresentationTheory/Spin/Structure.lean`. Combining that file's
even-dimensional structure theorem with the splitting below is what turns an odd-dimensional
Clifford algebra into a product of two matrix algebras; the identification of `even Q` for an
odd-dimensional form with the Clifford algebra of an even-dimensional one is a separate step and is
not carried out here.

## Main definitions

* `CliffordAlgebra.splitIdem`: the element `½ (1 + ω)`, idempotent as soon as `ω * ω = 1`; the
  companion idempotent is `splitIdem (-ω)`.
* `CliffordAlgebra.evenProdToClifford`: the algebra map `(x, y) ↦ e₊ x + e₋ y` from two copies of
  the even subalgebra.
* `CliffordAlgebra.evenProdEquiv`: **the splitting**, that map promoted to an algebra isomorphism.

## Main results

* `CliffordAlgebra.isIdempotentElem_splitIdem`, `CliffordAlgebra.splitIdem_mul_splitIdem_neg` and
  `CliffordAlgebra.splitIdem_add_splitIdem_neg`: the two idempotents are orthogonal and
  complementary.
* `CliffordAlgebra.eq_zero_of_mem_even_of_splitIdem_mul_eq_zero`: an even element killed by `e₊`
  is zero — the grade involution argument that makes the splitting injective.
* `CliffordAlgebra.evenProdEquiv`: `even Q × even Q ≃ₐ[R] CliffordAlgebra Q`.
* `CliffordAlgebra.nonempty_algEquiv_even_prod_of_odd_length`: the splitting for the volume element
  of a pairwise orthogonal spanning list of odd length, once its square is normalized.
* `CliffordAlgebra.nonempty_algEquiv_even_prod_of_isSepClosed`: over a separably closed field of
  characteristic not two, an orthogonal spanning list of odd length with no isotropic member always
  normalizes, so the Clifford algebra is a product of two copies of its even subalgebra.

## Implementation notes

The idempotent lemmas of the first section use nothing about a Clifford algebra beyond its
`R`-algebra structure; they are stated here rather than for an arbitrary algebra because that is
where their only consumer is, and because `CliffordAlgebra.splitIdem` is named for the role it plays
in the splitting. `CliffordAlgebra.prod_map_ι_mem_evenOdd` likewise sits here rather than beside its
siblings in `VolumeElement.lean`, which is deliberately independent of the `ℤ/2` grading.

`CliffordAlgebra.evenProdEquiv` is oriented `even Q × even Q ≃ₐ[R] CliffordAlgebra Q`, the direction
in which `AlgEquiv.ofBijective` produces it and in which the evaluation lemma is readable; the two
corollaries are stated in the opposite direction, matching how the structure theorem is usually
quoted.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 1, "The odd-dimensional case": the two central idempotents split the odd Clifford algebra,
  while the even subalgebra stays a single block.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989), Chapter I,
  Proposition 3.7 and Theorem 4.3.
* C. Chevalley, *The Algebraic Theory of Spinors*, Columbia University Press (1954), Chapter II.
-/

public section

universe u v

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

section SplitIdem

variable [Invertible (2 : R)]

/-- The element `½ (1 + ω)` of a Clifford algebra.

It is an idempotent exactly in the situation this file is about, namely when `ω * ω = 1`
(`CliffordAlgebra.isIdempotentElem_splitIdem`), and then `splitIdem (-ω) = ½ (1 - ω)` is the
complementary one. No property of `ω` is built into the definition, so that the two idempotents are
literally the same construction applied to `ω` and to `-ω`. -/
noncomputable def splitIdem (ω : CliffordAlgebra Q) : CliffordAlgebra Q := (⅟2 : R) • (1 + ω)

variable {ω : CliffordAlgebra Q}

/-- The defining formula for `CliffordAlgebra.splitIdem`. -/
theorem splitIdem_def (ω : CliffordAlgebra Q) : splitIdem ω = (⅟2 : R) • (1 + ω) := (rfl)

/-- Halving cancels doubling: the shape in which `Invertible (2 : R)` is used below. -/
private theorem invOf_two_smul_two_smul (x : CliffordAlgebra Q) :
    (⅟2 : R) • ((2 : R) • x) = x := by
  rw [smul_smul, invOf_mul_self, one_smul]

/-- **The two idempotents are complementary**: `½ (1 + ω) + ½ (1 - ω) = 1`. -/
theorem splitIdem_add_splitIdem_neg (ω : CliffordAlgebra Q) :
    splitIdem ω + splitIdem (-ω) = 1 := by
  rw [splitIdem_def, splitIdem_def, ← smul_add]
  have h : (1 + ω) + (1 + -ω) = (2 : R) • (1 : CliffordAlgebra Q) := by
    rw [two_smul]; abel
  rw [h, invOf_two_smul_two_smul]

/-- **The difference of the two idempotents is `ω`**: `½ (1 + ω) - ½ (1 - ω) = ω`. This is what
makes `ω` recoverable from the splitting, and it is the identity that puts the generators of the
Clifford algebra in the range of `CliffordAlgebra.evenProdToClifford`. -/
theorem splitIdem_sub_splitIdem_neg (ω : CliffordAlgebra Q) :
    splitIdem ω - splitIdem (-ω) = ω := by
  rw [splitIdem_def, splitIdem_def, ← smul_sub]
  have h : (1 + ω) - (1 + -ω) = (2 : R) • ω := by rw [two_smul]; abel
  rw [h, invOf_two_smul_two_smul]

/-- **`½ (1 + ω)` is idempotent** when `ω` squares to `1`. -/
theorem isIdempotentElem_splitIdem (hsq : ω * ω = 1) :
    IsIdempotentElem (splitIdem ω) := by
  have h : (1 + ω) * (1 + ω) = (2 : R) • (1 + ω) := by
    rw [add_mul, one_mul, mul_add, mul_one, hsq, two_smul]
    abel
  rw [IsIdempotentElem, splitIdem_def, smul_mul_assoc, mul_smul_comm, h, smul_smul, smul_smul]
  congr 1
  rw [mul_assoc, invOf_mul_self, mul_one]

/-- **The two idempotents are orthogonal**: `½ (1 + ω) · ½ (1 - ω) = 0` when `ω * ω = 1`. -/
theorem splitIdem_mul_splitIdem_neg (hsq : ω * ω = 1) :
    splitIdem ω * splitIdem (-ω) = 0 := by
  have h : (1 + ω) * (1 + -ω) = 0 := by
    rw [add_mul, one_mul, mul_add, mul_one, mul_neg, hsq]
    abel
  rw [splitIdem_def, splitIdem_def, smul_mul_assoc, mul_smul_comm, h, smul_zero, smul_zero]

/-- The reverse orthogonality `½ (1 - ω) · ½ (1 + ω) = 0`, obtained from
`CliffordAlgebra.splitIdem_mul_splitIdem_neg` at `-ω`. -/
theorem splitIdem_neg_mul_splitIdem (hsq : ω * ω = 1) :
    splitIdem (-ω) * splitIdem ω = 0 := by
  have h := splitIdem_mul_splitIdem_neg (ω := -ω) (by rw [neg_mul_neg]; exact hsq)
  rwa [neg_neg] at h

/-- **The idempotents inherit centrality from `ω`.** -/
theorem commute_splitIdem (hcomm : ∀ x, Commute ω x) (x : CliffordAlgebra Q) :
    Commute (splitIdem ω) x := by
  rw [splitIdem_def]
  exact Commute.smul_left ((Commute.one_left x).add_left (hcomm x)) _

/-- **An even element annihilated by `½ (1 + ω)` vanishes**, for `ω` odd with `ω * ω = 1`.

The grade involution fixes `x` and negates `ω`, so from `x + ω x = 0` it produces `x - ω x = 0`;
the two together give `2 x = 0`. Nothing else about `ω` is used, so the same statement at `-ω`
covers the complementary idempotent. -/
theorem eq_zero_of_mem_even_of_splitIdem_mul_eq_zero (hodd : ω ∈ evenOdd Q 1)
    {x : CliffordAlgebra Q} (hx : x ∈ evenOdd Q 0) (h : splitIdem ω * x = 0) : x = 0 := by
  have h1 : x + ω * x = 0 := by
    have h2 : (2 : R) • (splitIdem ω * x) = (1 + ω) * x := by
      rw [splitIdem_def, smul_mul_assoc, smul_smul, mul_invOf_self, one_smul]
    rw [h, smul_zero] at h2
    have h3 := h2.symm
    rwa [add_mul, one_mul] at h3
  have h2 : x - ω * x = 0 := by
    have h3 := congrArg (involute (Q := Q)) h1
    rw [map_add, map_mul, map_zero, involute_eq_of_mem_even hx, involute_eq_of_mem_odd hodd,
      neg_mul, ← sub_eq_add_neg] at h3
    exact h3
  have h4 : (2 : R) • x = 0 := by
    rw [two_smul]
    have h5 : x + x = (x + ω * x) + (x - ω * x) := by abel
    rw [h5, h1, h2, add_zero]
  calc x = (⅟2 : R) • ((2 : R) • x) := (invOf_two_smul_two_smul x).symm
    _ = 0 := by rw [h4, smul_zero]

end SplitIdem

/-! ### The splitting -/

section Splitting

variable [Invertible (2 : R)] {ω : CliffordAlgebra Q}

/-- The multiplication rule the splitting rests on: the two idempotents being orthogonal, central
and idempotent, the products of two elements of the form `e₊ a + e₋ b` multiply componentwise. -/
private theorem splitIdem_mul_add_mul (hcomm : ∀ x, Commute ω x) (hsq : ω * ω = 1)
    (a b c d : CliffordAlgebra Q) :
    (splitIdem ω * a + splitIdem (-ω) * b) *
        (splitIdem ω * c + splitIdem (-ω) * d)
      = splitIdem ω * (a * c) + splitIdem (-ω) * (b * d) := by
  have hcomm' : ∀ x, Commute (-ω) x := fun x => (hcomm x).neg_left
  have hee := (isIdempotentElem_splitIdem hsq).eq
  have hff := (isIdempotentElem_splitIdem (ω := -ω)
    (by rw [neg_mul_neg]; exact hsq)).eq
  have hef := splitIdem_mul_splitIdem_neg hsq
  have hfe := splitIdem_neg_mul_splitIdem hsq
  have hae : Commute a (splitIdem ω) := (commute_splitIdem hcomm a).symm
  have haf : Commute a (splitIdem (-ω)) := (commute_splitIdem hcomm' a).symm
  have hbe : Commute b (splitIdem ω) := (commute_splitIdem hcomm b).symm
  have hbf : Commute b (splitIdem (-ω)) := (commute_splitIdem hcomm' b).symm
  calc (splitIdem ω * a + splitIdem (-ω) * b) *
        (splitIdem ω * c + splitIdem (-ω) * d)
      = splitIdem ω * a * (splitIdem ω * c)
          + splitIdem ω * a * (splitIdem (-ω) * d)
          + (splitIdem (-ω) * b * (splitIdem ω * c)
            + splitIdem (-ω) * b * (splitIdem (-ω) * d)) := by
        rw [add_mul, mul_add, mul_add]
    _ = splitIdem ω * splitIdem ω * (a * c)
          + splitIdem ω * splitIdem (-ω) * (a * d)
          + (splitIdem (-ω) * splitIdem ω * (b * c)
            + splitIdem (-ω) * splitIdem (-ω) * (b * d)) := by
        rw [hae.mul_mul_mul_comm _ c, haf.mul_mul_mul_comm _ d, hbe.mul_mul_mul_comm _ c,
          hbf.mul_mul_mul_comm _ d]
    _ = splitIdem ω * (a * c) + splitIdem (-ω) * (b * d) := by
        rw [hee, hff, hef, hfe, zero_mul, zero_mul, add_zero, zero_add]

variable (Q ω) in
/-- **The splitting map**: `(x, y) ↦ ½ (1 + ω) x + ½ (1 - ω) y` from two copies of the even
subalgebra to the whole Clifford algebra, for a central `ω` squaring to `1`.

The proofs are `Prop` arguments, so two instances built from different proofs of the same
hypotheses are equal by proof irrelevance. -/
noncomputable def evenProdToClifford (hcomm : ∀ x, Commute ω x) (hsq : ω * ω = 1) :
    (↥(even Q) × ↥(even Q)) →ₐ[R] CliffordAlgebra Q where
  toFun p := splitIdem ω * (p.1 : CliffordAlgebra Q)
    + splitIdem (-ω) * (p.2 : CliffordAlgebra Q)
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, OneMemClass.coe_one, mul_one]
    exact splitIdem_add_splitIdem_neg ω
  map_mul' p q := (splitIdem_mul_add_mul hcomm hsq _ _ _ _).symm
  map_zero' := by simp
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, AddMemClass.coe_add, mul_add]
    abel
  commutes' r := by
    simp only [Prod.algebraMap_apply, SubalgebraClass.coe_algebraMap, ← add_mul]
    rw [splitIdem_add_splitIdem_neg, one_mul]

variable (Q ω) in
@[simp]
theorem evenProdToClifford_apply (hcomm : ∀ x, Commute ω x) (hsq : ω * ω = 1)
    (p : ↥(even Q) × ↥(even Q)) :
    evenProdToClifford Q ω hcomm hsq p
      = splitIdem ω * (p.1 : CliffordAlgebra Q)
        + splitIdem (-ω) * (p.2 : CliffordAlgebra Q) := (rfl)

/-- The splitting map is injective: multiplying by one idempotent isolates one component, and
`CliffordAlgebra.eq_zero_of_mem_even_of_splitIdem_mul_eq_zero` kills it. -/
theorem evenProdToClifford_injective (hcomm : ∀ x, Commute ω x) (hodd : ω ∈ evenOdd Q 1)
    (hsq : ω * ω = 1) : Function.Injective (evenProdToClifford Q ω hcomm hsq) := by
  have hodd' : -ω ∈ evenOdd Q 1 := Submodule.neg_mem _ hodd
  have hee := (isIdempotentElem_splitIdem hsq).eq
  have hff := (isIdempotentElem_splitIdem (ω := -ω)
    (by rw [neg_mul_neg]; exact hsq)).eq
  have hef := splitIdem_mul_splitIdem_neg hsq
  have hfe := splitIdem_neg_mul_splitIdem hsq
  refine (injective_iff_map_eq_zero _).mpr ?_
  rintro ⟨x, y⟩ h
  rw [evenProdToClifford_apply] at h
  have hx : splitIdem ω * (x : CliffordAlgebra Q) = 0 := by
    have h' := congrArg (fun z => splitIdem ω * z) h
    simp only [mul_add, ← mul_assoc, hee, hef, zero_mul, add_zero, mul_zero] at h'
    exact h'
  have hy : splitIdem (-ω) * (y : CliffordAlgebra Q) = 0 := by
    have h' := congrArg (fun z => splitIdem (-ω) * z) h
    simp only [mul_add, ← mul_assoc, hff, hfe, zero_mul, zero_add, mul_zero] at h'
    exact h'
  have hxmem : (x : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule Q]; exact x.2
  have hymem : (y : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule Q]; exact y.2
  have hx0 : (x : CliffordAlgebra Q) = 0 :=
    eq_zero_of_mem_even_of_splitIdem_mul_eq_zero hodd hxmem hx
  have hy0 : (y : CliffordAlgebra Q) = 0 :=
    eq_zero_of_mem_even_of_splitIdem_mul_eq_zero hodd' hymem hy
  exact Prod.ext (Subtype.ext hx0) (Subtype.ext hy0)

/-- The splitting map is surjective: its range is a subalgebra containing every generator
`ι Q v`, because `ω · ι Q v` is even and `(e₊ - e₋) ω = ω² = 1`. -/
theorem evenProdToClifford_surjective (hcomm : ∀ x, Commute ω x) (hodd : ω ∈ evenOdd Q 1)
    (hsq : ω * ω = 1) : Function.Surjective (evenProdToClifford Q ω hcomm hsq) := by
  rw [← AlgHom.range_eq_top, eq_top_iff, ← adjoin_range_ι (Q := Q)]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨v, rfl⟩
  have hev : ω * ι Q v ∈ even Q := by
    have h := SetLike.mul_mem_graded hodd (ι_mem_evenOdd_one Q v)
    rw [show (1 : ZMod 2) + 1 = 0 by decide, ← even_toSubmodule Q] at h
    exact h
  refine (evenProdToClifford Q ω hcomm hsq).mem_range.mpr
    ⟨(⟨ω * ι Q v, hev⟩, ⟨-(ω * ι Q v), neg_mem hev⟩), ?_⟩
  rw [evenProdToClifford_apply]
  calc splitIdem ω * (ω * ι Q v) + splitIdem (-ω) * (-(ω * ι Q v))
      = (splitIdem ω - splitIdem (-ω)) * (ω * ι Q v) := by
        rw [sub_mul, mul_neg, ← sub_eq_add_neg]
    _ = ι Q v := by rw [splitIdem_sub_splitIdem_neg, ← mul_assoc, hsq, one_mul]

variable (Q ω) in
/-- **The splitting**: a central odd `ω` with `ω * ω = 1` presents the Clifford algebra as two
copies of its even subalgebra, glued along the complementary central idempotents `½ (1 ± ω)`. -/
noncomputable def evenProdEquiv (hcomm : ∀ x, Commute ω x) (hodd : ω ∈ evenOdd Q 1)
    (hsq : ω * ω = 1) : (↥(even Q) × ↥(even Q)) ≃ₐ[R] CliffordAlgebra Q :=
  AlgEquiv.ofBijective (evenProdToClifford Q ω hcomm hsq)
    ⟨evenProdToClifford_injective hcomm hodd hsq, evenProdToClifford_surjective hcomm hodd hsq⟩

variable (Q ω) in
@[simp]
theorem evenProdEquiv_apply (hcomm : ∀ x, Commute ω x) (hodd : ω ∈ evenOdd Q 1) (hsq : ω * ω = 1)
    (p : ↥(even Q) × ↥(even Q)) :
    evenProdEquiv Q ω hcomm hodd hsq p
      = splitIdem ω * (p.1 : CliffordAlgebra Q)
        + splitIdem (-ω) * (p.2 : CliffordAlgebra Q) := (rfl)

end Splitting

/-! ### The volume element as the splitting element -/

/-- **An ordered product of `n` generators is homogeneous of degree `n`** for the `ℤ/2` grading. -/
theorem prod_map_ι_mem_evenOdd :
    ∀ l : List M, (l.map (ι Q)).prod ∈ evenOdd Q (l.length : ZMod 2)
  | [] => by simpa using SetLike.one_mem_graded (evenOdd Q)
  | a :: l => by
      have h := SetLike.mul_mem_graded (ι_mem_evenOdd_one Q a) (prod_map_ι_mem_evenOdd l)
      rw [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
        add_comm (l.length : ZMod 2) 1]
      exact h

/-- **The volume element of an odd number of vectors is odd.** -/
theorem prod_map_ι_mem_evenOdd_one_of_odd {l : List M} (hlen : Odd l.length) :
    (l.map (ι Q)).prod ∈ evenOdd Q 1 := by
  have h : (l.length : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod l.length 2, Nat.odd_iff.mp hlen, Nat.cast_one]
  exact h ▸ prod_map_ι_mem_evenOdd l

variable [Invertible (2 : R)]

/-- **The odd-dimensional splitting, run on the volume element.** For a pairwise orthogonal list of
vectors spanning `M`, of odd length, whose volume element has been rescaled by `s` so as to square
to `1`, the Clifford algebra is the product of two copies of its even subalgebra.

The normalization hypothesis is exactly `(s ω)² = 1` read through
`CliffordAlgebra.prod_map_ι_sq_scalar`; it forces each `Q vᵢ` to be a unit, so it carries the
nondegeneracy the statement needs without naming it. -/
theorem nonempty_algEquiv_even_prod_of_odd_length {l : List M} (hl : l.Pairwise Q.IsOrtho)
    (hlen : Odd l.length) (hspan : Submodule.span R {x : M | x ∈ l} = ⊤) {s : R}
    (hs : s * s * ((-1 : R) ^ l.length.choose 2 * (l.map Q).prod) = 1) :
    Nonempty (CliffordAlgebra Q ≃ₐ[R] (↥(even Q) × ↥(even Q))) := by
  set P : CliffordAlgebra Q := (l.map (ι Q)).prod with hP
  have hcenter : s • P ∈ Subalgebra.center R (CliffordAlgebra Q) :=
    Subalgebra.smul_mem _ (prod_map_ι_mem_center_of_odd_length hl hlen hspan) s
  have hcomm : ∀ x, Commute (s • P) x := fun x =>
    (Subalgebra.mem_center_iff.mp hcenter x).symm
  have hodd : s • P ∈ evenOdd Q 1 :=
    Submodule.smul_mem _ s (prod_map_ι_mem_evenOdd_one_of_odd hlen)
  have hsq : (s • P) * (s • P) = 1 := by
    rw [smul_mul_assoc, mul_smul_comm, hP, prod_map_ι_sq_scalar hl, smul_smul, Algebra.smul_def,
      ← map_mul, hs, map_one]
  exact ⟨(evenProdEquiv Q _ hcomm hodd hsq).symm⟩

/-- **Over a separably closed field of characteristic not two the normalization is automatic.**

An orthogonal spanning list of odd length with no isotropic member has a volume element whose
square is a nonzero scalar, and a separably closed field supplies its inverse square root, so the
Clifford algebra of such a form is the product of two copies of its even subalgebra. This is the
odd-dimensional half of the structure theorem, up to the identification of the even subalgebra with
a matrix algebra. -/
theorem nonempty_algEquiv_even_prod_of_isSepClosed {K V : Type*} [Field K] [IsSepClosed K]
    [AddCommGroup V] [Module K V] [Invertible (2 : K)] {Q : QuadraticForm K V} {l : List V}
    (hl : l.Pairwise Q.IsOrtho) (hlen : Odd l.length)
    (hspan : Submodule.span K {x : V | x ∈ l} = ⊤) (hQ : ∀ v ∈ l, Q v ≠ 0) :
    Nonempty (CliffordAlgebra Q ≃ₐ[K] (↥(even Q) × ↥(even Q))) := by
  have h2 : NeZero (2 : K) := ⟨Invertible.ne_zero 2⟩
  set c : K := (-1 : K) ^ l.length.choose 2 * (l.map Q).prod
  have hprod : (l.map Q).prod ≠ 0 := by
    refine List.prod_ne_zero ?_
    rintro hmem
    obtain ⟨v, hv, hv0⟩ := List.mem_map.mp hmem
    exact hQ v hv hv0
  have hcne : c ≠ 0 := mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hprod
  obtain ⟨s, hsz⟩ := IsSepClosed.exists_eq_mul_self (k := K) c⁻¹
  exact nonempty_algEquiv_even_prod_of_odd_length hl hlen hspan
    (s := s) (by rw [← hsz, inv_mul_cancel₀ hcne])

end CliffordAlgebra
