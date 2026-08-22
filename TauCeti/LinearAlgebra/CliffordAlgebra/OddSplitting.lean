/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement
public import TauCeti.RingTheory.Idempotents.SquareRootOne
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.FieldTheory.IsSepClosed

-- Private: the grade involution is used only inside proofs.
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Splitting a Clifford algebra along a central odd square root of one

An element `ω` of `CliffordAlgebra Q` which is **central**, **odd**, and squares to `1` splits the
algebra in two. The elements

`e₊ = ½ (1 + ω)`,  `e₋ = ½ (1 - ω)`

are complementary orthogonal idempotents — central as soon as `ω` is, and that much is general
algebra, recorded for an arbitrary `R`-algebra in
`TauCeti/RingTheory/Idempotents/SquareRootOne.lean` — and the resulting decomposition
`Cliff(Q) = e₊ Cliff(Q) ⊕ e₋ Cliff(Q)` has both summands isomorphic to the **even subalgebra**: the
map

`CliffordAlgebra.ofEvenProd : even Q × even Q →ₐ[R] CliffordAlgebra Q`,
`(x, y) ↦ e₊ x + e₋ y`

is an isomorphism of `R`-algebras. That is the content of this file, and it needs nothing beyond
`2` being invertible — no field, no finiteness, no nondegeneracy. Centrality is more than the
proofs use: multiplication only ever moves `ω` past even elements, so the declarations below ask
only that `ω` commute with `even Q`, and it is the volume element application that supplies a
genuinely central `ω`.

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
`CliffordAlgebra.equivEvenProdOfOddLength` asks for; over a separably closed field of characteristic
not two the rescaling always exists, and
`CliffordAlgebra.nonempty_algEquiv_even_prod_of_isSepClosed` drops the hypothesis in favour of the
orthogonal basis having no isotropic vector.

Only the odd case splits this way. For a list of even length the volume element anticommutes with
the generators coming from the span of the list rather than commuting with them
(`CliffordAlgebra.prod_map_ι_mul_ι_of_even_length`). Anticommutation does not by itself rule out
centrality — in an exterior algebra the volume element annihilates the generators and is central
all the same, as `VolumeElement.lean` records — but it does rule it out under the hypotheses this
file works with: were an even-length `ω` with `ω * ω = 1` central, then `2` being invertible would
give `ι Q m * ω = 0`, hence `ι Q m = ι Q m * ω * ω = 0`, for every `m` in the span of the list. The
even-dimensional Clifford algebra over a separably closed field is instead a matrix algebra, proved
from the spin module in
`TauCeti/RepresentationTheory/Spin/Structure.lean`. Combining that file's even-dimensional
structure theorem with the splitting below is what turns an odd-dimensional Clifford algebra into a
product of two matrix algebras; the identification of `even Q` for an odd-dimensional form with the
Clifford algebra of an even-dimensional one is a separate step and is not carried out here.

## Main definitions

* `CliffordAlgebra.ofEvenProd`: the algebra map `(x, y) ↦ e₊ x + e₋ y` from two copies of the even
  subalgebra, built on `TauCeti.halfOneAdd`.
* `CliffordAlgebra.equivEvenProd`: **the splitting**, that map promoted to an algebra isomorphism
  and read as `CliffordAlgebra Q ≃ₐ[R] even Q × even Q`.
* `CliffordAlgebra.equivEvenProdOfOddLength`: the splitting run on the volume element of a pairwise
  orthogonal spanning list of odd length, once its square has been normalized.

## Main results

* `CliffordAlgebra.eq_zero_of_mem_even_of_halfOneAdd_mul_eq_zero`: an even element killed by `e₊`
  is zero — the grade involution argument that makes the splitting injective.
* `CliffordAlgebra.ofEvenProd_injective` and `CliffordAlgebra.ofEvenProd_surjective`: the two halves
  of `CliffordAlgebra.equivEvenProd`.
* `CliffordAlgebra.coe_equivEvenProd_apply_fst` and `CliffordAlgebra.coe_equivEvenProd_apply_snd`:
  the forward direction of the splitting, `x ↦ (e₊ x + e₋ x̂, e₋ x + e₊ x̂)` with `x̂` the grade
  involution of `x`.
* `CliffordAlgebra.nonempty_algEquiv_even_prod_of_isSepClosed`: over a separably closed field of
  characteristic not two, an orthogonal spanning list of odd length with no isotropic member always
  normalizes, so the Clifford algebra is a product of two copies of its even subalgebra. The
  scalar rescaling comes from an existential there, which is why this one is a `Nonempty`
  statement rather than a definition.

## Implementation notes

`CliffordAlgebra.equivEvenProd` is oriented `CliffordAlgebra Q ≃ₐ[R] even Q × even Q`, matching
`CliffordAlgebra.equivEven` and the direction in which the structure theorem is usually quoted; its
underlying algebra map `CliffordAlgebra.ofEvenProd` runs the other way, which is the direction in
which the formula `(x, y) ↦ e₊ x + e₋ y` is the readable one, so that formula is stated for
`.symm`. The forward direction is read off the same two idempotents together with the grade
involution, one lemma per component, stated at the level of the underlying Clifford element so that
no membership proof has to appear in the statement.

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

open TauCeti (halfOneAdd)

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

/-! ### The splitting -/

section Splitting

variable [Invertible (2 : R)] {ω : CliffordAlgebra Q}

/-- **An even element annihilated by `½ (1 + ω)` vanishes**, for `ω` odd.

The grade involution fixes `x` and negates `ω`, so from `x + ω x = 0` it produces `x - ω x = 0`;
the two together give `2 x = 0`. Nothing else about `ω` is used, so the same statement at `-ω`
covers the complementary idempotent. -/
theorem eq_zero_of_mem_even_of_halfOneAdd_mul_eq_zero (hodd : ω ∈ evenOdd Q 1)
    {x : CliffordAlgebra Q} (hx : x ∈ evenOdd Q 0) (h : halfOneAdd R ω * x = 0) : x = 0 := by
  have h1 : x + ω * x = 0 := by
    have h2 : (2 : R) • (halfOneAdd R ω * x) = (1 + ω) * x := by
      rw [TauCeti.halfOneAdd_def, smul_mul_assoc, smul_smul, mul_invOf_self, one_smul]
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
  calc x = (⅟2 : R) • ((2 : R) • x) := (invOf_smul_smul (2 : R) x).symm
    _ = 0 := by rw [h4, smul_zero]

variable (Q ω) in
/-- **The splitting map**: `(x, y) ↦ ½ (1 + ω) x + ½ (1 - ω) y` from two copies of the even
subalgebra to the whole Clifford algebra, for an `ω` squaring to `1` which commutes with the even
subalgebra. Multiplication only ever moves `ω` past the two even components, so commutation with
`even Q` is all that is asked; a central `ω` — the case the volume element supplies — is a
special case.

The proofs are `Prop` arguments, so two instances built from different proofs of the same
hypotheses are equal by proof irrelevance. -/
noncomputable def ofEvenProd (hcomm : ∀ x : ↥(even Q), Commute ω (x : CliffordAlgebra Q))
    (hsq : ω * ω = 1) :
    (↥(even Q) × ↥(even Q)) →ₐ[R] CliffordAlgebra Q where
  toFun p := halfOneAdd R ω * (p.1 : CliffordAlgebra Q)
    + halfOneAdd R (-ω) * (p.2 : CliffordAlgebra Q)
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, OneMemClass.coe_one, mul_one]
    exact TauCeti.halfOneAdd_add_halfOneAdd_neg R ω
  map_mul' p q := (TauCeti.halfOneAdd_mul_add_mul R hsq (hcomm _) (hcomm _) _ _).symm
  map_zero' := by simp
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, AddMemClass.coe_add, mul_add]
    abel
  commutes' r := by
    simp only [Prod.algebraMap_apply, SubalgebraClass.coe_algebraMap, ← add_mul]
    rw [TauCeti.halfOneAdd_add_halfOneAdd_neg, one_mul]

variable (Q ω) in
@[simp]
theorem ofEvenProd_apply (hcomm : ∀ x : ↥(even Q), Commute ω (x : CliffordAlgebra Q))
    (hsq : ω * ω = 1) (p : ↥(even Q) × ↥(even Q)) :
    ofEvenProd Q ω hcomm hsq p
      = halfOneAdd R ω * (p.1 : CliffordAlgebra Q)
        + halfOneAdd R (-ω) * (p.2 : CliffordAlgebra Q) := (rfl)

/-- The splitting map is injective: multiplying by one idempotent isolates one component, and
`CliffordAlgebra.eq_zero_of_mem_even_of_halfOneAdd_mul_eq_zero` kills it. -/
theorem ofEvenProd_injective (hcomm : ∀ x : ↥(even Q), Commute ω (x : CliffordAlgebra Q))
    (hodd : ω ∈ evenOdd Q 1) (hsq : ω * ω = 1) :
    Function.Injective (ofEvenProd Q ω hcomm hsq) := by
  have hodd' : -ω ∈ evenOdd Q 1 := Submodule.neg_mem _ hodd
  have hee := (TauCeti.isIdempotentElem_halfOneAdd R hsq).eq
  have hff := (TauCeti.isIdempotentElem_halfOneAdd_neg R hsq).eq
  have hef := TauCeti.halfOneAdd_mul_halfOneAdd_neg R hsq
  have hfe := TauCeti.halfOneAdd_neg_mul_halfOneAdd R hsq
  refine (injective_iff_map_eq_zero _).mpr ?_
  rintro ⟨x, y⟩ h
  rw [ofEvenProd_apply] at h
  have hx : halfOneAdd R ω * (x : CliffordAlgebra Q) = 0 := by
    have h' := congrArg (fun z => halfOneAdd R ω * z) h
    simp only [mul_add, ← mul_assoc, hee, hef, zero_mul, add_zero, mul_zero] at h'
    exact h'
  have hy : halfOneAdd R (-ω) * (y : CliffordAlgebra Q) = 0 := by
    have h' := congrArg (fun z => halfOneAdd R (-ω) * z) h
    simp only [mul_add, ← mul_assoc, hff, hfe, zero_mul, zero_add, mul_zero] at h'
    exact h'
  have hxmem : (x : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule Q]; exact x.2
  have hymem : (y : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule Q]; exact y.2
  have hx0 : (x : CliffordAlgebra Q) = 0 :=
    eq_zero_of_mem_even_of_halfOneAdd_mul_eq_zero hodd hxmem hx
  have hy0 : (y : CliffordAlgebra Q) = 0 :=
    eq_zero_of_mem_even_of_halfOneAdd_mul_eq_zero hodd' hymem hy
  exact Prod.ext (Subtype.ext hx0) (Subtype.ext hy0)

/-- The splitting map is surjective: its range is a subalgebra containing every generator
`ι Q v`, because `ω · ι Q v` is even and `(e₊ - e₋) ω = ω² = 1`. -/
theorem ofEvenProd_surjective (hcomm : ∀ x : ↥(even Q), Commute ω (x : CliffordAlgebra Q))
    (hodd : ω ∈ evenOdd Q 1) (hsq : ω * ω = 1) :
    Function.Surjective (ofEvenProd Q ω hcomm hsq) := by
  rw [← AlgHom.range_eq_top, eq_top_iff, ← adjoin_range_ι (Q := Q)]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨v, rfl⟩
  have hev : ω * ι Q v ∈ even Q := by
    -- odd times odd is even: the two degrees add up to `0` in `ZMod 2`.
    have hdeg : (1 : ZMod 2) + 1 = 0 := by decide
    have h := SetLike.mul_mem_graded hodd (ι_mem_evenOdd_one Q v)
    rw [hdeg, ← even_toSubmodule Q] at h
    exact h
  refine (ofEvenProd Q ω hcomm hsq).mem_range.mpr
    ⟨(⟨ω * ι Q v, hev⟩, ⟨-(ω * ι Q v), neg_mem hev⟩), ?_⟩
  rw [ofEvenProd_apply]
  calc halfOneAdd R ω * (ω * ι Q v) + halfOneAdd R (-ω) * (-(ω * ι Q v))
      = (halfOneAdd R ω - halfOneAdd R (-ω)) * (ω * ι Q v) := by
        rw [sub_mul, mul_neg, ← sub_eq_add_neg]
    _ = ι Q v := by
        rw [TauCeti.halfOneAdd_sub_halfOneAdd_neg, ← mul_assoc, hsq, one_mul]

/-- The two halves together: the splitting map is bijective. -/
theorem ofEvenProd_bijective (hcomm : ∀ x : ↥(even Q), Commute ω (x : CliffordAlgebra Q))
    (hodd : ω ∈ evenOdd Q 1) (hsq : ω * ω = 1) :
    Function.Bijective (ofEvenProd Q ω hcomm hsq) :=
  ⟨ofEvenProd_injective hcomm hodd hsq, ofEvenProd_surjective hcomm hodd hsq⟩

variable (Q ω) in
/-- **The splitting**: an odd `ω` with `ω * ω = 1` commuting with the even subalgebra presents the
Clifford algebra as two copies of that subalgebra, glued along the complementary idempotents
`½ (1 ± ω)`. -/
noncomputable def equivEvenProd (hcomm : ∀ x : ↥(even Q), Commute ω (x : CliffordAlgebra Q))
    (hodd : ω ∈ evenOdd Q 1) (hsq : ω * ω = 1) :
    CliffordAlgebra Q ≃ₐ[R] (↥(even Q) × ↥(even Q)) :=
  (AlgEquiv.ofBijective (ofEvenProd Q ω hcomm hsq) (ofEvenProd_bijective hcomm hodd hsq)).symm

variable (Q ω) in
@[simp]
theorem equivEvenProd_symm_apply (hcomm : ∀ x : ↥(even Q), Commute ω (x : CliffordAlgebra Q))
    (hodd : ω ∈ evenOdd Q 1) (hsq : ω * ω = 1) (p : ↥(even Q) × ↥(even Q)) :
    (equivEvenProd Q ω hcomm hodd hsq).symm p
      = halfOneAdd R ω * (p.1 : CliffordAlgebra Q)
        + halfOneAdd R (-ω) * (p.2 : CliffordAlgebra Q) := by
  rw [equivEvenProd, AlgEquiv.symm_symm, AlgEquiv.ofBijective_apply, ofEvenProd_apply]

/-- The grade involution swaps the two idempotents, for `ω` odd. -/
theorem involute_halfOneAdd (hodd : ω ∈ evenOdd Q 1) :
    involute (halfOneAdd R ω) = halfOneAdd R (-ω) := by
  rw [TauCeti.halfOneAdd_def, TauCeti.halfOneAdd_def, map_smul, map_add, map_one,
    involute_eq_of_mem_odd hodd]

/-- The grade involution swaps the two idempotents, read in the other direction. -/
theorem involute_halfOneAdd_neg (hodd : ω ∈ evenOdd Q 1) :
    involute (halfOneAdd R (-ω)) = halfOneAdd R ω := by
  rw [involute_halfOneAdd (Submodule.neg_mem _ hodd), neg_neg]

/-- **The component calculation both formulas below rest on.** For involution-fixed `a` and `b`,
multiplying `e₊ a + e₋ b` by `e₊` and its grade involution by `e₋` recovers `a`: the involution
swaps the two idempotents, so each of the two terms contributes `a` against its own idempotent and
`0` against the other, and the pair sums to `1`.

The second component is this same statement at `-ω`, which is why it is stated for a bare `ω`. -/
private theorem halfOneAdd_mul_add_halfOneAdd_neg_mul_involute (hodd : ω ∈ evenOdd Q 1)
    (hsq : ω * ω = 1) {a b : CliffordAlgebra Q} (ha : involute a = a) (hb : involute b = b) :
    halfOneAdd R ω * (halfOneAdd R ω * a + halfOneAdd R (-ω) * b)
        + halfOneAdd R (-ω) * involute (halfOneAdd R ω * a + halfOneAdd R (-ω) * b) = a := by
  have hee := (TauCeti.isIdempotentElem_halfOneAdd R hsq).eq
  have hff := (TauCeti.isIdempotentElem_halfOneAdd_neg R hsq).eq
  have hef := TauCeti.halfOneAdd_mul_halfOneAdd_neg R hsq
  have hfe := TauCeti.halfOneAdd_neg_mul_halfOneAdd R hsq
  simp only [map_add, map_mul, ha, hb, involute_halfOneAdd hodd, involute_halfOneAdd_neg hodd,
    mul_add, ← mul_assoc, hee, hff, hef, hfe, zero_mul, add_zero]
  rw [← add_mul, TauCeti.halfOneAdd_add_halfOneAdd_neg, one_mul]

variable (Q ω) in
/-- **The first component of the splitting**: `x ↦ ½ (1 + ω) x + ½ (1 - ω) x̂`, where `x̂` is the
grade involution of `x`. Together with `CliffordAlgebra.coe_equivEvenProd_apply_snd` this reads the
forward direction off the same idempotents the inverse is built from. -/
@[simp]
theorem coe_equivEvenProd_apply_fst
    (hcomm : ∀ x : ↥(even Q), Commute ω (x : CliffordAlgebra Q)) (hodd : ω ∈ evenOdd Q 1)
    (hsq : ω * ω = 1) (x : CliffordAlgebra Q) :
    ((equivEvenProd Q ω hcomm hodd hsq x).1 : CliffordAlgebra Q)
      = halfOneAdd R ω * x + halfOneAdd R (-ω) * involute x := by
  obtain ⟨p, rfl⟩ := (equivEvenProd Q ω hcomm hodd hsq).symm.surjective x
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
  rw [AlgEquiv.apply_symm_apply, equivEvenProd_symm_apply]
  exact (halfOneAdd_mul_add_halfOneAdd_neg_mul_involute hodd hsq
    (involute_eq_of_mem_even (by rw [← even_toSubmodule Q]; exact ha))
    (involute_eq_of_mem_even (by rw [← even_toSubmodule Q]; exact hb))).symm

variable (Q ω) in
/-- **The second component of the splitting**: `x ↦ ½ (1 - ω) x + ½ (1 + ω) x̂`, the first component
read at `-ω`. -/
@[simp]
theorem coe_equivEvenProd_apply_snd
    (hcomm : ∀ x : ↥(even Q), Commute ω (x : CliffordAlgebra Q)) (hodd : ω ∈ evenOdd Q 1)
    (hsq : ω * ω = 1) (x : CliffordAlgebra Q) :
    ((equivEvenProd Q ω hcomm hodd hsq x).2 : CliffordAlgebra Q)
      = halfOneAdd R (-ω) * x + halfOneAdd R ω * involute x := by
  obtain ⟨p, rfl⟩ := (equivEvenProd Q ω hcomm hodd hsq).symm.surjective x
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
  rw [AlgEquiv.apply_symm_apply, equivEvenProd_symm_apply]
  have h := halfOneAdd_mul_add_halfOneAdd_neg_mul_involute (R := R)
    (Submodule.neg_mem _ hodd) (by rw [neg_mul_neg]; exact hsq)
    (involute_eq_of_mem_even (by rw [← even_toSubmodule Q]; exact hb))
    (involute_eq_of_mem_even (by rw [← even_toSubmodule Q]; exact ha))
  rw [neg_neg, add_comm (halfOneAdd R (-ω) * b) (halfOneAdd R ω * a)] at h
  exact h.symm

end Splitting

/-! ### The volume element as the splitting element -/

variable [Invertible (2 : R)]

/-- **The odd-dimensional splitting, run on the volume element.** For a pairwise orthogonal list of
vectors spanning `M`, of odd length, whose volume element has been rescaled by `s` so as to square
to `1`, the Clifford algebra is the product of two copies of its even subalgebra.

The normalization hypothesis is exactly `(s ω)² = 1` read through
`CliffordAlgebra.prod_map_ι_sq_scalar`; it forces each `Q vᵢ` to be a unit, so it carries the
nondegeneracy the statement needs without naming it. -/
noncomputable def equivEvenProdOfOddLength {l : List M} (hl : l.Pairwise Q.IsOrtho)
    (hlen : Odd l.length) (hspan : Submodule.span R {x : M | x ∈ l} = ⊤) {s : R}
    (hs : s * s * ((-1 : R) ^ l.length.choose 2 * (l.map Q).prod) = 1) :
    CliffordAlgebra Q ≃ₐ[R] (↥(even Q) × ↥(even Q)) :=
  equivEvenProd Q (s • (l.map (ι Q)).prod)
    (fun x => (Subalgebra.mem_center_iff.mp
      (Subalgebra.smul_mem _ (prod_map_ι_mem_center_of_odd_length hl hlen hspan) s)
        (x : CliffordAlgebra Q)).symm)
    (Submodule.smul_mem _ s (prod_map_ι_mem_evenOdd_one_of_odd_length hlen))
    (by rw [smul_mul_assoc, mul_smul_comm, prod_map_ι_sq_scalar hl, smul_smul, Algebra.smul_def,
      ← map_mul, hs, map_one])

/-- The inverse of `CliffordAlgebra.equivEvenProdOfOddLength`, read off
`CliffordAlgebra.equivEvenProd_symm_apply` at the rescaled volume element. -/
@[simp]
theorem equivEvenProdOfOddLength_symm_apply {l : List M} (hl : l.Pairwise Q.IsOrtho)
    (hlen : Odd l.length) (hspan : Submodule.span R {x : M | x ∈ l} = ⊤) {s : R}
    (hs : s * s * ((-1 : R) ^ l.length.choose 2 * (l.map Q).prod) = 1)
    (p : ↥(even Q) × ↥(even Q)) :
    (equivEvenProdOfOddLength hl hlen hspan hs).symm p
      = halfOneAdd R (s • (l.map (ι Q)).prod) * (p.1 : CliffordAlgebra Q)
        + halfOneAdd R (-(s • (l.map (ι Q)).prod)) * (p.2 : CliffordAlgebra Q) :=
  equivEvenProd_symm_apply Q (s • (l.map (ι Q)).prod) _ _ _ p

/-- The first component of `CliffordAlgebra.equivEvenProdOfOddLength`, read off
`CliffordAlgebra.coe_equivEvenProd_apply_fst` at the rescaled volume element. -/
@[simp]
theorem coe_equivEvenProdOfOddLength_apply_fst {l : List M} (hl : l.Pairwise Q.IsOrtho)
    (hlen : Odd l.length) (hspan : Submodule.span R {x : M | x ∈ l} = ⊤) {s : R}
    (hs : s * s * ((-1 : R) ^ l.length.choose 2 * (l.map Q).prod) = 1) (x : CliffordAlgebra Q) :
    ((equivEvenProdOfOddLength hl hlen hspan hs x).1 : CliffordAlgebra Q)
      = halfOneAdd R (s • (l.map (ι Q)).prod) * x
        + halfOneAdd R (-(s • (l.map (ι Q)).prod)) * involute x :=
  coe_equivEvenProd_apply_fst Q (s • (l.map (ι Q)).prod) _ _ _ x

/-- The second component of `CliffordAlgebra.equivEvenProdOfOddLength`, read off
`CliffordAlgebra.coe_equivEvenProd_apply_snd` at the rescaled volume element. -/
@[simp]
theorem coe_equivEvenProdOfOddLength_apply_snd {l : List M} (hl : l.Pairwise Q.IsOrtho)
    (hlen : Odd l.length) (hspan : Submodule.span R {x : M | x ∈ l} = ⊤) {s : R}
    (hs : s * s * ((-1 : R) ^ l.length.choose 2 * (l.map Q).prod) = 1) (x : CliffordAlgebra Q) :
    ((equivEvenProdOfOddLength hl hlen hspan hs x).2 : CliffordAlgebra Q)
      = halfOneAdd R (-(s • (l.map (ι Q)).prod)) * x
        + halfOneAdd R (s • (l.map (ι Q)).prod) * involute x :=
  coe_equivEvenProd_apply_snd Q (s • (l.map (ι Q)).prod) _ _ _ x

/-- **Over a separably closed field of characteristic not two the normalization is automatic.**

An orthogonal spanning list of odd length with no isotropic member has a volume element whose
square is a nonzero scalar, and a separably closed field supplies its inverse square root, so the
Clifford algebra of such a form is the product of two copies of its even subalgebra. The square
root is only known to exist, so the conclusion is a `Nonempty`; fixing a root and applying
`CliffordAlgebra.equivEvenProdOfOddLength` names the isomorphism. This is the odd-dimensional half
of the structure theorem, up to the identification of the even subalgebra with a matrix algebra. -/
theorem nonempty_algEquiv_even_prod_of_isSepClosed {K V : Type*} [Field K] [IsSepClosed K]
    [AddCommGroup V] [Module K V] [NeZero (2 : K)] {Q : QuadraticForm K V} {l : List V}
    (hl : l.Pairwise Q.IsOrtho) (hlen : Odd l.length)
    (hspan : Submodule.span K {x : V | x ∈ l} = ⊤) (hQ : ∀ v ∈ l, Q v ≠ 0) :
    Nonempty (CliffordAlgebra Q ≃ₐ[K] (↥(even Q) × ↥(even Q))) := by
  have _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  set c : K := (-1 : K) ^ l.length.choose 2 * (l.map Q).prod
  have hprod : (l.map Q).prod ≠ 0 := by
    refine List.prod_ne_zero ?_
    rintro hmem
    obtain ⟨v, hv, hv0⟩ := List.mem_map.mp hmem
    exact hQ v hv hv0
  have hcne : c ≠ 0 := mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hprod
  obtain ⟨s, hsz⟩ := IsSepClosed.exists_eq_mul_self (k := K) c⁻¹
  exact ⟨equivEvenProdOfOddLength hl hlen hspan
    (s := s) (by rw [← hsz, inv_mul_cancel₀ hcne])⟩

end CliffordAlgebra
