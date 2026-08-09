/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Group.ElementaryTwoQuotient.Exact
public import TauCeti.NumberTheory.ClassGroup.ElementaryTwoQuotient
public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Finite
public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.TotallyComplex

/-!
# The elementary-2 quotient `Cl⁺(K)/Cl⁺(K)²` of the narrow class group

Genus theory computes a `2`-rank, and for a real quadratic field the rank it computes — the `t - 1`
of the roadmap, `t` the number of ramified primes — is the rank of the **narrow** class group
`Cl⁺(K)`, not of the ordinary one. This file attaches the maximal elementary-2 quotient
`Cl⁺(K)/Cl⁺(K)²` to the narrow class group of `TauCeti.NumberField.NarrowClassGroup`, and compares
it with the ordinary quotient `Cl(K)/Cl(K)²` of
`TauCeti.NumberTheory.ClassGroup.ElementaryTwoQuotient`.

The comparison is the right exactness of `G ↦ G/G²`
(`TauCeti.ker_elementaryTwoQuotientMap`) applied to the forgetful surjection
`Cl⁺(K) → Cl(K)`, whose kernel is the group of narrow classes of principal ideals
(`toClassGroup_ker`). It gives

`Cl⁺(K)/Cl⁺(K)² ↠ Cl(K)/Cl(K)²`,

with kernel the classes of the principal ideals `(u)`, `u : Kˣ`. Hence the ordinary `2`-rank never
exceeds the narrow one, and the gap between them is bounded by the `2`-rank of that kernel — which
is elementary abelian (`sq_eq_one_of_mem_ker_toClassGroup`), so that its order is exactly
`2 ^ twoRank`. For a totally complex field the kernel is trivial and the two ranks agree, which is
why the genus-theory `2`-rank formula can be stated for the ordinary class group in the imaginary
case and needs the narrow one in the real case.

⚠ As throughout, `Cl⁺(K)/Cl⁺(K)²` is the maximal elementary-2 **quotient**, not the 2-torsion
subgroup `Cl⁺(K)[2]`.

## Main results

In the namespace `TauCeti.NumberField.NarrowClassGroup`:

* `elementaryTwoQuotientMap_toClassGroup_surjective`: `Cl⁺(K)/Cl⁺(K)² ↠ Cl(K)/Cl(K)²`.
* `mem_ker_elementaryTwoQuotientMap_toClassGroup_iff`: its kernel consists of the classes of the
  principal ideals.
* `twoRank_classGroup_le_twoRank`: `twoRank Cl(K) ≤ twoRank Cl⁺(K)`.
* `twoRank_le_twoRank_classGroup_add_twoRank_ker`: `twoRank Cl⁺(K) ≤ twoRank Cl(K) + twoRank ker`.
* `card_ker_toClassGroup_eq_two_pow_twoRank`: the kernel has order `2 ^ twoRank`, being elementary
  abelian.
* `twoRank_eq_twoRank_classGroup_of_forall_isSquare`: the ranks agree once every principal narrow
  class is a square.
* `twoRank_eq_twoRank_classGroup` and `card_eq_classNumber`: for a totally complex field the two
  `2`-ranks agree, as do the two class numbers.
-/

public section

open NumberField
open scoped NumberField

namespace TauCeti.NumberField.NarrowClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- **Forgetting positivity is surjective on elementary-2 quotients.** The surjection
`Cl⁺(K) → Cl(K)` induces a surjection `Cl⁺(K)/Cl⁺(K)² → Cl(K)/Cl(K)²`. -/
theorem elementaryTwoQuotientMap_toClassGroup_surjective :
    Function.Surjective (TauCeti.elementaryTwoQuotientMap (toClassGroup (K := K))) :=
  TauCeti.elementaryTwoQuotientMap_surjective toClassGroup_surjective

/-- **The kernel of `Cl⁺(K)/Cl⁺(K)² → Cl(K)/Cl(K)²` is spanned by the principal classes.** A narrow
square class dies in `Cl(K)/Cl(K)²` exactly when it is the class of `mkPrincipal u` for some
`u : Kˣ` — that is, exactly when it comes from a principal ideal, whose narrow class is nontrivial
only because its generator need not be totally positive.

This is right exactness of `G ↦ G/G²` combined with the exactness of
`Kˣ → Cl⁺(K) → Cl(K) → 1` at `Cl⁺(K)`. -/
theorem mem_ker_elementaryTwoQuotientMap_toClassGroup_iff
    (x : TauCeti.ElementaryTwoQuotient (NarrowClassGroup K)) :
    x ∈ LinearMap.ker (TauCeti.elementaryTwoQuotientMap (toClassGroup (K := K))) ↔
      ∃ u : Kˣ, TauCeti.elementaryTwoQuotientMk (mkPrincipal u) = x := by
  rw [TauCeti.mem_ker_elementaryTwoQuotientMap_iff toClassGroup_surjective]
  constructor
  · rintro ⟨C, hC, rfl⟩
    rw [toClassGroup_ker] at hC
    obtain ⟨u, rfl⟩ := hC
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨mkPrincipal u, ?_, rfl⟩
    rw [toClassGroup_ker]
    exact ⟨u, rfl⟩

/-- **The ordinary `2`-rank never exceeds the narrow one.** Since `Cl⁺(K) ↠ Cl(K)`, the quotient
`Cl(K)/Cl(K)²` is a quotient of `Cl⁺(K)/Cl⁺(K)²`. -/
theorem twoRank_classGroup_le_twoRank :
    TauCeti.ClassGroup.twoRank (𝓞 K) ≤ TauCeti.twoRank (NarrowClassGroup K) :=
  TauCeti.twoRank_le_of_surjective toClassGroup_surjective

/-- **The narrow `2`-rank exceeds the ordinary one by at most the rank of the defect.** The kernel
of `Cl⁺(K) → Cl(K)` measures how far a principal ideal is from having a totally positive generator;
the narrow `2`-rank is at most the ordinary one plus the `2`-rank of that kernel. -/
theorem twoRank_le_twoRank_classGroup_add_twoRank_ker :
    TauCeti.twoRank (NarrowClassGroup K) ≤
      TauCeti.ClassGroup.twoRank (𝓞 K) +
        TauCeti.twoRank (MonoidHom.ker (toClassGroup (K := K))) :=
  TauCeti.twoRank_le_twoRank_add_twoRank_ker toClassGroup_surjective

/-- **The narrow-versus-ordinary defect has order `2 ^ twoRank`.** The kernel of `Cl⁺(K) → Cl(K)` is
an elementary abelian `2`-group (`sq_eq_one_of_mem_ker_toClassGroup`), so it coincides with its own
elementary-2 quotient. -/
theorem card_ker_toClassGroup_eq_two_pow_twoRank :
    Nat.card (MonoidHom.ker (toClassGroup (K := K))) =
      2 ^ TauCeti.twoRank (MonoidHom.ker (toClassGroup (K := K))) :=
  TauCeti.card_eq_two_pow_twoRank_of_forall_sq_eq_one _ fun C =>
    Subtype.ext (sq_eq_one_of_mem_ker_toClassGroup C.2)

/-- **The `2`-ranks agree as soon as every principal narrow class is a square.** The narrow-versus-
ordinary defect is carried by the classes `mkPrincipal u` of principal ideals; if each of those is
already a square in `Cl⁺(K)`, then `Cl⁺(K)/Cl⁺(K)² → Cl(K)/Cl(K)²` is an isomorphism. -/
theorem twoRank_eq_twoRank_classGroup_of_forall_isSquare
    (h : ∀ u : Kˣ, IsSquare (mkPrincipal (K := K) u)) :
    TauCeti.twoRank (NarrowClassGroup K) = TauCeti.ClassGroup.twoRank (𝓞 K) := by
  refine TauCeti.twoRank_eq_of_forall_isSquare_of_mem_ker toClassGroup_surjective ?_
  intro C hC
  rw [toClassGroup_ker] at hC
  obtain ⟨u, rfl⟩ := hC
  exact h u

/-- **For a totally complex field the narrow and ordinary `2`-ranks agree**, because the narrow and
ordinary class groups themselves agree (`toClassGroupEquiv`). This is why the genus-theory `2`-rank
formula may be stated for `Cl(K)` in the imaginary quadratic case, while the real case genuinely
needs `Cl⁺(K)`. -/
theorem twoRank_eq_twoRank_classGroup [IsTotallyComplex K] :
    TauCeti.twoRank (NarrowClassGroup K) = TauCeti.ClassGroup.twoRank (𝓞 K) :=
  TauCeti.twoRank_eq_of_mulEquiv _ toClassGroupEquiv

/-- **For a totally complex field the narrow class number is the class number.** The companion of
`twoRank_eq_twoRank_classGroup` at the level of orders. -/
theorem card_eq_classNumber [IsTotallyComplex K] :
    Nat.card (NarrowClassGroup K) = NumberField.classNumber K := by
  rw [NumberField.classNumber, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr toClassGroupEquiv.toEquiv

end TauCeti.NumberField.NarrowClassGroup
