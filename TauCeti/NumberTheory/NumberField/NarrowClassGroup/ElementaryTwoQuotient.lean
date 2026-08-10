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
`2 ^ TauCeti.twoRank (ker (Cl⁺(K) → Cl(K)))`. For a totally complex field the kernel is trivial and
the two ranks agree, which is why the genus-theory `2`-rank formula can be stated for the ordinary
class group in the imaginary case and needs the narrow one in the real case.

⚠ As throughout, `Cl⁺(K)/Cl⁺(K)²` is the maximal elementary-2 **quotient**, not the 2-torsion
subgroup `Cl⁺(K)[2]`.

## Main results

In the namespace `TauCeti.NumberField.NarrowClassGroup`:

* `ElementaryTwoQuotient` and `twoRank`: the quotient `Cl⁺(K)/Cl⁺(K)²` and its `𝔽₂`-dimension,
  abbreviations for the general `TauCeti.ElementaryTwoQuotient` and `TauCeti.twoRank` of
  `NarrowClassGroup K`, so that the general API applies to them unchanged.
* `elementaryTwoQuotientMapToClassGroup` and `elementaryTwoQuotientMapToClassGroup_eq_zero_iff`:
  the induced map to the ordinary quotient and its kernel of principal classes.
* `classGroupTwoRank_le_twoRank`: `twoRank Cl(K) ≤ twoRank Cl⁺(K)`.
* `twoRank_le_classGroupTwoRank_add_twoRank_ker`: `twoRank Cl⁺(K) ≤ twoRank Cl(K) + twoRank ker`.
* `card_ker_toClassGroup_eq_two_pow_twoRank_ker`: the kernel of `Cl⁺(K) → Cl(K)` has order
  `2 ^ TauCeti.twoRank (ker (Cl⁺(K) → Cl(K)))`, being elementary abelian.
* `twoRank_eq_classGroupTwoRank_of_forall_isSquare_mkPrincipal`: the ranks agree once every
  principal narrow class is a square.
* `twoRank_eq_classGroupTwoRank`: for a totally complex field the two `2`-ranks agree.
-/

public section

open NumberField
open scoped NumberField

namespace TauCeti.NumberField.NarrowClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- **The maximal elementary-2 quotient `Cl⁺(K)/Cl⁺(K)²` of the narrow class group.** -/
abbrev ElementaryTwoQuotient (K : Type*) [Field K] [NumberField K] : Type _ :=
  TauCeti.ElementaryTwoQuotient (NarrowClassGroup K)

/-- **The 2-rank of the narrow class group**: the `ZMod 2` dimension of `Cl⁺(K)/Cl⁺(K)²`. -/
noncomputable abbrev twoRank (K : Type*) [Field K] [NumberField K] : ℕ :=
  TauCeti.twoRank (NarrowClassGroup K)

/-- The map `Cl⁺(K)/Cl⁺(K)² → Cl(K)/Cl(K)²` induced by forgetting positivity. -/
@[expose] noncomputable def elementaryTwoQuotientMapToClassGroup :
    ElementaryTwoQuotient K →ₗ[ZMod 2] TauCeti.ClassGroup.ElementaryTwoQuotient (𝓞 K) :=
  TauCeti.elementaryTwoQuotientMap (toClassGroup (K := K))

/-- The induced map `Cl⁺(K)/Cl⁺(K)² → Cl(K)/Cl(K)²` is the general induced map of
`toClassGroup`. -/
theorem elementaryTwoQuotientMapToClassGroup_def :
    elementaryTwoQuotientMapToClassGroup (K := K) =
      TauCeti.elementaryTwoQuotientMap (toClassGroup (K := K)) :=
  rfl

/-- The induced map to `Cl(K)/Cl(K)²` sends a narrow ideal class to its ordinary ideal class. -/
@[simp] theorem elementaryTwoQuotientMapToClassGroup_mk (C : NarrowClassGroup K) :
    elementaryTwoQuotientMapToClassGroup (TauCeti.elementaryTwoQuotientMk C) =
      TauCeti.elementaryTwoQuotientMk C.toClassGroup := by
  rw [elementaryTwoQuotientMapToClassGroup_def, TauCeti.elementaryTwoQuotientMap_mk]

/-- **The kernel of `Cl⁺(K)/Cl⁺(K)² → Cl(K)/Cl(K)²` is spanned by the principal classes.** A narrow
square class dies in `Cl(K)/Cl(K)²` exactly when it is the class of `mkPrincipal u` for some
`u : Kˣ` — that is, exactly when it comes from a principal ideal, whose narrow class is nontrivial
only because its generator need not be totally positive. -/
@[simp] theorem elementaryTwoQuotientMapToClassGroup_eq_zero_iff (x : ElementaryTwoQuotient K) :
    elementaryTwoQuotientMapToClassGroup x = 0 ↔
      ∃ u : Kˣ, TauCeti.elementaryTwoQuotientMk (mkPrincipal u) = x := by
  rw [elementaryTwoQuotientMapToClassGroup_def,
    TauCeti.elementaryTwoQuotientMap_eq_zero_iff toClassGroup_surjective]
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
theorem classGroupTwoRank_le_twoRank :
    TauCeti.ClassGroup.twoRank (𝓞 K) ≤ twoRank K := by
  rw [TauCeti.ClassGroup.twoRank_def]
  exact TauCeti.twoRank_le_twoRank_of_surjective toClassGroup_surjective

/-- **The narrow `2`-rank exceeds the ordinary one by at most the rank of the defect.** The kernel
of `Cl⁺(K) → Cl(K)` measures how far a principal ideal is from having a totally positive generator;
the narrow `2`-rank is at most the ordinary one plus the `2`-rank of that kernel. -/
theorem twoRank_le_classGroupTwoRank_add_twoRank_ker :
    twoRank K ≤
      TauCeti.ClassGroup.twoRank (𝓞 K) +
        TauCeti.twoRank (MonoidHom.ker (toClassGroup (K := K))) := by
  rw [TauCeti.ClassGroup.twoRank_def]
  exact TauCeti.twoRank_le_twoRank_add_twoRank_ker toClassGroup_surjective

/-- **The narrow-versus-ordinary defect has order `2 ^ TauCeti.twoRank (ker (Cl⁺(K) → Cl(K)))`.**
The kernel of `Cl⁺(K) → Cl(K)` is an elementary abelian `2`-group
(`sq_eq_one_of_mem_ker_toClassGroup`), so it has the same cardinality as its own elementary-2
quotient. -/
theorem card_ker_toClassGroup_eq_two_pow_twoRank_ker :
    Nat.card (MonoidHom.ker (toClassGroup (K := K))) =
      2 ^ TauCeti.twoRank (MonoidHom.ker (toClassGroup (K := K))) :=
  TauCeti.card_eq_two_pow_twoRank_of_forall_sq_eq_one _ fun C =>
    Subtype.ext <| by
      rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      exact sq_eq_one_of_mem_ker_toClassGroup C.2

/-- **The `2`-ranks agree as soon as every principal narrow class is a square.** The narrow-versus-
ordinary defect is carried by the classes `mkPrincipal u` of principal ideals; if each of those is
already a square in `Cl⁺(K)`, then `Cl⁺(K)/Cl⁺(K)² → Cl(K)/Cl(K)²` is an isomorphism. -/
theorem twoRank_eq_classGroupTwoRank_of_forall_isSquare_mkPrincipal
    (h : ∀ u : Kˣ, IsSquare (mkPrincipal (K := K) u)) :
    twoRank K = TauCeti.ClassGroup.twoRank (𝓞 K) := by
  rw [TauCeti.ClassGroup.twoRank_def]
  refine TauCeti.twoRank_eq_of_forall_isSquare_of_mem_ker toClassGroup_surjective ?_
  intro C hC
  rw [toClassGroup_ker] at hC
  obtain ⟨u, rfl⟩ := hC
  exact h u

/-- **For a totally complex field the narrow and ordinary `2`-ranks agree**, because the narrow and
ordinary class groups themselves agree (`toClassGroupEquiv`). This is why the genus-theory `2`-rank
formula may be stated for `Cl(K)` in the imaginary quadratic case, while the real case genuinely
needs `Cl⁺(K)`. -/
theorem twoRank_eq_classGroupTwoRank [IsTotallyComplex K] :
    twoRank K = TauCeti.ClassGroup.twoRank (𝓞 K) := by
  rw [TauCeti.ClassGroup.twoRank_def]
  exact TauCeti.twoRank_eq_of_mulEquiv _ toClassGroupEquiv

end TauCeti.NumberField.NarrowClassGroup
