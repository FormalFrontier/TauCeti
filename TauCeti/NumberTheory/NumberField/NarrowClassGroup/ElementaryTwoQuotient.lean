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

* `ElementaryTwoQuotient`, `elementaryTwoQuotientMk`, and `twoRank`: the quotient
  `Cl⁺(K)/Cl⁺(K)²`, its constructor, and its `𝔽₂`-dimension.
* `ElementaryTwoQuotient.toClassGroup` and `mem_ker_toClassGroup_iff`: the induced map to the
  ordinary quotient and its kernel of principal classes.
* `twoRank_classGroup_le_twoRank`: `twoRank Cl(K) ≤ twoRank Cl⁺(K)`.
* `twoRank_le_twoRank_classGroup_add_twoRank_ker`: `twoRank Cl⁺(K) ≤ twoRank Cl(K) + twoRank ker`.
* `card_ker_toClassGroup_eq_two_pow_twoRank`: the kernel has order `2 ^ twoRank`, being elementary
  abelian.
* `twoRank_eq_twoRank_classGroup_of_forall_isSquare`: the ranks agree once every principal narrow
  class is a square.
* `twoRank_eq_twoRank_classGroup`: for a totally complex field the two `2`-ranks agree.
-/

public section

open NumberField
open scoped NumberField

namespace TauCeti.NumberField.NarrowClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- **The maximal elementary-2 quotient `Cl⁺(K)/Cl⁺(K)²` of the narrow class group.** -/
abbrev ElementaryTwoQuotient (K : Type*) [Field K] [NumberField K] : Type _ :=
  TauCeti.ElementaryTwoQuotient (NarrowClassGroup K)

/-- The class of a narrow ideal class in the maximal elementary-2 quotient `Cl⁺(K)/Cl⁺(K)²`. -/
@[expose] noncomputable def elementaryTwoQuotientMk
    (C : NarrowClassGroup K) : ElementaryTwoQuotient K :=
  TauCeti.elementaryTwoQuotientMk C

/-- A narrow ideal class has trivial class in `Cl⁺(K)/Cl⁺(K)²` iff it is a square. -/
@[simp] theorem elementaryTwoQuotientMk_eq_zero_iff (C : NarrowClassGroup K) :
    elementaryTwoQuotientMk C = 0 ↔ IsSquare C :=
  TauCeti.elementaryTwoQuotientMk_eq_zero_iff C

namespace ElementaryTwoQuotient

/-- The map `Cl⁺(K)/Cl⁺(K)² → Cl(K)/Cl(K)²` induced by forgetting positivity. -/
@[expose] noncomputable def toClassGroup :
    ElementaryTwoQuotient K →ₗ[ZMod 2] TauCeti.ClassGroup.ElementaryTwoQuotient (𝓞 K) :=
  TauCeti.elementaryTwoQuotientMap (NarrowClassGroup.toClassGroup (K := K))

/-- The induced map `Cl⁺(K)/Cl⁺(K)² → Cl(K)/Cl(K)²` is surjective. -/
theorem toClassGroup_surjective : Function.Surjective (toClassGroup (K := K)) :=
  TauCeti.elementaryTwoQuotientMap_surjective NarrowClassGroup.toClassGroup_surjective

end ElementaryTwoQuotient

/-- **The 2-rank of the narrow class group**: the `ZMod 2` dimension of
`Cl⁺(K)/Cl⁺(K)²`. -/
noncomputable def twoRank (K : Type*) [Field K] [NumberField K] : ℕ :=
  TauCeti.twoRank (NarrowClassGroup K)

/-- The 2-rank of the narrow class group is the `ZMod 2` dimension of its maximal elementary-2
quotient. -/
@[simp] theorem twoRank_def :
    twoRank K = Module.finrank (ZMod 2) (ElementaryTwoQuotient K) :=
  TauCeti.twoRank_def (NarrowClassGroup K)

/-- **The kernel of `Cl⁺(K)/Cl⁺(K)² → Cl(K)/Cl(K)²` is spanned by the principal classes.** A narrow
square class dies in `Cl(K)/Cl(K)²` exactly when it is the class of `mkPrincipal u` for some
`u : Kˣ` — that is, exactly when it comes from a principal ideal, whose narrow class is nontrivial
only because its generator need not be totally positive. -/
theorem mem_ker_toClassGroup_iff (x : ElementaryTwoQuotient K) :
    x ∈ LinearMap.ker ElementaryTwoQuotient.toClassGroup ↔
      ∃ u : Kˣ, elementaryTwoQuotientMk (mkPrincipal u) = x := by
  have hmap : ElementaryTwoQuotient.toClassGroup (K := K) =
      TauCeti.elementaryTwoQuotientMap (NarrowClassGroup.toClassGroup (K := K)) := rfl
  rw [hmap, LinearMap.mem_ker,
    TauCeti.mem_ker_elementaryTwoQuotientMap_iff toClassGroup_surjective]
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
    TauCeti.ClassGroup.twoRank (𝓞 K) ≤ twoRank K := by
  rw [TauCeti.ClassGroup.twoRank_def, twoRank_def]
  exact TauCeti.twoRank_le_of_surjective toClassGroup_surjective

/-- **The narrow `2`-rank exceeds the ordinary one by at most the rank of the defect.** The kernel
of `Cl⁺(K) → Cl(K)` measures how far a principal ideal is from having a totally positive generator;
the narrow `2`-rank is at most the ordinary one plus the `2`-rank of that kernel. -/
theorem twoRank_le_twoRank_classGroup_add_twoRank_ker :
    twoRank K ≤
      TauCeti.ClassGroup.twoRank (𝓞 K) +
        TauCeti.twoRank (MonoidHom.ker (toClassGroup (K := K))) := by
  rw [twoRank_def, TauCeti.ClassGroup.twoRank_def]
  exact TauCeti.twoRank_le_twoRank_add_twoRank_ker toClassGroup_surjective

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
    twoRank K = TauCeti.ClassGroup.twoRank (𝓞 K) := by
  rw [twoRank_def, TauCeti.ClassGroup.twoRank_def]
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
    twoRank K = TauCeti.ClassGroup.twoRank (𝓞 K) := by
  rw [twoRank_def, TauCeti.ClassGroup.twoRank_def]
  exact TauCeti.twoRank_eq_of_mulEquiv _ toClassGroupEquiv

end TauCeti.NumberField.NarrowClassGroup
