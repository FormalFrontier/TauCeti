/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic

/-!
# The maximal elementary-2 quotient of a free abelian group

For a finite-rank free `ℤ`-module `A`, the multiplicative group `Multiplicative A` has maximal
elementary-2 quotient of cardinality `2 ^ rank`: squaring is doubling, and `A / 2A` is an
`𝔽₂`-vector space with basis the reduction of any `ℤ`-basis. Correspondingly the 2-rank of
`Multiplicative A` is exactly the `ℤ`-rank of `A`.

This is the free building block complementing the finite cyclic one of
`TauCeti.Algebra.Group.ElementaryTwoQuotient.Cyclic`: through a product decomposition of a
finitely generated abelian group, the two together compute its number of square classes. The
multiquadratic roadmap consumes this file through Dirichlet's unit theorem, whose free part
`Fin (rank) → ℤ` contributes `2 ^ rank` square classes of units.

The counting itself is Mathlib's `ModN.natCard_eq` (`|A/nA| = n ^ rank` for a free finite-rank
`ℤ`-module); this file transports it along the identification of `Additive (Multiplicative A)`
with `A`.

## Main results

* `TauCeti.card_elementaryTwoQuotient_multiplicative`:
  `|Multiplicative A / (Multiplicative A)²| = 2 ^ finrank ℤ A`, with the corresponding
  `Finite` instance (the group is infinite for positive rank, so the generic instance does not
  apply in general).
* `TauCeti.twoRank_multiplicative`: the 2-rank of `Multiplicative A` is `finrank ℤ A`.
-/

public section

namespace TauCeti

variable (A : Type*) [AddCommGroup A]

/-- The doubling submodule of `Additive (Multiplicative A)` corresponds to the doubling submodule
of `A` under the canonical identification, the compatibility fact needed to transport the `ModN`
model of the elementary-2 quotient. Kept private to the file. -/
private theorem map_range_lsmul_two_additiveMultiplicative :
    (LinearMap.range (LinearMap.lsmul ℤ (Additive (Multiplicative A)) ((2 : ℕ) : ℤ))).map
        ((AddEquiv.additiveMultiplicative A).toIntLinearEquiv :
          Additive (Multiplicative A) →ₗ[ℤ] A) =
      LinearMap.range (LinearMap.lsmul ℤ A ((2 : ℕ) : ℤ)) := by
  rw [← LinearMap.range_comp]
  have hcomp : ((AddEquiv.additiveMultiplicative A).toIntLinearEquiv :
        Additive (Multiplicative A) →ₗ[ℤ] A) ∘ₗ
          LinearMap.lsmul ℤ (Additive (Multiplicative A)) ((2 : ℕ) : ℤ) =
      LinearMap.lsmul ℤ A ((2 : ℕ) : ℤ) ∘ₗ
        ((AddEquiv.additiveMultiplicative A).toIntLinearEquiv :
          Additive (Multiplicative A) →ₗ[ℤ] A) := by
    ext x
    simp
  rw [hcomp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]

variable [Module.Free ℤ A] [Module.Finite ℤ A]

/-- **A finite-rank free abelian group has `2 ^ rank` square classes.** For a free `ℤ`-module `A`
of finite rank, the maximal elementary-2 quotient of `Multiplicative A` has cardinality
`2 ^ finrank ℤ A`. This is Mathlib's `ModN.natCard_eq` transported along the identification of
`Additive (Multiplicative A)` with `A`. -/
theorem card_elementaryTwoQuotient_multiplicative :
    Nat.card (ElementaryTwoQuotient (Multiplicative A)) = 2 ^ Module.finrank ℤ A := by
  calc
    Nat.card (ElementaryTwoQuotient (Multiplicative A))
        = Nat.card (ModN A 2) :=
          Nat.card_congr (Submodule.Quotient.equiv _ _
            (AddEquiv.additiveMultiplicative A).toIntLinearEquiv
            (map_range_lsmul_two_additiveMultiplicative A)).toEquiv
    _ = 2 ^ Module.finrank ℤ A := ModN.natCard_eq A 2

/-- The elementary-2 quotient of a finite-rank free abelian group is finite. The group is
infinite for positive rank, so the generic `Finite G → Finite (G/G²)` instance does not apply in
general; this instance lets consumers combine the free factor with the `twoRank`-level product and
divisibility lemmas. -/
instance : Finite (ElementaryTwoQuotient (Multiplicative A)) :=
  Nat.finite_of_card_ne_zero (by simp [card_elementaryTwoQuotient_multiplicative])

/-- The 2-rank of a finite-rank free abelian group is its rank:
`twoRank (Multiplicative A) = finrank ℤ A`. -/
theorem twoRank_multiplicative : twoRank (Multiplicative A) = Module.finrank ℤ A :=
  twoRank_eq_of_card_elementaryTwoQuotient_eq_two_pow _
    (card_elementaryTwoQuotient_multiplicative A)

end TauCeti
