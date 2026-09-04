/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Finrank

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# The dimension of the Vinberg `ℤ/3`-model of split `E₈`

Vinberg's `ℤ/3`-graded construction of the split exceptional Lie algebra `E₈` puts

`𝔢₈ = 𝔰𝔩₉ ⊕ ⋀³(K⁹) ⊕ ⋀³(K⁹)^*`,

with the degree-zero piece acting on the two exterior summands and the graded bracket pairing them
back into `𝔰𝔩₉`. This file checks the dimension arithmetic that the construction has to satisfy:
the three summands have dimensions `80`, `84` and `84`, so the carrier is `248`-dimensional, the
dimension of `E₈`.

The three inputs are `TauCeti.finrank_sl` for `𝔰𝔩₉`, Mathlib's `exteriorPower.finrank_eq` (which
gives `(dim K⁹).choose 3 = 84`) for `⋀³(K⁹)`, and `Module.finrank_linearMap_self` for the dual
summand. The `84` is a numeric instance of `exteriorPower.finrank_eq` rather than a piece of general
exterior-power theory, so it lives here beside the count that consumes it. The direct sum of three
summands is spelled as an iterated product, the form `Module.finrank_prod` computes with. All three
summands are finite free, so no field is needed anywhere: a nontrivial commutative ring does.

**What is not proved here.** Only the underlying `K`-module is treated: the graded bracket, the
Jacobi identity for it, Killing-simplicity of type `E₈`, and the comparison with Mathlib's
Serre-construction `LieAlgebra.e₈` are all separate statements and none of them is proved here. A
`248`-dimensional module is of course not by itself `E₈`; the point of the count is that it is the
arithmetic obstruction the construction must clear.

## Main results

* `TauCeti.finrank_exteriorPower_three_nine`: `⋀³(K⁹)` is `84`-dimensional.
* `TauCeti.finrank_sl_fin_nine`: `𝔰𝔩₉` is `80`-dimensional.
* `TauCeti.finrank_prod_sl_exteriorPower_dual`: `𝔰𝔩₉ ⊕ ⋀³(K⁹) ⊕ ⋀³(K⁹)^*` is `248`-dimensional.

## References

* È. B. Vinberg, *The Weyl group of a graded Lie algebra*, Izv. Akad. Nauk SSSR 40 (1976).
* J. C. Baez, *The octonions*, Bull. Amer. Math. Soc. 39 (2002), §4.6, for the `ℤ/3`-model of `E₈`.
-/

public section

namespace TauCeti

open Module LieAlgebra

/-- **`⋀³(K⁹)` is `84`-dimensional**, `84` being `9.choose 3`: the exterior cube of a free module
of rank `9`. This is the summand of the Vinberg `ℤ/3`-model of split `E₈` that appears twice, once
as itself and once as its dual. -/
theorem finrank_exteriorPower_three_nine (K : Type*) [CommRing K] [Nontrivial K] :
    finrank K (⋀[K]^3 (Fin 9 → K)) = 84 := by
  rw [exteriorPower.finrank_eq, Module.finrank_fin_fun]
  decide

/-- **`𝔰𝔩₉` is `80`-dimensional**, the degree-zero summand of the Vinberg `ℤ/3`-model of split
`E₈`. Like the exterior cube above, this needs no more than a commutative ring in which `finrank`
counts basis vectors. -/
theorem finrank_sl_fin_nine (K : Type*) [CommRing K] [StrongRankCondition K] :
    finrank K (SpecialLinear.sl (Fin 9) K) = 80 := by
  rw [finrank_sl, Fintype.card_fin]
  decide

/-- **The Vinberg `ℤ/3`-model of split `E₈` is `248`-dimensional**:
`finrank (𝔰𝔩₉ ⊕ ⋀³(K⁹) ⊕ ⋀³(K⁹)^*) = 80 + 84 + 84 = 248`.

Only the `K`-module is at issue; the graded Lie bracket that makes the sum `E₈` is not built
here. Like the two summand counts this needs no more than a nontrivial commutative ring: the dual
summand is finite free of the same rank as `⋀³(K⁹)` by `Module.finrank_linearMap_self`. -/
theorem finrank_prod_sl_exteriorPower_dual (K : Type*) [CommRing K] [Nontrivial K] :
    finrank K (SpecialLinear.sl (Fin 9) K ×
        ⋀[K]^3 (Fin 9 → K) × Dual K (⋀[K]^3 (Fin 9 → K))) = 248 := by
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_linearMap_self,
    finrank_sl_fin_nine, finrank_exteriorPower_three_nine]

end TauCeti
