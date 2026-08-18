/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.HalfSpin
-- Private: `CliffordAlgebra.two_mul_finrank_evenOdd` and
-- `TauCeti.ExteriorAlgebra.finrank_eq_two_pow` are used only inside proofs; neither is named by
-- an exported statement.
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension

/-!
# The dimensions of the spinor module and its half-spin summands

`TauCeti.spinRep` realizes the spinor module of a polarized quadratic space `(V, Q)` on the
exterior algebra `S = ⋀·W` of the isotropic summand `W` of the polarization, and
`TauCeti.spinPlus` and `TauCeti.spinMinus` cut it into its even and odd halves. This file counts
them.

The count of `S` itself is `TauCeti.finrank_spinRep`: `dim S = 2 ^ dim W`, the exterior-algebra
count `TauCeti.ExteriorAlgebra.finrank_eq_two_pow` read on the module `⋀·W` that carries the spin
representation. The count of the two halves is not a formality, because `⋀·W` is the Clifford
algebra of the *zero* form, where the classical argument — multiply by an anisotropic vector,
which is odd and invertible — has nothing to multiply by. The odd invertible operator is instead
exterior multiplication corrected by a contraction, and it is built in
`TauCeti/LinearAlgebra/CliffordAlgebra/ParitySwap.lean`; here it is only consumed, through
`CliffordAlgebra.two_mul_finrank_evenOdd`. So each half is exactly half of `S`, of dimension
`2 ^ (dim W - 1)` — the dimension of a half-spin representation.

The hypothesis `W ≠ ⊥` is real: for `W = 0` the spinor module is the ground field, sitting entirely
in the even half, and there is no half-spin splitting to speak of.

A polarization also fixes `dim W` in terms of `dim V`, by the dimension count that comes with the
polarization data itself (`TauCeti/RepresentationTheory/Spin/Polarization/Basic.lean`): `dim W = l`
both in even dimension `2l`, the type `Dₗ` case where the spinor module splits into two half-spin
summands of dimension `2 ^ (l - 1)`, and in odd dimension `2l + 1`, the type `Bₗ` case, where the
splitting is not one of representations (see `TauCeti/RepresentationTheory/Spin/HalfSpin.lean`) and
the spin module of dimension `2 ^ l` is the one that matters.

## Main results

* `TauCeti.finrank_spinRep`: **the spinor module has dimension `2 ^ dim W`.**
* `TauCeti.finrank_spinPlus` and `TauCeti.finrank_spinMinus`: **each half-spin summand has
  dimension `2 ^ (dim W - 1)`.**

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1: the spin module
  `S = ⋀·W` of dimension `2ˡ` and its half-spin summands `S⁺`, `S⁻` of dimension `2ˡ⁻¹`.
* [Spin-representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 5, "The half-spin representation of `𝔰𝔬(2l)` has dimension `2^{l-1}`".
-/

public section

open Module CliffordAlgebra

namespace TauCeti

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q) [FiniteDimensional K P.W]

/-- **The spinor module has dimension `2 ^ dim W`.**

The module carrying `TauCeti.spinRep` is the exterior algebra `⋀·W` of the isotropic summand, so
this is `TauCeti.ExteriorAlgebra.finrank_eq_two_pow` for `W`; it is stated here in terms of the
dimension `l` of `W`, which a polarization ties to `dim V` by
`TauCeti.SpinPolarizationData.finrank_W_of_finrank_eq_two_mul` in dimension `2l` and by
`TauCeti.SpinPolarizationData.finrank_W_of_finrank_eq_two_mul_add_one` in dimension `2l + 1`. So
the spinor module of a `2l`- or `(2l + 1)`-dimensional space has dimension `2 ^ l`. -/
theorem finrank_spinRep (l : ℕ) (hW : finrank K P.W = l) :
    finrank K (ExteriorAlgebra K P.W) = 2 ^ l := by
  rw [ExteriorAlgebra.finrank_eq_two_pow, hW]

/-- The shared content of `TauCeti.finrank_spinPlus` and `TauCeti.finrank_spinMinus`: each parity
half of the spinor module `⋀·W` is half of it, of dimension `2 ^ (dim W - 1)`.

The exterior algebra is the Clifford algebra of the zero form, so the halving is *not* the
classical argument by an anisotropic vector; it is `CliffordAlgebra.two_mul_finrank_evenOdd`,
which multiplies by a vector and corrects by a contraction. -/
private theorem finrank_evenOdd_exteriorAlgebra_W (hW : P.W ≠ ⊥) (i : ZMod 2) :
    finrank K (evenOdd (0 : QuadraticForm K P.W) i) = 2 ^ (finrank K P.W - 1) := by
  have : Nontrivial P.W := Submodule.nontrivial_iff_ne_bot.2 hW
  have hpos : 0 < finrank K P.W := Module.finrank_pos
  refine Nat.eq_of_mul_eq_mul_left two_pos ?_
  rw [two_mul_finrank_evenOdd, ExteriorAlgebra.finrank_eq_two_pow, ← pow_succ',
    Nat.sub_add_cancel hpos]

/-- **The even half-spin summand has dimension `2 ^ (dim W - 1)`.**

Half the dimension `2 ^ dim W` of the spinor module `⋀·W`, so `2 ^ (l - 1)` for a polarization of
a `2l`-dimensional space, where `dim W = l` by
`TauCeti.SpinPolarizationData.finrank_W_of_finrank_eq_two_mul`. The hypothesis `W ≠ ⊥` rules out
the degenerate case `⋀·W = K`, which is entirely even. -/
theorem finrank_spinPlus (hW : P.W ≠ ⊥) :
    finrank K (spinPlus Q P) = 2 ^ (finrank K P.W - 1) := by
  rw [spinPlus_def]
  exact finrank_evenOdd_exteriorAlgebra_W P hW 0

/-- **The odd half-spin summand has dimension `2 ^ (dim W - 1)`**, the same as the even one:
`TauCeti.finrank_spinPlus` for the other parity. -/
theorem finrank_spinMinus (hW : P.W ≠ ⊥) :
    finrank K (spinMinus Q P) = 2 ^ (finrank K P.W - 1) := by
  rw [spinMinus_def]
  exact finrank_evenOdd_exteriorAlgebra_W P hW 1

end TauCeti
