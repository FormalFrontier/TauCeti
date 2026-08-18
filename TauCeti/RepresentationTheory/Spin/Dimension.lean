/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.HalfSpin
-- Private: `CliffordAlgebra.two_mul_finrank_evenOdd` and
-- `TauCeti.ExteriorAlgebra.finrank_eq_two_pow` are used only inside proofs, as is
-- `Subspace.dual_finrank_eq`; none is named by an exported statement.
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The dimensions of the spinor module and its half-spin summands

`TauCeti.spinRep` realizes the spinor module of a polarized quadratic space `(V, Q)` on the
exterior algebra `S = ⋀·W` of the isotropic summand `W` of the polarization, and
`TauCeti.spinPlus` and `TauCeti.spinMinus` cut it into its even and odd halves. This file counts
them.

The count of `S` itself is `TauCeti.ExteriorAlgebra.finrank_eq_two_pow`: `dim S = 2 ^ dim W`. The
count of the two halves is not a formality, because `⋀·W` is the Clifford algebra of the *zero*
form, where the classical argument — multiply by an anisotropic vector, which is odd and
invertible — has nothing to multiply by. The odd invertible operator is instead exterior
multiplication corrected by a contraction, and it is built in
`TauCeti/LinearAlgebra/CliffordAlgebra/ParitySwap.lean`; here it is only consumed, through
`CliffordAlgebra.two_mul_finrank_evenOdd`. So each half is exactly half of `S`, of dimension
`2 ^ (dim W - 1)` — the dimension of a half-spin representation.

The hypothesis `W ≠ ⊥` is real: for `W = 0` the spinor module is the ground field, sitting entirely
in the even half, and there is no half-spin splitting to speak of.

A polarization also fixes `dim W` in terms of `dim V`. The two isotropic summands are dual to each
other, so equidimensional (`TauCeti.SpinPolarizationData.finrank_W'`), and the third summand
embeds in the scalar line, so is at most a line
(`TauCeti.SpinPolarizationData.finrank_line_le_one`); hence
`dim V = 2 · dim W + dim line` with `dim line ≤ 1`, and the parity of `dim V` decides which. In
even dimension `2l` the line is absent and `dim W = l`, the type `Dₗ` case where the spinor module
splits into two half-spin summands of dimension `2 ^ (l - 1)`; in odd dimension `2l + 1` the line
is present and `dim W = l` again, the type `Bₗ` case, where the splitting is not one of
representations (see `TauCeti/RepresentationTheory/Spin/HalfSpin.lean`) and the spin module of
dimension `2 ^ l` is the one that matters.

## Main results

* `TauCeti.SpinPolarizationData.finrank_eq`: `dim V = 2 · dim W + dim line`, with
  `TauCeti.SpinPolarizationData.finrank_line_le_one` bounding the last summand by `1`.
* `TauCeti.SpinPolarizationData.finrank_W_of_finrank_eq_two_mul` and
  `TauCeti.SpinPolarizationData.finrank_W_of_finrank_eq_two_mul_add_one`: `dim W = l` in dimension
  `2l` and in dimension `2l + 1`.
* `TauCeti.finrank_spinPlus` and `TauCeti.finrank_spinMinus`: **each half-spin summand has
  dimension `2 ^ (dim W - 1)`.**

## Implementation notes

The polarization dimension count is stated here rather than with the polarization data itself
because it is the half-spin count that needs it, and because it is the first place a field and a
finite dimension are assumed: `TauCeti.SpinPolarizationData` is defined over a commutative ring
with no finiteness anywhere.

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
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)

namespace SpinPolarizationData

/-- **The two isotropic summands of a polarization are equidimensional**, because the polar form
identifies the second with the dual of the first. -/
theorem finrank_W' : finrank K P.W' = finrank K P.W :=
  P.pairingEquiv.finrank_eq.trans Subspace.dual_finrank_eq

/-- **The remainder of a polarization is at most a line**: it embeds into the ground field through
its coordinate. -/
theorem finrank_line_le_one : finrank K P.line ≤ 1 := by
  simpa using P.lineCoordinate.finrank_le_finrank_of_injective P.lineCoordinate_injective

variable [FiniteDimensional K V]

/-- **The dimension of a polarized quadratic space**: twice the dimension of the isotropic summand,
plus the dimension of the remainder — which is `0` or `1` by
`TauCeti.SpinPolarizationData.finrank_line_le_one`, so the parity of `finrank K V` decides which. -/
theorem finrank_eq : finrank K V = 2 * finrank K P.W + finrank K P.line := by
  have h := P.decompositionEquiv.finrank_eq
  rw [finrank_prod, finrank_prod, P.finrank_W'] at h
  omega

/-- In **even** dimension `2l` the remainder of a polarization is trivial and the isotropic summand
has dimension `l`. This is the type `Dₗ` case, where the spinor module `⋀·W` has dimension `2ˡ` by
`TauCeti.ExteriorAlgebra.finrank_eq_two_pow` and splits into two half-spin subrepresentations. -/
theorem finrank_W_of_finrank_eq_two_mul {l : ℕ} (hV : finrank K V = 2 * l) :
    finrank K P.W = l := by
  have h := P.finrank_eq
  have := P.finrank_line_le_one
  omega

/-- In **odd** dimension `2l + 1` the remainder of a polarization is a line and the isotropic
summand again has dimension `l`. This is the type `Bₗ` case, where the spinor module `⋀·W` has
dimension `2ˡ` and the parity splitting is not one of representations. -/
theorem finrank_W_of_finrank_eq_two_mul_add_one {l : ℕ} (hV : finrank K V = 2 * l + 1) :
    finrank K P.W = l := by
  have h := P.finrank_eq
  have := P.finrank_line_le_one
  omega

end SpinPolarizationData

variable [FiniteDimensional K V]

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
