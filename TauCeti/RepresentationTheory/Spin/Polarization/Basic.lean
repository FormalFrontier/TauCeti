/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical

-- Private: `Subspace.dual_finrank_eq`, `Module.finrank_prod` and
-- `LinearMap.finrank_le_finrank_of_injective` occur only inside the proofs of the dimension
-- count; none is named by an exported statement.
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Polarization data for quadratic spaces

This file packages the decomposition used to construct spinor modules: two isotropic subspaces
in a left- and right-nondegenerate polar pairing and an orthogonal remainder embedded in the
scalar line. It also records the two elementary consequences that every consumer needs: the polar
form vanishes identically on each isotropic summand, and a basis of the first summand has a
Kronecker-dual family of vectors in the second.

Over a field the decomposition also counts dimensions: the two isotropic summands are dual to each
other, so equidimensional, and the remainder embeds in the scalar line, so is at most a line.
Hence `dim V = 2 · dim W + dim line` with `dim line ≤ 1`, and the parity of `dim V` decides which,
giving `dim W = l` both in dimension `2l` (type `Dₗ`) and in dimension `2l + 1` (type `Bₗ`).

## Main definitions

* `TauCeti.SpinPolarizationData` records the decomposition and its consumer-facing coordinates.
* `TauCeti.SpinPolarizationData.dualVector`: given a basis of the first isotropic summand, the
  vector of the second summand matching a coordinate functional of that basis.
* `TauCeti.SpinPolarizationData.dualBasis`: the resulting basis of the second isotropic summand.

## Main results

* `TauCeti.SpinPolarizationData.polar_W_eq_zero` and
  `TauCeti.SpinPolarizationData.polar_W'_eq_zero`: the polar form vanishes on each isotropic
  summand.
* `TauCeti.SpinPolarizationData.polar_dualVector`: the dual vectors pair with the chosen basis by
  the Kronecker delta.
* `TauCeti.SpinPolarizationData.dualBasis_apply`: the dual basis has `dualVector` as its underlying
  family.
* `TauCeti.SpinPolarizationData.finrank_eq_two_mul_finrank_W_add_finrank_line` and
  `TauCeti.SpinPolarizationData.finrank_line_le_one` give the dimension bookkeeping of a
  finite-dimensional polarization.
* `TauCeti.SpinPolarizationData.line_eq_bot_of_even_finrank` and
  `TauCeti.SpinPolarizationData.finrank_W_of_finrank_eq_two_mul` are its even-dimensional
  consequences.
* `TauCeti.SpinPolarizationData.finrank_W_of_finrank_eq_two_mul_add_one` and
  `TauCeti.SpinPolarizationData.finrank_line_eq_one_of_finrank_eq_two_mul_add_one` are its
  odd-dimensional consequences: the isotropic summand again has dimension `l`, and the remainder
  is exactly a line.
* `TauCeti.SpinPolarizationData.nondegenerate` and
  `TauCeti.SpinPolarizationData.nondegenerate_of_line_eq_bot`: a polarized quadratic form is
  nondegenerate, as soon as `2` is a regular scalar of a reduced ring in general and
  unconditionally when there is no remainder.

## References

* [Tau Ceti Roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), Representation Theory /
  Spin Representations, Layer 4, "The spin module".
-/

public section

namespace TauCeti

universe u v

/-- The decomposition data used by the exterior model of a spin representation. -/
@[ext]
structure SpinPolarizationData {K : Type u} [CommRing K] {V : Type v}
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) where
  /-- The isotropic subspace used for exterior multiplication. -/
  W : Submodule K V
  /-- The complementary isotropic subspace used for contraction. -/
  W' : Submodule K V
  /-- The orthogonal remainder, embedded in the scalar line by `lineCoordinate`. -/
  line : Submodule K V
  /-- The direct-sum coordinates of the quadratic space. -/
  decompositionEquiv : ((W × W') × line) ≃ₗ[K] V
  /-- The decomposition equivalence adds the three components in the ambient module. -/
  decompositionEquiv_apply :
    ∀ x, decompositionEquiv x = (x.1.1 : V) + x.1.2 + x.2
  /-- The first summand is isotropic. -/
  isotropic_W : ∀ x : W, Q x = 0
  /-- The second summand is isotropic. -/
  isotropic_W' : ∀ y : W', Q y = 0
  /-- The polar form identifies the second summand with the dual of the first. -/
  pairingEquiv : W' ≃ₗ[K] Module.Dual K W
  /-- The pairing equivalence is evaluation by the polar form. -/
  pairingEquiv_apply :
    ∀ (y : W') (x : W), pairingEquiv y x = QuadraticMap.polar Q x y
  /-- The polar pairing has trivial left radical. -/
  pairing_separatingLeft :
    ∀ x : W, (∀ y : W', QuadraticMap.polar Q x y = 0) → x = 0
  /-- The coordinate on the at-most-one-dimensional remainder. -/
  lineCoordinate : line →ₗ[K] K
  /-- The remainder embeds in the scalar line through its coordinate. -/
  lineCoordinate_injective : Function.Injective lineCoordinate
  /-- The quadratic form on the remainder is the square of its coordinate. -/
  lineCoordinate_sq : ∀ z : line, lineCoordinate z * lineCoordinate z = Q z
  /-- The remainder is orthogonal to the first isotropic summand. -/
  line_orthogonal_W :
    ∀ z : line, ∀ x : W, QuadraticMap.polar Q z x = 0
  /-- The remainder is orthogonal to the second isotropic summand. -/
  line_orthogonal_W' :
    ∀ z : line, ∀ y : W', QuadraticMap.polar Q z y = 0

attribute [simp, grind =] SpinPolarizationData.decompositionEquiv_apply
  SpinPolarizationData.isotropic_W SpinPolarizationData.isotropic_W'
  SpinPolarizationData.pairingEquiv_apply SpinPolarizationData.lineCoordinate_sq
  SpinPolarizationData.line_orthogonal_W SpinPolarizationData.line_orthogonal_W'

namespace SpinPolarizationData

/-- Recover the three components of a vector assembled from polarization coordinates. -/
@[simp, grind =]
theorem decompositionEquiv_symm_apply {K : Type u} [CommRing K] {V : Type v}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
    (x : P.W) (y : P.W') (z : P.line) :
    P.decompositionEquiv.symm ((x : V) + (y : V) + (z : V)) = ((x, y), z) := by
  apply P.decompositionEquiv.injective
  rw [P.decompositionEquiv.apply_symm_apply, P.decompositionEquiv_apply]

/-- A vector of the first isotropic summand has only that coordinate. -/
@[simp, grind =]
theorem decompositionEquiv_symm_coe_W {K : Type u} [CommRing K] {V : Type v}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
    (x : P.W) : P.decompositionEquiv.symm (x : V) = ((x, 0), 0) := by
  simpa using P.decompositionEquiv_symm_apply x 0 0

/-- A vector of the second isotropic summand has only that coordinate. -/
@[simp, grind =]
theorem decompositionEquiv_symm_coe_W' {K : Type u} [CommRing K] {V : Type v}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
    (y : P.W') : P.decompositionEquiv.symm (y : V) = ((0, y), 0) := by
  simpa using P.decompositionEquiv_symm_apply 0 y 0

/-- A vector of the orthogonal remainder has only that coordinate. -/
@[simp, grind =]
theorem decompositionEquiv_symm_coe_line {K : Type u} [CommRing K] {V : Type v}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
    (z : P.line) : P.decompositionEquiv.symm (z : V) = ((0, 0), z) := by
  simpa using P.decompositionEquiv_symm_apply 0 0 z

/-- The polar pairing has trivial right radical. -/
theorem pairing_separatingRight {K : Type u} [CommRing K] {V : Type v}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
    (y : P.W') (hy : ∀ x : P.W, QuadraticMap.polar Q x y = 0) : y = 0 := by
  apply P.pairingEquiv.injective
  ext x
  simp only [P.pairingEquiv_apply, hy x, map_zero, LinearMap.zero_apply]

section Isotropic

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)

/-! ### The polar form vanishes on each isotropic summand -/

/-- The polar form vanishes on the first isotropic summand of a polarization: that summand is
isotropic and closed under addition. -/
theorem polar_W_eq_zero (x y : P.W) : QuadraticMap.polar Q (x : V) (y : V) = 0 := by
  have h : Q ((x : V) + (y : V)) = 0 := by simpa using P.isotropic_W (x + y)
  simp [QuadraticMap.polar, h]

/-- The polar form vanishes on the second isotropic summand of a polarization. -/
theorem polar_W'_eq_zero (x y : P.W') : QuadraticMap.polar Q (x : V) (y : V) = 0 := by
  have h : Q ((x : V) + (y : V)) = 0 := by simpa using P.isotropic_W' (x + y)
  simp [QuadraticMap.polar, h]

/-! ### The dual isotropic vectors of a basis -/

variable {ι : Type*} [DecidableEq ι] (b : Module.Basis ι K P.W)

/-- The vector of the second isotropic summand `W'` dual to the `i`-th basis vector of `W`: the
polarization pairing identifies `W'` with the dual of `W`, and this is the vector matching the
`i`-th coordinate functional. -/
noncomputable def dualVector (i : ι) : P.W' :=
  P.pairingEquiv.symm (b.coord i)

omit [DecidableEq ι] in
@[simp]
theorem pairingEquiv_dualVector (i : ι) : P.pairingEquiv (P.dualVector b i) = b.coord i :=
  P.pairingEquiv.apply_symm_apply _

section DualBasis

variable [Finite ι]

/-- The basis of the second isotropic summand dual to `b` under the polarization pairing. -/
noncomputable def dualBasis : Module.Basis ι K P.W' :=
  b.dualBasis.map P.pairingEquiv.symm

@[simp]
theorem dualBasis_apply (i : ι) : P.dualBasis b i = P.dualVector b i := by
  rw [dualBasis, Module.Basis.map_apply]
  apply P.pairingEquiv.injective
  rw [P.pairingEquiv.apply_symm_apply, P.pairingEquiv_dualVector]
  exact congrFun b.coe_dualBasis i

end DualBasis

/-- The dual vectors pair with the basis of `W` by the Kronecker delta. -/
@[simp]
theorem polar_dualVector (i j : ι) :
    QuadraticMap.polar Q (b j : V) (P.dualVector b i : V) = if j = i then 1 else 0 := by
  rw [← P.pairingEquiv_apply (P.dualVector b i) (b j), pairingEquiv_dualVector]
  simp [Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]

omit [DecidableEq ι] in
/-- A basis vector of `W` pairs with its own dual vector to `1`. -/
theorem polar_dualVector_self (i : ι) :
    QuadraticMap.polar Q (b i : V) (P.dualVector b i : V) = 1 := by
  classical
  simp

end Isotropic

/-- **A vector orthogonal to the whole space lies in the orthogonal remainder.** The polar pairing
separates each isotropic summand from the other, and the remainder is orthogonal to both, so the
two isotropic coordinates of such a vector vanish and only its remainder coordinate survives. -/
private theorem mem_line_of_polarBilin_eq_zero {K : Type u} [CommRing K] {V : Type v}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (P : SpinPolarizationData Q) {v : V} (hv : Q.polarBilin v = 0) : v ∈ P.line := by
  let x := (P.decompositionEquiv.symm v).1.1
  let y := (P.decompositionEquiv.symm v).1.2
  let z := (P.decompositionEquiv.symm v).2
  have hdecomp : (x : V) + (y : V) + (z : V) = v := by
    rw [← P.decompositionEquiv_apply]
    exact P.decompositionEquiv.apply_symm_apply v
  have hWW (a b : P.W) : QuadraticMap.polar Q (a : V) b = 0 := P.polar_W_eq_zero a b
  have hW'W' (a b : P.W') : QuadraticMap.polar Q (a : V) b = 0 := P.polar_W'_eq_zero a b
  have hx : x = 0 := by
    apply P.pairing_separatingLeft
    intro b
    have h := LinearMap.congr_fun hv (b : V)
    simpa only [QuadraticMap.polarBilin_apply_apply, ← hdecomp,
      QuadraticMap.polar_add_left, hW'W', P.line_orthogonal_W', LinearMap.zero_apply,
      add_zero] using h
  have hy : y = 0 := by
    apply P.pairing_separatingRight
    intro a
    have h := LinearMap.congr_fun hv (a : V)
    simpa only [QuadraticMap.polarBilin_apply_apply, ← hdecomp,
      QuadraticMap.polar_add_left, hWW, P.line_orthogonal_W, LinearMap.zero_apply,
      add_zero, zero_add, QuadraticMap.polar_comm Q y a] using h
  rw [← hdecomp, hx, hy]
  simp

/-- A quadratic form whose polar form has trivial kernel is nondegenerate. -/
private theorem nondegenerate_of_ker_polarBilin_eq_bot {K : Type u} [CommRing K] {V : Type v}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (hker : Q.polarBilin.ker = ⊥) :
    Q.Nondegenerate := by
  refine ⟨le_antisymm (Q.radical_le_ker_polarBilin.trans hker.le) bot_le, ?_⟩
  rw [hker]
  nontriviality K
  simp only [rank_subsingleton', zero_le]

/-- A polarization without an orthogonal remainder has nondegenerate quadratic form. -/
theorem nondegenerate_of_line_eq_bot {K : Type u} [CommRing K] {V : Type v}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (P : SpinPolarizationData Q) (hline : P.line = ⊥) : Q.Nondegenerate := by
  refine nondegenerate_of_ker_polarBilin_eq_bot (LinearMap.ker_eq_bot'.2 fun v hv => ?_)
  simpa [hline] using P.mem_line_of_polarBilin_eq_zero hv

/-- **A polarization has nondegenerate quadratic form**, whatever its orthogonal remainder, as soon
as `2` is a regular scalar and the base ring is reduced.

A vector orthogonal to everything lies in the remainder, where the polar form is `2 Q` and `Q` is
the square of the injective coordinate `SpinPolarizationData.lineCoordinate`; both hypotheses are
needed to run that back — cancelling the `2` only asks it to be regular, not invertible, and the
square only has to vanish for a square-zero scalar, which is all a reduced ring is asked for. When
the remainder vanishes the same conclusion is available with neither hypothesis, from the separate
`TauCeti.SpinPolarizationData.nondegenerate_of_line_eq_bot`; this theorem is what makes
nondegeneracy redundant as a hypothesis alongside polarization data in general. -/
theorem nondegenerate {K : Type u} [CommRing K] [IsReduced K]
    {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (P : SpinPolarizationData Q) (h2 : IsSMulRegular K (2 : K)) : Q.Nondegenerate := by
  refine nondegenerate_of_ker_polarBilin_eq_bot (LinearMap.ker_eq_bot'.2 fun v hv => ?_)
  let z : P.line := ⟨v, P.mem_line_of_polarBilin_eq_zero hv⟩
  have hQz : Q v = 0 := by
    refine h2.right_eq_zero_of_smul ?_
    simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self,
      LinearMap.zero_apply, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul] using
      LinearMap.congr_fun hv v
  have hcoord : P.lineCoordinate z = 0 := by
    have h : P.lineCoordinate z ^ 2 = 0 := by
      rw [pow_two, P.lineCoordinate_sq]
      exact hQz
    exact eq_zero_of_pow_eq_zero h
  exact congrArg Subtype.val (P.lineCoordinate_injective (by simpa using hcoord) :
    z = (0 : P.line))

section Dimension

open Module

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)

/-! ### The dimensions of the three summands

A polarization is a decomposition `V = W ⊕ W' ⊕ L` in which the polar form pairs `W` with `W'`
perfectly and `L` sits inside the scalar line. The first fact makes the two isotropic summands
equidimensional and the second bounds the remainder by one dimension, so the dimension of `V`
determines the dimension of `W` up to the parity of `finrank V`. -/

/-- **The two isotropic summands of a polarization have the same dimension.** The polar form
identifies the second with the dual of the first, and a space and its dual have the same
dimension. -/
theorem finrank_W'_eq_finrank_W : finrank K P.W' = finrank K P.W := by
  rw [P.pairingEquiv.finrank_eq, Subspace.dual_finrank_eq]

/-- **The orthogonal remainder of a polarization is at most a line.** Its scalar coordinate
`SpinPolarizationData.lineCoordinate` is injective into `K`, which is one-dimensional. -/
theorem finrank_line_le_one : finrank K P.line ≤ 1 := by
  have h := LinearMap.finrank_le_finrank_of_injective (f := P.lineCoordinate)
    P.lineCoordinate_injective
  simpa using h

variable [FiniteDimensional K V]

/-- **The dimension of a polarized quadratic space**: twice the dimension of the isotropic summand
`W`, plus the dimension of the remainder. Together with `finrank_line_le_one` this pins
`finrank W` to `finrank V / 2`. -/
theorem finrank_eq_two_mul_finrank_W_add_finrank_line :
    finrank K V = 2 * finrank K P.W + finrank K P.line := by
  rw [← P.decompositionEquiv.finrank_eq, finrank_prod, finrank_prod, P.finrank_W'_eq_finrank_W]
  ring

/-- **In even dimension a polarization has no remainder.** The remainder is at most a line and
carries the parity of `finrank V`, so an even-dimensional space forces it to vanish. This is the
hypothesis under which the exterior parity of `⋀·W` splits the spin representation, in
`TauCeti/RepresentationTheory/Spin/HalfSpin.lean`. -/
theorem line_eq_bot_of_even_finrank (h : Even (finrank K V)) : P.line = ⊥ := by
  obtain ⟨m, hm⟩ := h
  have h₁ := P.finrank_line_le_one
  have h₂ := P.finrank_eq_two_mul_finrank_W_add_finrank_line
  exact Submodule.finrank_eq_zero.1 (by omega)

/-- **A polarization with no remainder has even dimension.** The two isotropic summands are
equidimensional, so with the remainder gone the dimension is twice that of `W`. This is the
converse of `SpinPolarizationData.line_eq_bot_of_even_finrank`, and it is what lets the
even-dimensional theory be stated with the single hypothesis `P.line = ⊥` that the parity
splitting of the spinor module needs. -/
theorem even_finrank_of_line_eq_bot (hline : P.line = ⊥) : Even (finrank K V) := by
  have h := P.finrank_eq_two_mul_finrank_W_add_finrank_line
  rw [hline, finrank_bot] at h
  exact ⟨finrank K P.W, by omega⟩

/-- **In even dimension the isotropic summand has half the dimension.** The isotropic summand `W`
of a polarization of a `2l`-dimensional space has dimension `l`. This is the type `Dₗ` case, where
the spinor module `⋀·W` has dimension `2ˡ`. -/
theorem finrank_W_of_finrank_eq_two_mul {l : ℕ} (hV : finrank K V = 2 * l) :
    finrank K P.W = l := by
  have h₁ := P.finrank_line_le_one
  have h₂ := P.finrank_eq_two_mul_finrank_W_add_finrank_line
  omega

/-- **In odd dimension the isotropic summand again has half the dimension, rounded down.** The
isotropic summand `W` of a polarization of a `2l + 1`-dimensional space has dimension `l`, the odd
dimension being taken up by the remainder. This is the type `Bₗ` case, where the spinor module
`⋀·W` again has dimension `2ˡ` but the parity splitting is not one of representations. -/
theorem finrank_W_of_finrank_eq_two_mul_add_one {l : ℕ} (hV : finrank K V = 2 * l + 1) :
    finrank K P.W = l := by
  have h₁ := P.finrank_line_le_one
  have h₂ := P.finrank_eq_two_mul_finrank_W_add_finrank_line
  omega

/-- **In odd dimension the remainder is exactly a line.** It is at most a line by
`SpinPolarizationData.finrank_line_le_one`, and the two isotropic summands, being equidimensional,
take up an even dimension, so an odd-dimensional space leaves the remainder no alternative. It is
the line spanned by an anisotropic vector, whose action mixes the two exterior parities of the
spinor module — which is why they are not subrepresentations in the type `Bₗ` case. -/
theorem finrank_line_eq_one_of_finrank_eq_two_mul_add_one {l : ℕ} (hV : finrank K V = 2 * l + 1) :
    finrank K P.line = 1 := by
  have h₁ := P.finrank_line_le_one
  have h₂ := P.finrank_eq_two_mul_finrank_W_add_finrank_line
  omega

end Dimension

end SpinPolarizationData

end TauCeti
