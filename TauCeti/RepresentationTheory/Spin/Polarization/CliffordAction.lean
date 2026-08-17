/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# The spinor module of a polarized quadratic space

A polarization of a quadratic space `(V, Q)` splits it as `W ⊕ W' ⊕ L`, with `W` and `W'`
isotropic and in perfect `QuadraticMap.polar`-pairing and `L` an orthogonal remainder carried by a
scalar coordinate. This file turns the exterior algebra `⋀·W` into a module over the Clifford
algebra of `Q` — the Fock model of the spinor representation. Classically, over `ℂ`, it is the
carrier of the spin and half-spin representations, which no tensor power of `V` contains; that
statement belongs to the complex theory and is not proved here.

The three summands act by three visibly different operators on `S = ⋀·W`:

* a vector of `W` acts by exterior multiplication (`TauCeti.SpinPolarizationData.wedge`), a
  *creation* operator;
* a vector of `W'` acts by contraction against the functional `QuadraticMap.polar Q · y` that the
  polarization pairing attaches to it (`TauCeti.SpinPolarizationData.contract`), an
  *annihilation* operator;
* a vector of the remainder acts by its scalar coordinate times the grade involution, or *parity*
  operator, of `⋀·W` (`TauCeti.SpinPolarizationData.lineOperator`), which supplies the extra
  generator in odd dimension.

Assembled into one linear map `TauCeti.SpinPolarizationData.cliffordOperator`, these satisfy the
Clifford relation, and the universal property then produces the algebra homomorphism
`TauCeti.spinAction`. The coefficient in the relation is not a prose "twice": the
computation of `TauCeti.SpinPolarizationData.cliffordOperator_sq` runs through
`QuadraticMap.polar`, which enters through the creation–annihilation anticommutator
`TauCeti.SpinPolarizationData.contract_wedge` and through nothing else.

The exterior algebra is Mathlib's `ExteriorAlgebra K W`, which *is*
`CliffordAlgebra (0 : QuadraticForm K W)`, so the interior product is the zero-form
specialization of `CliffordAlgebra.contractLeft` and the parity operator is the zero-form
specialization of `CliffordAlgebra.involute`; there is no bespoke exterior-algebra vocabulary
here. Everything holds over an arbitrary commutative ring, since
`TauCeti.SpinPolarizationData` already carries the isotropy and pairing that the relation needs;
no invertibility of `2` is used.

Surjectivity of `TauCeti.spinAction` onto `Module.End K S` when `P.W` is finite free, and its
restriction to `pinGroup Q` and `spinGroup Q`, are in
`TauCeti/RepresentationTheory/Spin/Representation.lean`; the half-spin summands are in
`TauCeti/RepresentationTheory/Spin/HalfSpin.lean`.

## Main definitions

* `TauCeti.SpinPolarizationData.wedge`, `TauCeti.SpinPolarizationData.contract`,
  `TauCeti.SpinPolarizationData.lineOperator`: the three component operators on `⋀·W`.
* `TauCeti.SpinPolarizationData.cliffordOperator`: the operator `c v` on `⋀·W` attached to a
  vector `v` of `V`, assembled from them.
* `TauCeti.spinAction`: the resulting `CliffordAlgebra Q`-module structure on `⋀·W`.

## Main results

* `TauCeti.SpinPolarizationData.cliffordOperator_coe_W`,
  `TauCeti.SpinPolarizationData.cliffordOperator_coe_W'` and
  `TauCeti.SpinPolarizationData.cliffordOperator_coe_line`: the operator of a vector of a single
  summand, in terms of the component operator of that summand.
* `TauCeti.SpinPolarizationData.contract_wedge`: the only anticommutation relation between the
  component operators that is not zero, and the one carrying the polarization pairing.
* `TauCeti.SpinPolarizationData.cliffordOperator_sq`: the Clifford relation `c v ∘ c v = Q v • 1`.
* `TauCeti.spinAction_ι_wedge`, `TauCeti.spinAction_ι_contract` and
  `TauCeti.spinAction_ι_lineOperator`: the three summands act by exterior multiplication,
  contraction, and the parity operator.

## References

* [Spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 4, "The Clifford module `S = ⋀·W`".
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti

universe u v

namespace SpinPolarizationData

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)

/-- **The creation operator**: a vector of the isotropic summand `W` acts on `⋀·W` by exterior
multiplication. -/
noncomputable def wedge : P.W →ₗ[K] Module.End K (ExteriorAlgebra K P.W) :=
  (LinearMap.mul K (ExteriorAlgebra K P.W)).comp (ExteriorAlgebra.ι K)

@[simp, grind =]
theorem wedge_apply (x : P.W) (s : ExteriorAlgebra K P.W) :
    P.wedge x s = ExteriorAlgebra.ι K x * s :=
  -- `(rfl)`, not `rfl`: the body of `wedge` is not `@[expose]`d.
  (rfl)

/-- **The annihilation operator**: a vector `y` of the second isotropic summand `W'` acts on `⋀·W`
by contraction against the functional `x ↦ polar Q x y` that the polarization pairing attaches to
it. -/
noncomputable def contract : P.W' →ₗ[K] Module.End K (ExteriorAlgebra K P.W) :=
  (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K P.W))).comp
    P.pairingEquiv.toLinearMap

@[simp, grind =]
theorem contract_apply (y : P.W') (s : ExteriorAlgebra K P.W) :
    P.contract y s = CliffordAlgebra.contractLeft (P.pairingEquiv y) s :=
  -- `(rfl)`, not `rfl`: the body of `contract` is not `@[expose]`d.
  (rfl)

/-- **The parity operator**: a vector of the orthogonal remainder acts on `⋀·W` by its scalar
coordinate times the grade involution `CliffordAlgebra.involute` of the exterior algebra. The
involution anticommutes with both the creation and the annihilation operators, and the
scalar coordinate is the normalization that makes the square of this operator `Q z`. -/
noncomputable def lineOperator : P.line →ₗ[K] Module.End K (ExteriorAlgebra K P.W) :=
  (LinearMap.toSpanSingleton K (Module.End K (ExteriorAlgebra K P.W))
    (CliffordAlgebra.involute (Q := (0 : QuadraticForm K P.W))).toLinearMap).comp
    P.lineCoordinate

@[simp, grind =]
theorem lineOperator_apply (z : P.line) (s : ExteriorAlgebra K P.W) :
    P.lineOperator z s = P.lineCoordinate z • CliffordAlgebra.involute s :=
  -- `(rfl)`, not `rfl`: the body of `lineOperator` is not `@[expose]`d.
  (rfl)

/-- **The Clifford operator** of a vector: the assembly of the creation, annihilation and parity
operators along the polarization coordinates. -/
noncomputable def cliffordOperator : V →ₗ[K] Module.End K (ExteriorAlgebra K P.W) :=
  ((P.wedge.coprod P.contract).coprod P.lineOperator).comp
    P.decompositionEquiv.symm.toLinearMap

/-- On the isotropic summand `W` the Clifford operator is the creation operator. -/
@[simp, grind =]
theorem cliffordOperator_coe_W (x : P.W) : P.cliffordOperator (x : V) = P.wedge x := by
  simp [cliffordOperator]

/-- On the second isotropic summand `W'` the Clifford operator is the annihilation operator. -/
@[simp, grind =]
theorem cliffordOperator_coe_W' (y : P.W') : P.cliffordOperator (y : V) = P.contract y := by
  simp [cliffordOperator]

/-- On the orthogonal remainder the Clifford operator is the scaled parity operator. -/
@[simp, grind =]
theorem cliffordOperator_coe_line (z : P.line) : P.cliffordOperator (z : V) = P.lineOperator z := by
  simp [cliffordOperator]

/-! ### The squares and the anticommutators of the component operators

Expanding the Clifford relation in polarization coordinates produces six terms: the squares of
the three component operators, and the three anticommutators between distinct ones. Five are
statements about a single Clifford algebra and come from elsewhere. The two isotropic squares
vanish — `ExteriorAlgebra.ι_sq_zero` for creation and
`CliffordAlgebra.contractLeft_contractLeft` for annihilation — whereas the parity square does not:
it is the identity, by `CliffordAlgebra.involute_involute`, which is what makes the remainder
coordinate contribute `Q z` rather than `0`. Parity anticommutes with each of the other two, by
`CliffordAlgebra.involute_ι` through `map_mul` and by
`TauCeti.CliffordAlgebra.involute_contractLeft`. The sixth term, the creation–annihilation
anticommutator, is the only one that sees the polarization and the only nonzero one among the
three; it is recorded here. -/

/-- **Creation and annihilation anticommute up to the pairing**: this is the one anticommutator
that is not zero, and the scalar it produces is the polar form of the two vectors. It is what pins
the coefficient of the Clifford relation to `QuadraticMap.polar`. -/
@[grind =]
theorem contract_wedge (x : P.W) (y : P.W') (s : ExteriorAlgebra K P.W) :
    P.contract y (P.wedge x s) =
      polar Q (x : V) (y : V) • s - P.wedge x (P.contract y s) := by
  rw [contract_apply, wedge_apply, CliffordAlgebra.contractLeft_ι_mul, P.pairingEquiv_apply,
    wedge_apply, contract_apply]

/-- The quadratic form of a vector in polarization coordinates: both isotropic summands drop out
and the remainder is orthogonal to them, so only the pairing term and the remainder survive. -/
@[simp, grind =]
theorem quadraticForm_coe_add_coe_add_coe (x : P.W) (y : P.W') (z : P.line) :
    Q ((x : V) + (y : V) + (z : V)) = polar Q (x : V) (y : V) + Q (z : V) := by
  have hxz : polar Q (x : V) (z : V) = 0 := by
    rw [polar_comm]
    exact P.line_orthogonal_W z x
  have hyz : polar Q (y : V) (z : V) = 0 := by
    rw [polar_comm]
    exact P.line_orthogonal_W' z y
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, P.isotropic_W, P.isotropic_W',
    polar_add_left, hxz, hyz]
  ring

/-- **The Clifford relation for the spinor operators**: squaring the operator of a vector `v`
returns the scalar `Q v`. The three cross terms are exactly the three anticommutators — creation
against annihilation contributes the pairing, and parity against each of the other two cancels —
so the coefficient is read off `QuadraticMap.polar`, not assumed. -/
theorem cliffordOperator_sq (v : V) :
    P.cliffordOperator v * P.cliffordOperator v
      = algebraMap K (Module.End K (ExteriorAlgebra K P.W)) (Q v) := by
  obtain ⟨c, rfl⟩ := P.decompositionEquiv.surjective v
  obtain ⟨⟨x, y⟩, z⟩ := c
  rw [P.decompositionEquiv_apply]
  have hc : P.cliffordOperator ((x : V) + (y : V) + (z : V))
      = P.wedge x + P.contract y + P.lineOperator z := by
    simp only [map_add, P.cliffordOperator_coe_W, P.cliffordOperator_coe_W',
      P.cliffordOperator_coe_line]
  rw [hc, P.quadraticForm_coe_add_coe_add_coe, ← P.lineCoordinate_sq z]
  ext s
  simp only [Module.End.mul_apply, LinearMap.add_apply, Module.algebraMap_end_apply,
    wedge_apply, contract_apply, lineOperator_apply, map_add, map_smul, mul_add,
    ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul,
    CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_contractLeft,
    map_mul, CliffordAlgebra.involute_ι, neg_mul,
    TauCeti.CliffordAlgebra.involute_contractLeft,
    CliffordAlgebra.involute_involute, P.pairingEquiv_apply]
  module

end SpinPolarizationData

/-- **The spinor representation of the Clifford algebra**: `CliffordAlgebra Q` acts on the
exterior algebra `S = ⋀·W` of the isotropic summand of a polarization, by exterior multiplication
for `W`, by contraction against the polar pairing for `W'`, and by a multiple of the parity
operator for the orthogonal remainder.

This is the Fock model of the spin module. Classically — over an algebraically closed field of
characteristic different from `2`, with `Q` nondegenerate and finite-dimensional — it is an
isomorphism onto `Module.End K S` in even dimension, and in odd dimension it factors through one
of the two central-idempotent summands of the Clifford algebra; neither statement is proved
here, and neither is claimed at the generality of this definition. -/
noncomputable def spinAction {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (P : SpinPolarizationData Q) :
    CliffordAlgebra Q →ₐ[K] Module.End K (ExteriorAlgebra K P.W) :=
  CliffordAlgebra.lift Q ⟨P.cliffordOperator, P.cliffordOperator_sq⟩

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)

@[simp, grind =]
theorem spinAction_ι (v : V) :
    spinAction Q P (CliffordAlgebra.ι Q v) = P.cliffordOperator v :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-- A vector of the isotropic summand `W` acts on the spin module by exterior multiplication. -/
theorem spinAction_ι_wedge (x : P.W) (s : ExteriorAlgebra K P.W) :
    spinAction Q P (CliffordAlgebra.ι Q x) s = ExteriorAlgebra.ι K x * s := by
  rw [spinAction_ι, P.cliffordOperator_coe_W, P.wedge_apply]

/-- A vector of the second isotropic summand `W'` acts on the spin module by contraction against
the functional the polarization pairing attaches to it. -/
theorem spinAction_ι_contract (y : P.W') (s : ExteriorAlgebra K P.W) :
    spinAction Q P (CliffordAlgebra.ι Q y) s =
      CliffordAlgebra.contractLeft (P.pairingEquiv y) s := by
  rw [spinAction_ι, P.cliffordOperator_coe_W', P.contract_apply]

/-- A vector of the orthogonal remainder acts on the spin module by its scalar coordinate times
the parity operator. -/
theorem spinAction_ι_lineOperator (z : P.line) (s : ExteriorAlgebra K P.W) :
    spinAction Q P (CliffordAlgebra.ι Q z) s =
      P.lineCoordinate z • CliffordAlgebra.involute s := by
  rw [spinAction_ι, P.cliffordOperator_coe_line, P.lineOperator_apply]

end TauCeti
