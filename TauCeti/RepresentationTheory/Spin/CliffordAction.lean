/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
algebra of `Q` — the Fock model of the spinor representation, and the carrier of the spin and
half-spin representations, which no tensor power of `V` contains.

The three summands act by three visibly different operators on `S = ⋀·W`:

* a vector of `W` acts by exterior multiplication (`TauCeti.SpinPolarizationData.wedge`), a
  *creation* operator;
* a vector of `W'` acts by contraction against the functional `QuadraticMap.polar Q · y` that the
  polarization pairing attaches to it (`TauCeti.SpinPolarizationData.contract`), an
  *annihilation* operator;
* a vector of the remainder acts by its scalar coordinate times the grade involution
  (`TauCeti.SpinPolarizationData.parity`), the operator that supplies the extra anticommuting
  generator in odd dimension.

Assembled into one linear map `TauCeti.SpinPolarizationData.cliffordOperator`, these satisfy the
Clifford relation, and the universal property then produces the algebra homomorphism
`TauCeti.spinAction`. The coefficient in the relation is not a prose "twice": the
computation of `TauCeti.SpinPolarizationData.cliffordOperator_sq` runs through
`QuadraticMap.polar`, and the polarized form
`TauCeti.spinAction_ι_mul_add_swap` records the anticommutator
`c x ∘ c y + c y ∘ c x = polar Q x y • 1` that pins it.

The exterior algebra is Mathlib's `ExteriorAlgebra K W`, which *is*
`CliffordAlgebra (0 : QuadraticForm K W)`, so the interior product is the zero-form
specialization of `CliffordAlgebra.contractLeft` and the parity operator is the zero-form
specialization of `CliffordAlgebra.involute`; there is no bespoke exterior-algebra vocabulary
here. Everything holds over an arbitrary commutative ring, since
`TauCeti.SpinPolarizationData` already carries the isotropy and pairing that the relation needs;
no invertibility of `2` is used.

Surjectivity of `TauCeti.spinAction` onto `Module.End K S` in even dimension, the restriction to
`spinGroup Q`, and the half-spin summands are not proved here.

## Main definitions

* `TauCeti.SpinPolarizationData.wedge`, `TauCeti.SpinPolarizationData.contract`,
  `TauCeti.SpinPolarizationData.parity`: the three component operators on `⋀·W`.
* `TauCeti.SpinPolarizationData.cliffordOperator`: the operator `c v` on `⋀·W` attached to a
  vector `v` of `V`, assembled from them.
* `TauCeti.spinAction`: the resulting `CliffordAlgebra Q`-module structure on `⋀·W`.

## Main results

* `TauCeti.SpinPolarizationData.contract_wedge`, `TauCeti.SpinPolarizationData.parity_wedge` and
  `TauCeti.SpinPolarizationData.parity_contract`: the anticommutation relations between the
  component operators.
* `TauCeti.SpinPolarizationData.cliffordOperator_sq`: the Clifford relation `c v ∘ c v = Q v • 1`.
* `TauCeti.spinAction_ι_wedge`, `TauCeti.spinAction_ι_contract`, `TauCeti.spinAction_ι_parity`:
  the three summands act by exterior multiplication, contraction, and the parity operator.
* `TauCeti.spinAction_ι_mul_add_swap`: the anticommutator identity pinning the coefficient to
  `QuadraticMap.polar`.

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

@[simp]
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

@[simp]
theorem contract_apply (y : P.W') (s : ExteriorAlgebra K P.W) :
    P.contract y s = CliffordAlgebra.contractLeft (P.pairingEquiv y) s :=
  -- `(rfl)`, not `rfl`: the body of `contract` is not `@[expose]`d.
  (rfl)

/-- **The parity operator** on `⋀·W`, the grade involution of the exterior algebra. It anticommutes
with both the creation and the annihilation operators, which is what lets an anisotropic vector
orthogonal to the polarization act by a multiple of it. -/
noncomputable def parity : Module.End K (ExteriorAlgebra K P.W) :=
  (CliffordAlgebra.involute (Q := (0 : QuadraticForm K P.W))).toLinearMap

@[simp]
theorem parity_apply (s : ExteriorAlgebra K P.W) : P.parity s = CliffordAlgebra.involute s :=
  -- `(rfl)`, not `rfl`: the body of `parity` is not `@[expose]`d.
  (rfl)

/-- A vector of the orthogonal remainder acts by its scalar coordinate times the parity
operator, the normalization that makes its square the scalar `Q z`. -/
noncomputable def lineOperator : P.line →ₗ[K] Module.End K (ExteriorAlgebra K P.W) :=
  (LinearMap.toSpanSingleton K (Module.End K (ExteriorAlgebra K P.W)) P.parity).comp
    P.lineCoordinate

@[simp]
theorem lineOperator_apply (z : P.line) (s : ExteriorAlgebra K P.W) :
    P.lineOperator z s = P.lineCoordinate z • CliffordAlgebra.involute s :=
  -- `(rfl)`, not `rfl`: the body of `lineOperator` is not `@[expose]`d.
  (rfl)

/-- **The Clifford operator** of a vector: the assembly of the creation, annihilation and parity
operators along the polarization coordinates. -/
noncomputable def cliffordOperator : V →ₗ[K] Module.End K (ExteriorAlgebra K P.W) :=
  ((P.wedge.coprod P.contract).coprod P.lineOperator).comp
    P.decompositionEquiv.symm.toLinearMap

/-- The Clifford operator of a vector in polarization coordinates is the sum of the three
component operators. -/
theorem cliffordOperator_add_apply (x : P.W) (y : P.W') (z : P.line)
    (s : ExteriorAlgebra K P.W) :
    P.cliffordOperator ((x : V) + (y : V) + (z : V)) s =
      P.wedge x s + P.contract y s + P.lineCoordinate z • P.parity s := by
  simp [cliffordOperator]

/-! ### The anticommutation relations

The Clifford relation is the sum of six anticommutators between the three component operators.
Each is recorded separately, in the "solved" form that rewrites a composite back to the opposite
order, since that is what the assembly of `TauCeti.SpinPolarizationData.cliffordOperator_sq`
consumes. -/

/-- **Exterior multiplication is square-zero**: the isotropy of `W` at the level of operators. -/
theorem wedge_wedge (x : P.W) (s : ExteriorAlgebra K P.W) : P.wedge x (P.wedge x s) = 0 := by
  rw [wedge_apply, wedge_apply, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- **Contraction is square-zero**: the isotropy of `W'` at the level of operators. -/
theorem contract_contract (y : P.W') (s : ExteriorAlgebra K P.W) :
    P.contract y (P.contract y s) = 0 := by
  rw [contract_apply, contract_apply, CliffordAlgebra.contractLeft_contractLeft]

/-- **Creation and annihilation anticommute up to the pairing**: this is the one anticommutator
that is not zero, and the scalar it produces is the polar form of the two vectors. It is what pins
the coefficient of the Clifford relation to `QuadraticMap.polar`. -/
theorem contract_wedge (x : P.W) (y : P.W') (s : ExteriorAlgebra K P.W) :
    P.contract y (P.wedge x s) =
      polar Q (x : V) (y : V) • s - P.wedge x (P.contract y s) := by
  rw [contract_apply, wedge_apply, CliffordAlgebra.contractLeft_ι_mul, P.pairingEquiv_apply,
    wedge_apply, contract_apply]

/-- **The parity operator is an involution.** -/
theorem parity_parity (s : ExteriorAlgebra K P.W) : P.parity (P.parity s) = s := by
  rw [parity_apply, parity_apply, CliffordAlgebra.involute_involute]

/-- **Parity anticommutes with exterior multiplication**, since a vector is odd. -/
theorem parity_wedge (x : P.W) (s : ExteriorAlgebra K P.W) :
    P.parity (P.wedge x s) = -P.wedge x (P.parity s) := by
  rw [parity_apply, wedge_apply, map_mul, CliffordAlgebra.involute_ι, neg_mul, wedge_apply,
    parity_apply]

/-- **Parity anticommutes with contraction**, since contracting lowers the exterior degree
by one. -/
theorem parity_contract (y : P.W') (s : ExteriorAlgebra K P.W) :
    P.parity (P.contract y s) = -P.contract y (P.parity s) := by
  rw [parity_apply, contract_apply, TauCeti.CliffordAlgebra.involute_contractLeft, contract_apply,
    parity_apply]

/-- The quadratic form of a vector in polarization coordinates: both isotropic summands drop out
and the remainder is orthogonal to them, so only the pairing term and the remainder survive. -/
theorem quadraticForm_add (x : P.W) (y : P.W') (z : P.line) :
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
  ext s
  rw [Module.End.mul_apply, Module.algebraMap_end_apply, P.cliffordOperator_add_apply,
    P.cliffordOperator_add_apply, P.quadraticForm_add, ← P.lineCoordinate_sq z]
  simp only [map_add, map_smul, P.wedge_wedge, P.contract_contract, P.contract_wedge,
    P.parity_wedge, P.parity_contract, P.parity_parity]
  module

end SpinPolarizationData

/-- **The spinor representation of the Clifford algebra**: `CliffordAlgebra Q` acts on the
exterior algebra `S = ⋀·W` of the isotropic summand of a polarization, by exterior multiplication
for `W`, by contraction against the polar pairing for `W'`, and by a multiple of the parity
operator for the orthogonal remainder.

This is the Fock model of the spin module. In even dimension over an algebraically closed field it
is an isomorphism onto `Module.End K S`, and in odd dimension it factors through one of the two
central-idempotent summands of the Clifford algebra; neither statement is proved here. -/
noncomputable def spinAction {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (P : SpinPolarizationData Q) :
    CliffordAlgebra Q →ₐ[K] Module.End K (ExteriorAlgebra K P.W) :=
  CliffordAlgebra.lift Q ⟨P.cliffordOperator, P.cliffordOperator_sq⟩

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)

@[simp]
theorem spinAction_ι (v : V) :
    spinAction Q P (CliffordAlgebra.ι Q v) = P.cliffordOperator v :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-- A vector of the isotropic summand `W` acts on the spin module by exterior multiplication. -/
theorem spinAction_ι_wedge (x : P.W) (s : ExteriorAlgebra K P.W) :
    spinAction Q P (CliffordAlgebra.ι Q x) s = ExteriorAlgebra.ι K x * s := by
  rw [spinAction_ι, show ((x : V)) = (x : V) + ((0 : P.W') : V) + ((0 : P.line) : V) by simp,
    P.cliffordOperator_add_apply]
  simp

/-- A vector of the second isotropic summand `W'` acts on the spin module by contraction against
the functional the polarization pairing attaches to it. -/
theorem spinAction_ι_contract (y : P.W') (s : ExteriorAlgebra K P.W) :
    spinAction Q P (CliffordAlgebra.ι Q y) s =
      CliffordAlgebra.contractLeft (P.pairingEquiv y) s := by
  rw [spinAction_ι, show ((y : V)) = ((0 : P.W) : V) + (y : V) + ((0 : P.line) : V) by simp,
    P.cliffordOperator_add_apply]
  simp

/-- A vector of the orthogonal remainder acts on the spin module by its scalar coordinate times
the parity operator. -/
theorem spinAction_ι_parity (z : P.line) (s : ExteriorAlgebra K P.W) :
    spinAction Q P (CliffordAlgebra.ι Q z) s =
      P.lineCoordinate z • CliffordAlgebra.involute s := by
  rw [spinAction_ι,
    show ((z : V)) = ((0 : P.W) : V) + ((0 : P.W') : V) + (z : V) by simp,
    P.cliffordOperator_add_apply]
  simp

/-- **The anticommutator identity** pinning the coefficient of the spinor action: two vectors act
with anticommutator the scalar `QuadraticMap.polar Q x y`. Taking `y = x` returns the Clifford
relation, since `polar Q x x = 2 • Q x`. -/
theorem spinAction_ι_mul_add_swap (a b : V) :
    spinAction Q P (CliffordAlgebra.ι Q a) * spinAction Q P (CliffordAlgebra.ι Q b)
        + spinAction Q P (CliffordAlgebra.ι Q b) * spinAction Q P (CliffordAlgebra.ι Q a)
      = algebraMap K (Module.End K (ExteriorAlgebra K P.W)) (polar Q a b) := by
  rw [← map_mul (spinAction Q P), ← map_mul (spinAction Q P), ← map_add (spinAction Q P),
    CliffordAlgebra.ι_mul_ι_add_swap, AlgHom.commutes]

/-- The second isotropic summand annihilates the vacuum vector `1 ∈ ⋀·W`: contraction lowers the
exterior degree, and the vacuum has degree zero. -/
theorem spinAction_ι_apply_one (y : P.W') :
    spinAction Q P (CliffordAlgebra.ι Q y) 1 = 0 := by
  rw [spinAction_ι_contract, CliffordAlgebra.contractLeft_one]

end TauCeti
