/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Basic

/-!
# The group structure on connected components of an affine group

Let `H` be the coordinate Hopf algebra of a finite-type affine group over an algebraically closed
field. Every connected component of `Spec H` contains a rational point, and two rational points
lie in the same component exactly when they differ by a point of the identity component. Thus the
canonical equivalence

```text
H(k) / H⁰(k) ≃ ConnectedComponents (Spec H)
```

transports the quotient-group structure to the connected components. This file records that
structure and its characteristic API: the component of a product is the product of the
components, and the component map from rational points is a surjective group homomorphism whose
kernel is exactly `H⁰(k)`.

This is the group-theoretic input for representing `π₀(H)` by the finite constant group scheme
on the connected components. The coordinate-algebra comparison additionally needs the orthogonal
component-idempotent decomposition.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.instGroupConnectedComponents`: the component-group structure
  on `ConnectedComponents (PrimeSpectrum H)`.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPointsMulEquivConnectedComponents`: the
  multiplicative equivalence from the rational pointwise quotient to connected components.
* `TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap`: the surjective homomorphism sending a
  rational point to its connected component.
* `TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap_ker`: its kernel is the rational points
  of the identity component.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and Section 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 6.7 and 14.

This advances Layer 3, "Identity component `G°` and component group `π₀(G)`", of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Locally expose the group structure carried by the bundled rational component group. -/
noncomputable local instance componentGroupPointsGroupForTransfer
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) : Group (componentGroupPoints H) :=
  (componentGroupPoints H).str

/-- The group structure on the connected components of the spectrum of a finite-type affine
group. It is characterized by the requirement that the canonical bijection from
`H(k) / H⁰(k)` be multiplicative. -/
noncomputable instance instGroupConnectedComponents
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Group (ConnectedComponents (PrimeSpectrum H)) :=
  (componentGroupPointsEquivConnectedComponents H).symm.group

/-- The canonical equivalence from the rational pointwise component group to the connected
components of the spectrum, as a multiplicative equivalence. -/
noncomputable def componentGroupPointsMulEquivConnectedComponents
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    componentGroupPoints H ≃* ConnectedComponents (PrimeSpectrum H) :=
  ((componentGroupPointsEquivConnectedComponents H).symm.mulEquiv).symm

/-- The multiplicative component-group equivalence is the canonical component map on elements.
-/
@[simp]
theorem componentGroupPointsMulEquivConnectedComponents_apply
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (q : componentGroupPoints H) :
    componentGroupPointsMulEquivConnectedComponents H q =
      componentGroupPointsToConnectedComponents H q := by
  simp only [componentGroupPointsMulEquivConnectedComponents,
    Equiv.mulEquiv_symm_apply, Equiv.symm_symm]
  exact componentGroupPointsEquivConnectedComponents_apply H q

/-- The canonical bijection from the rational pointwise quotient to connected components
sends the identity to the identity component. -/
@[simp]
theorem componentGroupPointsToConnectedComponents_one
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    componentGroupPointsToConnectedComponents H 1 = 1 := by
  rw [← componentGroupPointsMulEquivConnectedComponents_apply]
  exact map_one (componentGroupPointsMulEquivConnectedComponents H)

/-- The canonical bijection from the rational pointwise quotient to connected components
preserves multiplication. -/
@[simp]
theorem componentGroupPointsToConnectedComponents_mul
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (q r : componentGroupPoints H) :
    componentGroupPointsToConnectedComponents H (q * r) =
      componentGroupPointsToConnectedComponents H q *
        componentGroupPointsToConnectedComponents H r := by
  calc
    componentGroupPointsToConnectedComponents H (q * r) =
        componentGroupPointsMulEquivConnectedComponents H (q * r) :=
      (componentGroupPointsMulEquivConnectedComponents_apply H (q * r)).symm
    _ = componentGroupPointsMulEquivConnectedComponents H q *
        componentGroupPointsMulEquivConnectedComponents H r :=
      map_mul (componentGroupPointsMulEquivConnectedComponents H) q r
    _ = componentGroupPointsToConnectedComponents H q *
        componentGroupPointsToConnectedComponents H r := by
      rw [componentGroupPointsMulEquivConnectedComponents_apply,
        componentGroupPointsMulEquivConnectedComponents_apply]

/-- The canonical bijection from the rational pointwise quotient to connected components
preserves inverses. -/
@[simp]
theorem componentGroupPointsToConnectedComponents_inv
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (q : componentGroupPoints H) :
    componentGroupPointsToConnectedComponents H q⁻¹ =
      (componentGroupPointsToConnectedComponents H q)⁻¹ := by
  rw [← componentGroupPointsMulEquivConnectedComponents_apply, map_inv,
    componentGroupPointsMulEquivConnectedComponents_apply]

/-- Send a rational point of a finite-type affine group to the connected component containing
its kernel point. -/
noncomputable def rationalComponentMap (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →*
      ConnectedComponents (PrimeSpectrum H) :=
  (componentGroupPointsMulEquivConnectedComponents H).toMonoidHom.comp
    (componentGroupPointsMk H).hom

/-- The rational component map sends a point to the component containing its kernel point. -/
@[simp]
theorem rationalComponentMap_apply (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    rationalComponentMap H g =
      (rationalKernelPoint H g : ConnectedComponents (PrimeSpectrum H)) := by
  dsimp [rationalComponentMap]
  rw [componentGroupPointsMulEquivConnectedComponents_apply,
    componentGroupPointsToConnectedComponents_mk]

/-- The component containing the identity rational point is the identity of the component
group. -/
@[simp]
theorem rationalKernelPoint_one_component (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (rationalKernelPoint H 1 : ConnectedComponents (PrimeSpectrum H)) = 1 := by
  rw [← rationalComponentMap_apply]
  exact map_one (rationalComponentMap H)

/-- The component of a product of rational points is the product of their components. -/
@[simp]
theorem rationalKernelPoint_mul_component (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (g h : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (rationalKernelPoint H (g * h) : ConnectedComponents (PrimeSpectrum H)) =
      (rationalKernelPoint H g : ConnectedComponents (PrimeSpectrum H)) *
        (rationalKernelPoint H h : ConnectedComponents (PrimeSpectrum H)) := by
  rw [← rationalComponentMap_apply, map_mul, rationalComponentMap_apply,
    rationalComponentMap_apply]

/-- The component of the inverse of a rational point is the inverse component. -/
@[simp]
theorem rationalKernelPoint_inv_component (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (rationalKernelPoint H g⁻¹ : ConnectedComponents (PrimeSpectrum H)) =
      (rationalKernelPoint H g : ConnectedComponents (PrimeSpectrum H))⁻¹ := by
  rw [← rationalComponentMap_apply, map_inv, rationalComponentMap_apply]

/-- Every connected component of the spectrum contains the kernel point of a rational point. -/
theorem rationalComponentMap_surjective (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Function.Surjective (rationalComponentMap H) :=
  (componentGroupPointsMulEquivConnectedComponents H).surjective.comp <|
    componentGroupPointsMk_surjective H

/-- A rational point maps to the identity component exactly when it belongs to the rational
points of `H⁰`. -/
@[simp]
theorem rationalComponentMap_eq_one_iff (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    rationalComponentMap H g = 1 ↔
      g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
        (CommAlgCat.of k k) := by
  dsimp [rationalComponentMap]
  rw [(componentGroupPointsMulEquivConnectedComponents H).map_eq_one_iff,
    componentGroupPointsMk_eq_one_iff]

/-- The kernel of the rational component map is the rational-point subgroup of the identity
component. -/
theorem rationalComponentMap_ker (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (rationalComponentMap H).ker =
      CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
        (CommAlgCat.of k k) := by
  ext g
  rw [MonoidHom.mem_ker]
  exact rationalComponentMap_eq_one_iff H g

end TauCeti.FiniteTypeCommHopfAlgCat
