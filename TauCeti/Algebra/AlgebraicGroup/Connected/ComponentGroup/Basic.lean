/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.GroupScheme
public import TauCeti.Algebra.AlgebraicGroup.Connected.Normal
public import TauCeti.Algebra.AlgebraicGroup.Connected.Translation
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.ConnectedComponents
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Projection
public import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# The component group of an affine group

Let `H` be the coordinate Hopf algebra of a finite-type affine group over an algebraically closed
field. Its identity component is a normal closed subgroup, so the fppf quotient construction
defines the component group sheaf `π₀(H) = H / H⁰`.

On rational points, the corresponding pointwise quotient is canonically equivalent to the
connected components of `Spec H`. The proof uses translation to identify two rational points
modulo `H⁰` exactly when their kernel points lie in the same connected component. Every connected
component contains a rational point: its component idempotent is non-nilpotent, so the affine
Nullstellensatz detects it at an algebraically closed point. Consequently the rational component
group is finite.

No representability is asserted here. Showing that the fppf quotient is represented by a finite
étale group scheme is the remaining scheme-theoretic part of the component-group construction.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupFppfSheaf`: the fppf quotient by the identity
  component.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupFppfProjection`: its locally surjective quotient
  projection.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints`: its pointwise precursor on rational
  points.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPointsEquivConnectedComponents`: the canonical
  equivalence between that quotient and the connected components of `Spec H`.
* `TauCeti.FiniteTypeCommHopfAlgCat.instFiniteComponentGroupPoints`: finiteness of the rational
  component group.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and Section 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 6.7 and 14.

This advances Layer 3, "Identity component `G°` and component group `π₀(G)`", of the
ReductiveGroups roadmap.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The prime-spectrum point underlying a rational point of a finite-type affine group.

The explicit `PrimeSpectrum` return type bridges the scheme-point spelling of `AlgHom.kernelPoint`
to the connected-component API. -/
abbrev rationalKernelPoint (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) : PrimeSpectrum H :=
  AlgHom.kernelPoint g.ofConv

omit [IsAlgClosed k] in
/-- The prime-spectrum point underlying the identity rational point is the augmentation point. -/
@[simp]
theorem rationalKernelPoint_one (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    rationalKernelPoint H 1 = Bialgebra.augmentationPoint k H := by
  apply congrArg AlgHom.kernelPoint
  apply AlgHom.ext
  exact AlgHom.convOne_apply

/-- The identity-component Hopf ideal is normal over an algebraically closed field. -/
theorem isNormal_identityComponentHopfIdeal (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).IsNormal := by
  let : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  exact HopfAlgebra.isNormal_identityComponentHopfIdeal (k := k) (H := H)

/-- The component group fppf sheaf `H / H⁰` of a finite-type affine group over an algebraically
closed field. Its representability by a finite étale group scheme is not asserted here. -/
noncomputable abbrev componentGroupFppfSheaf (H : FiniteTypeCommHopfAlgCat.{u, u} k) :=
  CommHopfAlgCat.fppfQuotientSheaf H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
    (isNormal_identityComponentHopfIdeal H)

/-- The canonical morphism from the fppf sheaf of points of `H` to its component group sheaf. -/
noncomputable def componentGroupFppfProjection (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.pointsFppfGroupObject H.obj ⟶ componentGroupFppfSheaf H :=
  CommHopfAlgCat.fppfQuotientProjection H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
    (isNormal_identityComponentHopfIdeal H)

/-- The projection to the component group is an epimorphism of group objects in fppf sheaves. -/
instance instEpiComponentGroupFppfProjection (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Epi (componentGroupFppfProjection H) := by
  unfold componentGroupFppfProjection
  infer_instance

/-- Every section of the component group lifts to an ambient-group section after an fppf cover. -/
theorem isLocallySurjective_componentGroupFppfProjection
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Sheaf.IsLocallySurjective (componentGroupFppfProjection H).hom.hom := by
  unfold componentGroupFppfProjection
  exact CommHopfAlgCat.isLocallySurjective_fppfQuotientProjection H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
    (isNormal_identityComponentHopfIdeal H)

/-- The rational pointwise component group `H(k) / H⁰(k)`.

This is the value at `k` of the pointwise quotient presheaf whose sheafification is
`componentGroupFppfSheaf`. -/
noncomputable abbrev componentGroupPoints (H : FiniteTypeCommHopfAlgCat.{u, u} k) : GrpCat.{u} :=
  CommHopfAlgCat.pointwiseQuotientGroup H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
    (isNormal_identityComponentHopfIdeal H) (CommAlgCat.of k k)

/-- Locally expose the group structure carried by the bundled rational component group. -/
noncomputable local instance componentGroupPointsGroup
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) : Group (componentGroupPoints H) :=
  (componentGroupPoints H).str

/-- The quotient homomorphism from rational points to the rational pointwise component group. -/
noncomputable def componentGroupPointsMk (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⟶ componentGroupPoints H :=
  CommHopfAlgCat.pointwiseQuotientMk H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
    (isNormal_identityComponentHopfIdeal H) (CommAlgCat.of k k)

/-- The quotient homomorphism from rational points to the rational component group is
surjective. -/
theorem componentGroupPointsMk_surjective (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Function.Surjective (componentGroupPointsMk H) := by
  unfold componentGroupPointsMk
  exact CommHopfAlgCat.pointwiseQuotientMk_surjective H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
    (isNormal_identityComponentHopfIdeal H) (CommAlgCat.of k k)

/-- A rational point maps to the identity of the rational component group exactly when it lies
in the identity-component subgroup. -/
@[simp]
theorem componentGroupPointsMk_eq_one_iff (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    componentGroupPointsMk H g = 1 ↔
      g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
        (CommAlgCat.of k k) := by
  unfold componentGroupPointsMk
  exact CommHopfAlgCat.pointwiseQuotientMk_eq_one_iff H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
    (isNormal_identityComponentHopfIdeal H) (CommAlgCat.of k k) g

/-- A rational point belongs to `H⁰(k)` exactly when its kernel point belongs to the identity
component of `Spec H`. -/
theorem mem_identityComponentPointsSubgroup_iff
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ↔
      rationalKernelPoint H g ∈ connectedComponent (rationalKernelPoint H 1) := by
  rw [← range_identityComponentPointsHom H (CommAlgCat.of k k)]
  -- The range is stored as a monoid-hom range, while the existing point criterion uses `Set.range`.
  change g ∈ Set.range (identityComponentPointsHom H (CommAlgCat.of k k)) ↔ _
  rw [rationalKernelPoint_one]
  exact mem_range_identityComponentPointsHom_iff H g

/-- Two rational points have kernel points in the same connected component exactly when their
left quotient belongs to the identity-component subgroup. -/
theorem connectedComponents_rationalKernelPoint_eq_iff
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (g h : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (rationalKernelPoint H g : ConnectedComponents (PrimeSpectrum H)) =
      rationalKernelPoint H h ↔
      g⁻¹ * h ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) := by
  let N := CommHopfAlgCat.quotientPointsSubgroup H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k)
  let hN : N.Normal := CommHopfAlgCat.quotientPointsSubgroup_normal H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
    (isNormal_identityComponentHopfIdeal H) (CommAlgCat.of k k)
  have hright :
      rationalKernelPoint H h ∈ connectedComponent (rationalKernelPoint H g) ↔
        h * g⁻¹ ∈ N := by
    constructor
    · intro hh
      have himage := TauCeti.HopfAlgebra.rightTranslationHomeomorph_image_connectedComponent g⁻¹
        (rationalKernelPoint H g)
      have hmem : TauCeti.HopfAlgebra.rightTranslationHomeomorph g⁻¹
          (rationalKernelPoint H h) ∈
          TauCeti.HopfAlgebra.rightTranslationHomeomorph g⁻¹ ''
            connectedComponent (rationalKernelPoint H g) :=
        ⟨rationalKernelPoint H h, hh, rfl⟩
      rw [himage, TauCeti.HopfAlgebra.rightTranslationHomeomorph_kernelPoint,
        TauCeti.HopfAlgebra.rightTranslationHomeomorph_kernelPoint, mul_inv_cancel] at hmem
      -- Translation simplifies the identity to `ofConv 1`; restore the bundled point spelling.
      change rationalKernelPoint H (h * g⁻¹) ∈
        connectedComponent (rationalKernelPoint H 1) at hmem
      exact (mem_identityComponentPointsSubgroup_iff H (h * g⁻¹)).mpr hmem
    · intro hh
      have hh' := (mem_identityComponentPointsSubgroup_iff H (h * g⁻¹)).mp hh
      have himage := TauCeti.HopfAlgebra.rightTranslationHomeomorph_image_connectedComponent g
        (rationalKernelPoint H 1)
      have hmem : TauCeti.HopfAlgebra.rightTranslationHomeomorph g
          (rationalKernelPoint H (h * g⁻¹)) ∈
          TauCeti.HopfAlgebra.rightTranslationHomeomorph g ''
            connectedComponent (rationalKernelPoint H 1) :=
        ⟨rationalKernelPoint H (h * g⁻¹), hh', rfl⟩
      rw [himage, TauCeti.HopfAlgebra.rightTranslationHomeomorph_kernelPoint,
        TauCeti.HopfAlgebra.rightTranslationHomeomorph_kernelPoint, mul_assoc,
        inv_mul_cancel, mul_one, one_mul] at hmem
      exact hmem
  rw [ConnectedComponents.coe_eq_coe]
  have hmem_swap :
      rationalKernelPoint H g ∈ connectedComponent (rationalKernelPoint H h) ↔
        rationalKernelPoint H h ∈ connectedComponent (rationalKernelPoint H g) := by
    calc
      rationalKernelPoint H g ∈ connectedComponent (rationalKernelPoint H h) ↔
          connectedComponent (rationalKernelPoint H g) =
            connectedComponent (rationalKernelPoint H h) :=
        connectedComponent_eq_iff_mem.symm
      _ ↔ connectedComponent (rationalKernelPoint H h) =
          connectedComponent (rationalKernelPoint H g) := eq_comm
      _ ↔ rationalKernelPoint H h ∈ connectedComponent (rationalKernelPoint H g) :=
        connectedComponent_eq_iff_mem
  rw [connectedComponent_eq_iff_mem, hmem_swap, hright]
  constructor
  · intro hh
    have hc := hN.conj_mem (h * g⁻¹) hh g⁻¹
    have heq : g⁻¹ * (h * g⁻¹) * (g⁻¹)⁻¹ = g⁻¹ * h := by group
    rw [heq] at hc
    exact hc
  · intro hh
    have hc := hN.conj_mem (g⁻¹ * h) hh g
    have heq : g * (g⁻¹ * h) * g⁻¹ = h * g⁻¹ := by group
    rw [heq] at hc
    exact hc

/-- Send a rational point to the connected component containing its kernel point. This descends
to the quotient by `H⁰(k)`. -/
noncomputable def componentGroupPointsToConnectedComponents
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    componentGroupPoints H → ConnectedComponents (PrimeSpectrum H) :=
  fun q ↦ Quotient.liftOn' q
    (fun g ↦ (rationalKernelPoint H g : ConnectedComponents (PrimeSpectrum H)))
    (fun g h hgh ↦ by
      rw [connectedComponents_rationalKernelPoint_eq_iff H g h]
      exact (QuotientGroup.leftRel_apply.mp hgh))

/-- The component map sends the class of a rational point to the component containing its kernel
point. -/
@[simp]
theorem componentGroupPointsToConnectedComponents_mk
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    componentGroupPointsToConnectedComponents H (componentGroupPointsMk H g) =
      (rationalKernelPoint H g : ConnectedComponents (PrimeSpectrum H)) := by
  rw [componentGroupPointsMk, CommHopfAlgCat.pointwiseQuotientMk_apply]
  rfl

private theorem componentGroupPointsToConnectedComponents_surjective
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Function.Surjective (componentGroupPointsToConnectedComponents H) := by
  intro C
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  let e := PrimeSpectrum.connectedComponentIdempotent x
  have he_ne_zero : e ≠ 0 := by
    intro he
    have he_mem : e ∈ x.asIdeal := he ▸ x.asIdeal.zero_mem
    exact PrimeSpectrum.connectedComponentIdempotent_notMem_asIdeal x he_mem
  have he_not_nilpotent : ¬ IsNilpotent e := by
    intro he
    exact he_ne_zero
      (he.eq_zero_of_isIdempotentElem
        (PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent x))
  obtain ⟨f, hf⟩ :=
    exists_algHom_apply_ne_zero_of_not_isNilpotent (k := k) (K := k) he_not_nilpotent
  let g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) := toConv f
  refine ⟨componentGroupPointsMk H g, ?_⟩
  rw [componentGroupPointsToConnectedComponents_mk, ConnectedComponents.coe_eq_coe']
  rw [← PrimeSpectrum.basicOpen_connectedComponentIdempotent]
  apply (PrimeSpectrum.mem_basicOpen e (rationalKernelPoint H g)).mpr
  rw [rationalKernelPoint, AlgHom.kernelPoint_asIdeal, RingHom.mem_ker]
  exact hf

private theorem componentGroupPointsToConnectedComponents_injective
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Function.Injective (componentGroupPointsToConnectedComponents H) := by
  intro x y hxy
  obtain ⟨g, rfl⟩ := CommHopfAlgCat.pointwiseQuotientMk_surjective H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
    (isNormal_identityComponentHopfIdeal H) (CommAlgCat.of k k) x
  obtain ⟨h, rfl⟩ := CommHopfAlgCat.pointwiseQuotientMk_surjective H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
    (isNormal_identityComponentHopfIdeal H) (CommAlgCat.of k k) y
  -- Surjectivity exposes the raw quotient map; refold the component-group projection wrapper.
  change componentGroupPointsToConnectedComponents H (componentGroupPointsMk H g) =
    componentGroupPointsToConnectedComponents H (componentGroupPointsMk H h) at hxy
  rw [componentGroupPointsToConnectedComponents_mk,
    componentGroupPointsToConnectedComponents_mk,
    connectedComponents_rationalKernelPoint_eq_iff] at hxy
  -- Refold the same wrapper in the equality of quotient classes.
  change componentGroupPointsMk H g = componentGroupPointsMk H h
  rw [componentGroupPointsMk, CommHopfAlgCat.pointwiseQuotientMk_apply,
    CommHopfAlgCat.pointwiseQuotientMk_apply,
    QuotientGroup.mk'_eq_mk']
  exact ⟨g⁻¹ * h, hxy, by group⟩

/-- Over an algebraically closed field, the rational pointwise component group is canonically
equivalent to the connected components of the prime spectrum. -/
noncomputable def componentGroupPointsEquivConnectedComponents
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    componentGroupPoints H ≃ ConnectedComponents (PrimeSpectrum H) :=
  Equiv.ofBijective (componentGroupPointsToConnectedComponents H)
    ⟨componentGroupPointsToConnectedComponents_injective H,
      componentGroupPointsToConnectedComponents_surjective H⟩

/-- The canonical equivalence from the rational pointwise component group is the component map
on elements. -/
@[simp]
theorem componentGroupPointsEquivConnectedComponents_apply
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (q : componentGroupPoints H) :
    componentGroupPointsEquivConnectedComponents H q =
      componentGroupPointsToConnectedComponents H q :=
  (rfl)

/-- The rational pointwise component group of a finite-type affine group over an algebraically
closed field is finite. -/
noncomputable instance instFiniteComponentGroupPoints
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) : Finite (componentGroupPoints H) :=
  Finite.of_equiv (ConnectedComponents (PrimeSpectrum H))
    (componentGroupPointsEquivConnectedComponents H).symm

end TauCeti.FiniteTypeCommHopfAlgCat
