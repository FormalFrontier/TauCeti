/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Idempotents
public import TauCeti.RingTheory.Idempotents.Connected.Component
public import TauCeti.Topology.ConnectedComponents

/-!
# Decomposing a ring by its connected components

Let `R` be a commutative ring for which the connected-components quotient of its prime spectrum is
discrete. Each connected component is selected by a canonical idempotent. This discreteness holds
in particular when the prime spectrum is locally connected or has finitely many connected
components. In the finite case, these idempotents form a complete orthogonal family and decompose
`R` as the product of the corresponding quotient rings.

Unlike `PrimeSpectrum.connectedComponentIdempotent`, which is indexed by a point of the spectrum,
`PrimeSpectrum.connectedComponentsIdempotent` is indexed by the component itself. Its
characteristic formula says that its basic open is exactly the fibre of the quotient map to
connected components. The complete-orthogonal theorem is therefore independent of any choice of
representative point.

The product decomposition assumes only `Finite (ConnectedComponents (PrimeSpectrum R))` and
constructs a `Fintype` internally for the finite sum.

## Main declarations

* `PrimeSpectrum.connectedComponentsIdempotent`: the idempotent selecting a connected component.
* `PrimeSpectrum.basicOpen_connectedComponentsIdempotent`: its basic open is the corresponding
  fibre of the quotient map.
* `PrimeSpectrum.completeOrthogonalIdempotents_connectedComponentsIdempotent`: the component
  idempotents are complete and pairwise orthogonal.
* `PrimeSpectrum.ringEquivPiQuotientConnectedComponentsIdeal`: the canonical product
  decomposition into the component quotient rings.

## References

* The Stacks Project, Tag 00EE, *Idempotents and clopen subsets*.
* J. S. Milne, *Algebraic Groups* (2017), Section 2.a.

This supplies the idempotent decomposition needed for the identity component and component group
in Layer 3 of the ReductiveGroups roadmap; it does not itself assert compatibility with base
change.
-/

public section

open Set Topology

namespace PrimeSpectrum

universe u

variable {R : Type u} [CommRing R]

section DiscreteConnectedComponents

variable [DiscreteTopology (ConnectedComponents (PrimeSpectrum R))]

/-- The canonical idempotent indexed by a connected component of `Spec R`.

It corresponds under the idempotent--clopen equivalence to the fibre of the quotient map over the
given component. -/
noncomputable def connectedComponentsIdempotent :
    ConnectedComponents (PrimeSpectrum R) → R :=
  fun C ↦
    ((isIdempotentElemEquivClopens (R := R)).symm
      (⟨ConnectedComponents.mk ⁻¹' ({C} : Set (ConnectedComponents (PrimeSpectrum R))),
        (isClopen_discrete {C}).preimage ConnectedComponents.continuous_coe⟩ :
        TopologicalSpace.Clopens (PrimeSpectrum R))).1

/-- Every component-indexed idempotent is idempotent. -/
theorem isIdempotentElem_connectedComponentsIdempotent
    (C : ConnectedComponents (PrimeSpectrum R)) :
    IsIdempotentElem (connectedComponentsIdempotent C) := by
  simpa only [connectedComponentsIdempotent] using
    ((isIdempotentElemEquivClopens (R := R)).symm
      (⟨ConnectedComponents.mk ⁻¹' ({C} : Set (ConnectedComponents (PrimeSpectrum R))),
        (isClopen_discrete {C}).preimage ConnectedComponents.continuous_coe⟩ :
        TopologicalSpace.Clopens (PrimeSpectrum R))).2

/-- The basic open of a component-indexed idempotent is the fibre of the quotient map over that
component. -/
theorem basicOpen_connectedComponentsIdempotent
    (C : ConnectedComponents (PrimeSpectrum R)) :
    (basicOpen (connectedComponentsIdempotent C) : Set (PrimeSpectrum R)) =
      ((↑) ⁻¹' ({C} : Set (ConnectedComponents (PrimeSpectrum R)))) := by
  simpa only [connectedComponentsIdempotent, TopologicalSpace.Clopens.coe_toOpens,
    TopologicalSpace.Opens.coe_mk, TopologicalSpace.Clopens.coe_mk] using congrArg SetLike.coe
      (basicOpen_isIdempotentElemEquivClopens_symm
        (⟨ConnectedComponents.mk ⁻¹' ({C} : Set (ConnectedComponents (PrimeSpectrum R))),
          (isClopen_discrete {C}).preimage ConnectedComponents.continuous_coe⟩ :
          TopologicalSpace.Clopens (PrimeSpectrum R)))

end DiscreteConnectedComponents

/-- On a component represented by `x`, the component-indexed idempotent is the point-indexed
component idempotent of `x`. -/
@[simp]
theorem connectedComponentsIdempotent_mk [LocallyConnectedSpace (PrimeSpectrum R)]
    (x : PrimeSpectrum R) :
    connectedComponentsIdempotent (x : ConnectedComponents (PrimeSpectrum R)) =
      connectedComponentIdempotent x := by
  apply basicOpen_injOn_isIdempotentElem
    (isIdempotentElem_connectedComponentsIdempotent _)
    (isIdempotentElem_connectedComponentIdempotent x)
  apply TopologicalSpace.Opens.ext
  rw [basicOpen_connectedComponentsIdempotent, basicOpen_connectedComponentIdempotent,
    connectedComponents_preimage_singleton]

section DiscreteConnectedComponents

variable [DiscreteTopology (ConnectedComponents (PrimeSpectrum R))]

/-- A point belongs to the basic open selected by a component exactly when it lies in that
component. -/
theorem mem_basicOpen_connectedComponentsIdempotent
    (C : ConnectedComponents (PrimeSpectrum R)) (x : PrimeSpectrum R) :
    x ∈ basicOpen (connectedComponentsIdempotent C) ↔
      (x : ConnectedComponents (PrimeSpectrum R)) = C := by
  rw [← SetLike.mem_coe, basicOpen_connectedComponentsIdempotent]
  simp only [Set.mem_preimage, Set.mem_singleton_iff]

/-- Distinct connected components have orthogonal component-indexed idempotents. -/
theorem connectedComponentsIdempotent_mul_eq_zero
    {C D : ConnectedComponents (PrimeSpectrum R)} (hCD : C ≠ D) :
    connectedComponentsIdempotent C * connectedComponentsIdempotent D = 0 := by
  apply basicOpen_injOn_isIdempotentElem
    ((isIdempotentElem_connectedComponentsIdempotent C).mul
      (isIdempotentElem_connectedComponentsIdempotent D)) IsIdempotentElem.zero
  rw [basicOpen_mul, basicOpen_zero]
  apply TopologicalSpace.Opens.ext
  rw [TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_bot]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rw [Set.mem_inter_iff, SetLike.mem_coe, SetLike.mem_coe,
    mem_basicOpen_connectedComponentsIdempotent,
    mem_basicOpen_connectedComponentsIdempotent] at hx
  exact hCD (hx.1.symm.trans hx.2)

/-- The component-indexed idempotents are pairwise orthogonal. -/
theorem orthogonalIdempotents_connectedComponentsIdempotent :
    OrthogonalIdempotents
      (connectedComponentsIdempotent : ConnectedComponents (PrimeSpectrum R) → R) :=
  ⟨isIdempotentElem_connectedComponentsIdempotent,
    fun _ _ hCD ↦ connectedComponentsIdempotent_mul_eq_zero hCD⟩

/-- The ideal generated by the complement of the idempotent indexed by `C`. -/
noncomputable def connectedComponentsIdeal
    (C : ConnectedComponents (PrimeSpectrum R)) : Ideal R :=
  Ideal.span {1 - connectedComponentsIdempotent C}

end DiscreteConnectedComponents

/-- At a component represented by `x`, the component-indexed ideal is the point-indexed connected
component ideal of `x`. -/
@[simp]
theorem connectedComponentsIdeal_mk [LocallyConnectedSpace (PrimeSpectrum R)]
    (x : PrimeSpectrum R) :
    connectedComponentsIdeal (x : ConnectedComponents (PrimeSpectrum R)) =
      connectedComponentIdeal x := by
  ext r
  rw [connectedComponentsIdeal, Ideal.mem_span_singleton', mem_connectedComponentIdeal_iff,
    connectedComponentsIdempotent_mk]

section DiscreteConnectedComponents

variable [DiscreteTopology (ConnectedComponents (PrimeSpectrum R))]

/-- A component-indexed idempotent becomes one in its component quotient. -/
@[simp]
theorem quotientMk_connectedComponentsIdempotent_eq_one
    (C : ConnectedComponents (PrimeSpectrum R)) :
    Ideal.Quotient.mk (connectedComponentsIdeal C) (connectedComponentsIdempotent C) = 1 := by
  rw [← map_one (Ideal.Quotient.mk (connectedComponentsIdeal C)), Ideal.Quotient.eq,
    connectedComponentsIdeal, Ideal.mem_span_singleton']
  exact ⟨-1, by ring⟩

/-- The zero locus of a component-indexed ideal is the corresponding fibre of the quotient map to
connected components. -/
@[simp]
theorem zeroLocus_connectedComponentsIdeal
    (C : ConnectedComponents (PrimeSpectrum R)) :
    zeroLocus (connectedComponentsIdeal C : Set R) =
      ((↑) ⁻¹' ({C} : Set (ConnectedComponents (PrimeSpectrum R)))) := by
  rw [connectedComponentsIdeal, zeroLocus_span,
    zeroLocus_eq_basicOpen_of_isIdempotentElem _
      (isIdempotentElem_connectedComponentsIdempotent C).one_sub,
    sub_sub_cancel, basicOpen_connectedComponentsIdempotent]

/-- The spectrum of a component quotient is homeomorphic to the corresponding fibre of the
quotient map to connected components. -/
noncomputable def primeSpectrumQuotientHomeomorphConnectedComponentsFiber
    (C : ConnectedComponents (PrimeSpectrum R)) :
    PrimeSpectrum (R ⧸ connectedComponentsIdeal C) ≃ₜ
      (((↑) ⁻¹' ({C} : Set (ConnectedComponents (PrimeSpectrum R)))) :
        Set (PrimeSpectrum R)) :=
  (quotientHomeomorphZeroLocus (connectedComponentsIdeal C)).trans
    (Homeomorph.setCongr (zeroLocus_connectedComponentsIdeal C))

/-- The spectrum of a component-indexed quotient is connected. -/
noncomputable instance connectedSpace_quotient_connectedComponentsIdeal
    (C : ConnectedComponents (PrimeSpectrum R)) :
    ConnectedSpace (PrimeSpectrum (R ⧸ connectedComponentsIdeal C)) := by
  let e := primeSpectrumQuotientHomeomorphConnectedComponentsFiber C
  let _ : ConnectedSpace
      ((((↑) ⁻¹' ({C} : Set (ConnectedComponents (PrimeSpectrum R)))) :
        Set (PrimeSpectrum R))) := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
    rw [connectedComponents_preimage_singleton]
    exact Subtype.connectedSpace isConnected_connectedComponent
  exact
    { isPreconnected_univ := by
        rw [← e.isPreconnected_image]
        simpa using (PreconnectedSpace.isPreconnected_univ :
          IsPreconnected (Set.univ : Set
            (((↑) ⁻¹' ({C} : Set (ConnectedComponents (PrimeSpectrum R)))) :
              Set (PrimeSpectrum R))))
      toNonempty := e.toEquiv.nonempty_congr.mpr inferInstance }

/-- A component-indexed quotient is nontrivial. -/
noncomputable instance nontrivial_quotient_connectedComponentsIdeal
    (C : ConnectedComponents (PrimeSpectrum R)) :
    Nontrivial (R ⧸ connectedComponentsIdeal C) :=
  (Classical.choice
    (inferInstance : Nonempty (PrimeSpectrum (R ⧸ connectedComponentsIdeal C)))).nontrivial

/-- After coercion to `PrimeSpectrum R`, the component-indexed quotient-spectrum homeomorphism
sends a point to its contraction along the quotient map. -/
@[simp]
theorem primeSpectrumQuotientHomeomorphConnectedComponentsFiber_apply_coe
    (C : ConnectedComponents (PrimeSpectrum R))
    (y : PrimeSpectrum (R ⧸ connectedComponentsIdeal C)) :
    (primeSpectrumQuotientHomeomorphConnectedComponentsFiber C y : PrimeSpectrum R) =
      comap (Ideal.Quotient.mk (connectedComponentsIdeal C)) y := by
  simp only [primeSpectrumQuotientHomeomorphConnectedComponentsFiber,
    Homeomorph.trans_apply, Homeomorph.setCongr]
  exact quotientHomeomorphZeroLocus_apply_coe _ y

end DiscreteConnectedComponents

private theorem connectedComponentsIdempotent_sum_eq_one
    [Fintype (ConnectedComponents (PrimeSpectrum R))] :
    ∑ C : ConnectedComponents (PrimeSpectrum R), connectedComponentsIdempotent C = 1 := by
  classical
  let s := ∑ C : ConnectedComponents (PrimeSpectrum R), connectedComponentsIdempotent C
  have hs : IsIdempotentElem s := by
    simpa only [s] using
      orthogonalIdempotents_connectedComponentsIdempotent.isIdempotentElem_sum
        (s := Finset.univ)
  apply basicOpen_injOn_isIdempotentElem hs IsIdempotentElem.one
  rw [basicOpen_one, eq_top_iff]
  intro x _
  rw [PrimeSpectrum.mem_basicOpen]
  intro hs_mem
  have hmul_mem : connectedComponentsIdempotent
      (x : ConnectedComponents (PrimeSpectrum R)) *
        (∑ C : ConnectedComponents (PrimeSpectrum R), connectedComponentsIdempotent C) ∈
          x.asIdeal := by
    simpa only [s] using x.asIdeal.mul_mem_left
      (connectedComponentsIdempotent (x : ConnectedComponents (PrimeSpectrum R))) hs_mem
  have hmul := orthogonalIdempotents_connectedComponentsIdempotent.mul_sum_of_mem
    (i := (x : ConnectedComponents (PrimeSpectrum R))) (s := Finset.univ)
    (Finset.mem_univ _)
  rw [hmul] at hmul_mem
  have hnot_mem : connectedComponentsIdempotent
      (x : ConnectedComponents (PrimeSpectrum R)) ∉ x.asIdeal := by
    rw [← PrimeSpectrum.mem_basicOpen]
    exact (mem_basicOpen_connectedComponentsIdempotent _ x).mpr rfl
  exact hnot_mem hmul_mem

/-- The idempotents indexed by the connected components of `Spec R` form a complete orthogonal
family. -/
theorem completeOrthogonalIdempotents_connectedComponentsIdempotent
    [Fintype (ConnectedComponents (PrimeSpectrum R))] :
    CompleteOrthogonalIdempotents
      (connectedComponentsIdempotent : ConnectedComponents (PrimeSpectrum R) → R) :=
  ⟨orthogonalIdempotents_connectedComponentsIdempotent,
    connectedComponentsIdempotent_sum_eq_one⟩

/-- A ring with finitely many connected components in its prime spectrum is canonically
isomorphic to the product of its component-indexed quotient rings. -/
noncomputable def ringEquivPiQuotientConnectedComponentsIdeal
    [Finite (ConnectedComponents (PrimeSpectrum R))] :
    R ≃+* ∀ C : ConnectedComponents (PrimeSpectrum R), R ⧸ connectedComponentsIdeal C := by
  classical
  let _ : Fintype (ConnectedComponents (PrimeSpectrum R)) := Fintype.ofFinite _
  apply RingEquiv.ofBijective
    (RingHom.pi fun C ↦ Ideal.Quotient.mk (connectedComponentsIdeal C))
  -- Rewriting the ideal is blocked here because each quotient type depends on it, so expose the
  -- defining span in the whole dependent function type at once.
  change Function.Bijective
    (RingHom.pi fun C ↦
      Ideal.Quotient.mk (Ideal.span {1 - connectedComponentsIdempotent C}))
  exact completeOrthogonalIdempotents_connectedComponentsIdempotent.bijective_pi

/-- The product decomposition sends an element to its class in each component-indexed
quotient. -/
@[simp]
theorem ringEquivPiQuotientConnectedComponentsIdeal_apply
    [Finite (ConnectedComponents (PrimeSpectrum R))]
    (r : R) (C : ConnectedComponents (PrimeSpectrum R)) :
    ringEquivPiQuotientConnectedComponentsIdeal r C =
      Ideal.Quotient.mk (connectedComponentsIdeal C) r :=
  by
    rw [ringEquivPiQuotientConnectedComponentsIdeal, RingEquiv.ofBijective_apply,
      RingHom.pi_apply]

end PrimeSpectrum
