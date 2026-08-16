/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import TauCeti.RingTheory.Idempotents.Connected.Component

/-!
# Decomposing a ring by its connected components

Let `R` be a commutative ring whose prime spectrum is locally connected and has finitely many
connected components. Each component is selected by a canonical idempotent. This file shows that
these idempotents form a complete orthogonal family and uses them to decompose `R` as the product
of the coordinate rings of its connected components.

Unlike `PrimeSpectrum.connectedComponentIdempotent`, which is indexed by a point of the spectrum,
`PrimeSpectrum.componentIdempotent` is indexed by the component itself. Its characteristic formula
says that its basic open is exactly the fibre of the quotient map to connected components. The
complete-orthogonal theorem is therefore independent of any choice of representative point.

For a finite-type algebra over a Noetherian ring the hypotheses are automatic. Applied to the
coordinate ring of a finite-type affine group, this decomposition is the commutative-algebra input
for representing its component group by a finite constant group scheme.

## Main declarations

* `PrimeSpectrum.componentIdempotent`: the idempotent selecting a connected component.
* `PrimeSpectrum.basicOpen_componentIdempotent`: its basic open is the corresponding component.
* `PrimeSpectrum.completeOrthogonalIdempotents_componentIdempotent`: the component idempotents
  are complete and pairwise orthogonal.
* `PrimeSpectrum.componentDecompositionRingEquiv`: the canonical product decomposition into the
  component quotient rings.

## References

* The Stacks Project, Tag 00EE, *Idempotents and clopen subsets*.
* J. S. Milne, *Algebraic Groups* (2017), Section 2.a.

This supplies the idempotent decomposition needed for the finite étale component group in Layer 3
of the ReductiveGroups roadmap.
-/

public section

open Set Topology

namespace PrimeSpectrum

universe u

variable {R : Type u} [CommRing R] [LocallyConnectedSpace (PrimeSpectrum R)]

/-- The canonical idempotent selecting a connected component of `Spec R`.

This descends `connectedComponentIdempotent` from points to components; points in the same
component give the same idempotent because their basic opens are the same component. -/
noncomputable def componentIdempotent : ConnectedComponents (PrimeSpectrum R) → R :=
  Quotient.lift connectedComponentIdempotent fun x y hxy ↦ by
    apply (eq_connectedComponentIdempotent_iff
      (isIdempotentElem_connectedComponentIdempotent x) y).mpr
    rw [basicOpen_connectedComponentIdempotent]
    exact hxy

/-- On a component represented by `x`, the component idempotent is the point-indexed component
idempotent of `x`. -/
@[simp]
theorem componentIdempotent_mk (x : PrimeSpectrum R) :
    componentIdempotent (x : ConnectedComponents (PrimeSpectrum R)) =
      connectedComponentIdempotent x :=
  (rfl)

/-- Every component idempotent is idempotent. -/
theorem isIdempotentElem_componentIdempotent
    (C : ConnectedComponents (PrimeSpectrum R)) :
    IsIdempotentElem (componentIdempotent C) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  exact isIdempotentElem_connectedComponentIdempotent x

/-- The basic open of a component idempotent is exactly the fibre of the quotient map over that
component. -/
theorem basicOpen_componentIdempotent (C : ConnectedComponents (PrimeSpectrum R)) :
    (basicOpen (componentIdempotent C) : Set (PrimeSpectrum R)) =
      {x : PrimeSpectrum R | (x : ConnectedComponents (PrimeSpectrum R)) = C} := by
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [componentIdempotent_mk, basicOpen_connectedComponentIdempotent]
  ext x
  rw [Set.mem_ofPred_eq, ConnectedComponents.coe_eq_coe']

/-- A point belongs to the basic open selected by a component exactly when it lies in that
component. -/
theorem mem_basicOpen_componentIdempotent
    (C : ConnectedComponents (PrimeSpectrum R)) (x : PrimeSpectrum R) :
    x ∈ basicOpen (componentIdempotent C) ↔
      (x : ConnectedComponents (PrimeSpectrum R)) = C := by
  rw [← SetLike.mem_coe, basicOpen_componentIdempotent]
  rfl

/-- Distinct connected components have orthogonal component idempotents. -/
theorem componentIdempotent_mul_eq_zero
    {C D : ConnectedComponents (PrimeSpectrum R)} (hCD : C ≠ D) :
    componentIdempotent C * componentIdempotent D = 0 := by
  apply basicOpen_injOn_isIdempotentElem
    ((isIdempotentElem_componentIdempotent C).mul
      (isIdempotentElem_componentIdempotent D)) IsIdempotentElem.zero
  rw [basicOpen_mul]
  apply SetLike.coe_injective
  -- The lattice infimum of basic opens is their set-theoretic intersection.
  change
    ({x : PrimeSpectrum R | x ∈ basicOpen (componentIdempotent C) ∧
        x ∈ basicOpen (componentIdempotent D)} : Set (PrimeSpectrum R)) =
      (basicOpen (0 : R) : Set (PrimeSpectrum R))
  ext x
  rw [Set.mem_ofPred_eq, mem_basicOpen_componentIdempotent,
    mem_basicOpen_componentIdempotent]
  -- Membership in the zero basic open is presented as nonmembership of zero in the prime.
  change
    (((x : ConnectedComponents (PrimeSpectrum R)) = C ∧
        (x : ConnectedComponents (PrimeSpectrum R)) = D) ↔ (0 : R) ∉ x.asIdeal)
  constructor
  · intro h
    exact (hCD (h.1.symm.trans h.2)).elim
  · intro hzero
    exact (hzero x.asIdeal.zero_mem).elim

variable [Fintype (ConnectedComponents (PrimeSpectrum R))]

private theorem componentIdempotent_sum_eq_one :
    ∑ C : ConnectedComponents (PrimeSpectrum R), componentIdempotent C = 1 := by
  classical
  let e : ConnectedComponents (PrimeSpectrum R) → R := componentIdempotent
  have he : OrthogonalIdempotents e := ⟨
    isIdempotentElem_componentIdempotent,
    fun _ _ hCD ↦ componentIdempotent_mul_eq_zero hCD⟩
  let s := ∑ C : ConnectedComponents (PrimeSpectrum R), e C
  have hs : IsIdempotentElem s := by
    simpa [s] using he.isIdempotentElem_sum (s := Finset.univ)
  have hnil : IsNilpotent (1 - s) := (nilpotent_iff_mem_prime).2 fun p hp ↦ by
    let x : PrimeSpectrum R := ⟨p, hp⟩
    let C : ConnectedComponents (PrimeSpectrum R) := x
    have heC_not_mem : e C ∉ p := by
      -- Refold the ideal `p` as the ideal carried by the corresponding spectrum point.
      change componentIdempotent C ∉ x.asIdeal
      rw [← PrimeSpectrum.mem_basicOpen, mem_basicOpen_componentIdempotent]
    have hone_sub_mem : 1 - e C ∈ p := by
      apply (hp.mem_or_mem ?_).resolve_left heC_not_mem
      have hmul : e C * (1 - e C) = 0 := by
        rw [mul_sub, mul_one, he.idem C |>.eq, sub_self]
      exact hmul ▸ p.zero_mem
    have hother : ∀ D ∈ (Finset.univ.erase C), e D ∈ p := by
      intro D hD
      have hDC : D ≠ C := by simpa using (Finset.mem_erase.mp hD).1
      by_contra hnot
      have hxD : x ∈ basicOpen (componentIdempotent D) := by
        rw [PrimeSpectrum.mem_basicOpen]
        exact hnot
      exact hDC ((mem_basicOpen_componentIdempotent D x).mp hxD).symm
    have hs_decomp : s = e C + ∑ D ∈ Finset.univ.erase C, e D := by
      -- Expose the `Fintype` sum before separating its `C`-term.
      change (∑ D, e D) = e C + ∑ D ∈ Finset.univ.erase C, e D
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ C)]
    rw [hs_decomp]
    convert p.sub_mem hone_sub_mem (p.sum_mem hother) using 1
    ring
  have hone_sub : IsIdempotentElem (1 - s) := hs.one_sub
  exact (sub_eq_zero.mp (hone_sub.eq_zero_of_isNilpotent hnil)).symm

/-- The idempotents selecting the connected components of `Spec R` form a complete orthogonal
family. -/
theorem completeOrthogonalIdempotents_componentIdempotent :
    CompleteOrthogonalIdempotents
      (componentIdempotent : ConnectedComponents (PrimeSpectrum R) → R) := by
  classical
  refine ⟨⟨isIdempotentElem_componentIdempotent, ?_⟩, componentIdempotent_sum_eq_one⟩
  exact fun _ _ hCD ↦ componentIdempotent_mul_eq_zero hCD

/-- The ideal cutting out a connected component of `Spec R`, indexed by the component rather
than by a representative point. -/
noncomputable def componentIdeal
    (C : ConnectedComponents (PrimeSpectrum R)) : Ideal R :=
  Ideal.span {1 - componentIdempotent C}

omit [Fintype (ConnectedComponents (PrimeSpectrum R))] in
/-- The ideal cutting out a component is generated by the complement of its component
idempotent. -/
theorem componentIdeal_eq_span (C : ConnectedComponents (PrimeSpectrum R)) :
    componentIdeal C = Ideal.span {1 - componentIdempotent C} :=
  (rfl)

omit [Fintype (ConnectedComponents (PrimeSpectrum R))] in
/-- For a component represented by `x`, the component ideal is the point-indexed connected
component ideal of `x`. -/
@[simp]
theorem componentIdeal_mk (x : PrimeSpectrum R) :
    componentIdeal (x : ConnectedComponents (PrimeSpectrum R)) = connectedComponentIdeal x := by
  rw [componentIdeal_eq_span, connectedComponentIdeal_eq_span, componentIdempotent_mk]

/-- A ring with finitely many open connected components is canonically the product of the
coordinate rings of those components. -/
noncomputable def componentDecompositionRingEquiv :
    R ≃+* ∀ C : ConnectedComponents (PrimeSpectrum R), R ⧸ componentIdeal C := by
  classical
  apply RingEquiv.ofBijective
    (RingHom.pi fun C ↦ Ideal.Quotient.mk (componentIdeal C))
  -- Expose the component ideals to match Mathlib's generic idempotent decomposition theorem.
  change Function.Bijective
    (RingHom.pi fun C ↦ Ideal.Quotient.mk (Ideal.span {1 - componentIdempotent C}))
  exact completeOrthogonalIdempotents_componentIdempotent.bijective_pi

/-- The component decomposition sends an element to its class in each component quotient. -/
@[simp]
theorem componentDecompositionRingEquiv_apply
    (r : R) (C : ConnectedComponents (PrimeSpectrum R)) :
    componentDecompositionRingEquiv r C = Ideal.Quotient.mk (componentIdeal C) r :=
  (rfl)

end PrimeSpectrum
