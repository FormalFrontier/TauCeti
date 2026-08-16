/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.RepresentationTheory.GaloisLattice.Basic

/-!
# Finite quotients acting on Galois lattices

A finite free module representation whose vectors have open stabilizers has open kernel. Indeed,
the kernel is already the intersection of the stabilizers of a finite basis. The Krull
neighborhood basis then puts a finite-dimensional normal subextension's fixing subgroup inside
that kernel, so the quotient of the absolute Galois group by the kernel is finite. The original
action therefore factors faithfully through a finite group.

This finite-quotient reduction is the first descent step in the classification of non-split tori:
the Galois action on a torus character lattice factors through a finite Galois quotient, after
which the corresponding split torus can be descended from a finite extension.

## Main declarations

* `Representation.isOpen_ker_of_finite`: open point stabilizers imply an open kernel on a finite
  free module.
* `Field.absoluteGaloisGroup.exists_finiteDimensional_normal_fixingSubgroup_le`: every open
  subgroup contains the fixing subgroup of a finite-dimensional normal subextension.
* `TauCeti.GaloisLatticeCat.actionQuotient`: the finite quotient of the absolute Galois group
  acting faithfully on a Galois lattice.
* `TauCeti.GaloisLatticeCat.actionQuotientRepresentation`: the induced representation of that
  finite quotient.

## References

See J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Corollary 12.24.
-/

public section

namespace Representation

universe u v w

variable {R : Type u} [Semiring R]
variable {G : Type v} [Group G] [TopologicalSpace G]
variable {V : Type w} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]

/-- A representation on a finite free module has open kernel if every vector stabilizer is open.

It is enough to intersect the stabilizers of a finite basis: an element fixes that basis exactly
when its linear action is the identity. -/
theorem isOpen_ker_of_finite (rho : Representation R G V)
    (hopen : ∀ x : V, IsOpen {g | rho g x = x}) :
    IsOpen (rho.ker : Set G) := by
  let B := Module.Free.chooseBasis R V
  let _ : MulAction G V := {
    smul g x := rho g x
    one_smul x := by
      -- Expose the local action, whose scalar operation is definitionally `rho`.
      change rho 1 x = x
      rw [map_one, Module.End.one_apply]
    mul_smul g h x := by
      -- Expose the local action, whose scalar operation is definitionally `rho`.
      change rho (g * h) x = rho g (rho h x)
      rw [map_mul, Module.End.mul_apply]
  }
  let U : Subgroup G :=
    ⨅ i : Module.Free.ChooseBasisIndex R V, MulAction.stabilizer G (B i)
  have hU : U = rho.ker := by
    apply le_antisymm
    · intro g hg
      rw [MonoidHom.mem_ker]
      apply B.ext
      intro i
      exact MulAction.mem_stabilizer_iff.mp (Subgroup.mem_iInf.mp hg i)
    · intro g hg
      rw [Subgroup.mem_iInf]
      intro i
      rw [MulAction.mem_stabilizer_iff]
      -- The stabilizer uses the local action; expose its defining representation.
      change rho g (B i) = B i
      rw [MonoidHom.mem_ker.mp hg, Module.End.one_apply]
  rw [← hU, Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun i ↦ hopen (B i)

end Representation

namespace Field.absoluteGaloisGroup

universe u

variable {k : Type u} [Field k]

/-- Every open subgroup of an absolute Galois group contains the fixing subgroup of a
finite-dimensional normal subextension of the chosen algebraic closure. -/
theorem exists_finiteDimensional_normal_fixingSubgroup_le
    (U : Subgroup (Field.absoluteGaloisGroup k))
    (hU : IsOpen (U : Set (Field.absoluteGaloisGroup k))) :
    ∃ E : IntermediateField k (AlgebraicClosure k),
      FiniteDimensional k E ∧ Normal k E ∧ E.fixingSubgroup ≤ U := by
  let U' : Subgroup Gal(AlgebraicClosure k / k) := U
  have hU'_open : IsOpen (U' : Set Gal(AlgebraicClosure k / k)) := by
    exact hU
  have hU'_nhds := hU'_open.mem_nhds U'.one_mem
  rw [_root_.krullTopology_mem_nhds_one_iff_of_normal k (AlgebraicClosure k)] at hU'_nhds
  obtain ⟨E, hEfinite, hEnormal, hEU⟩ := hU'_nhds
  refine ⟨E, hEfinite, hEnormal, ?_⟩
  intro sigma hsigma
  exact hEU hsigma

/-- Every open subgroup of an absolute Galois group has finite quotient. -/
theorem finite_quotient_of_isOpen
    (U : Subgroup (Field.absoluteGaloisGroup k))
    (hU : IsOpen (U : Set (Field.absoluteGaloisGroup k))) :
    Finite (Field.absoluteGaloisGroup k ⧸ U) := by
  obtain ⟨E, hEfinite, hEnormal, hEU⟩ :=
    exists_finiteDimensional_normal_fixingSubgroup_le U hU
  let _ : FiniteDimensional k E := hEfinite
  let _ : Normal k E := hEnormal
  let _ : Finite Gal(E / k) := (AlgEquiv.fintype k E).finite
  have hEindex : E.fixingSubgroup.FiniteIndex := by
    rw [← E.restrictNormalHom_ker]
    infer_instance
  have hUindex : U.FiniteIndex :=
    @Subgroup.finiteIndex_of_le _ _ E.fixingSubgroup U hEindex hEU
  exact @Subgroup.finite_quotient_of_finiteIndex _ _ U hUindex

end Field.absoluteGaloisGroup

namespace TauCeti.GaloisLatticeCat

universe u

variable {k : Type u} [Field k]

/-- The module structure stored in the bundled representation. -/
noncomputable local instance storedModule (M : GaloisLatticeCat k) : Module ℤ M.obj :=
  M.obj.hV2

/-- The kernel of the absolute-Galois representation on a Galois lattice is open. -/
theorem isOpen_ker_ρ (M : GaloisLatticeCat k) :
    IsOpen (M.obj.ρ.ker : Set (Field.absoluteGaloisGroup k)) := by
  have hM := (galoisLatticeProperty_iff k M.obj).mp M.property
  let _ : Module.Free ℤ M.obj := hM.1.1
  let _ : Module.Finite ℤ M.obj := hM.1.2
  exact Representation.isOpen_ker_of_finite M.obj.ρ hM.2

/-- The finite quotient of the absolute Galois group that acts faithfully on a Galois lattice. -/
abbrev actionQuotient (M : GaloisLatticeCat k) :=
  Field.absoluteGaloisGroup k ⧸ M.obj.ρ.ker

/-- The quotient of the absolute Galois group acting on a Galois lattice is finite. -/
noncomputable instance instFiniteActionQuotient (M : GaloisLatticeCat k) :
    Finite (actionQuotient M) :=
  Field.absoluteGaloisGroup.finite_quotient_of_isOpen M.obj.ρ.ker (isOpen_ker_ρ M)

/-- The representation of the finite action quotient induced by a Galois lattice. It is
faithful by construction, since the quotient is by the kernel of the original action. -/
noncomputable def actionQuotientRepresentation (M : GaloisLatticeCat k) :
    Representation ℤ (actionQuotient M) M.obj :=
  QuotientGroup.lift M.obj.ρ.ker M.obj.ρ le_rfl

/-- The quotient representation acts on a coset through any representative. -/
@[simp]
theorem actionQuotientRepresentation_mk_apply (M : GaloisLatticeCat k)
    (sigma : Field.absoluteGaloisGroup k) (x : M.obj) :
    actionQuotientRepresentation M (sigma : actionQuotient M) x =
      M.obj.ρ sigma x := by
  simp [actionQuotientRepresentation]

/-- The action of a Galois lattice is the pullback of its finite-quotient representation. -/
theorem actionQuotientRepresentation_comp_mk (M : GaloisLatticeCat k) :
    (actionQuotientRepresentation M).comp (QuotientGroup.mk' M.obj.ρ.ker) = M.obj.ρ := by
  simp [actionQuotientRepresentation]

/-- The representation of the finite action quotient is faithful. -/
theorem actionQuotientRepresentation_injective (M : GaloisLatticeCat k) :
    Function.Injective (actionQuotientRepresentation M) := by
  exact (QuotientGroup.injective_lift_iff M.obj.ρ.ker M.obj.ρ le_rfl).2 rfl

end TauCeti.GaloisLatticeCat
