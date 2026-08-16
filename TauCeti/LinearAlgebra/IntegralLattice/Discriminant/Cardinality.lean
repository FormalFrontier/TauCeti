/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Group
public import TauCeti.LinearAlgebra.IntegralLattice.Gram

/-!
# Cardinality of an integral lattice's discriminant group

For a nondegenerate integral lattice `L`, the order of its discriminant group is the absolute
value of any Gram determinant:

```text
#(Lᵛ / L) = |det Gram(L)|.
```

The proof uses Mathlib's quotient-cardinality theorem for full-rank free `ℤ`-submodules.  Given
a carrier basis `b`, the corresponding bilinear dual basis is a basis of `Lᵛ`, while `b` itself
gives a basis of the copy of `L` inside `Lᵛ`.  The change-of-basis matrix between them is the
Gram matrix of `b`: the coefficient of `b j` along the dual vector indexed by `i` is
`B(b j, b i)`, which equals `B(b i, b j)` by symmetry.

## Main results

* `TauCeti.IntegralLattice.carrierInDualBasis`: a carrier basis, regarded as a basis of the copy
  of the carrier inside the dual carrier.
* `TauCeti.IntegralLattice.dualCarrierBasis_toMatrix_carrierInDualBasis`: the associated
  change-of-basis matrix is the Gram matrix.
* `TauCeti.IntegralLattice.natCard_discriminantGroup`: the discriminant-group cardinality is the
  lattice discriminant.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md` (Layer 2).
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

open Classical in
/-- A basis of the carrier, regarded as a basis of its copy inside the dual carrier. -/
noncomputable def carrierInDualBasis (L : IntegralLattice V) {ι : Type v}
    (b : Basis ι ℤ L) : Basis ι ℤ L.carrierInDual :=
  b.map L.carrierInDualEquiv.symm

open Classical in
/-- The vector of `carrierInDualBasis` indexed by `i` has underlying carrier vector `b i`. -/
@[simp]
theorem carrierInDualBasis_apply (L : IntegralLattice V) {ι : Type v}
    (b : Basis ι ℤ L) (i : ι) :
    (L.carrierInDualBasis b i : L.dualCarrier) = ⟨b i, L.le_dualCarrier (b i).property⟩ := by
  apply Subtype.ext
  exact L.coe_carrierInDualEquiv_symm_apply (b i)

open Classical in
/-- The ambient rational vector underlying `carrierInDualBasis b i` is `b i`. -/
@[simp]
theorem coe_carrierInDualBasis (L : IntegralLattice V) {ι : Type v}
    (b : Basis ι ℤ L) (i : ι) :
    ((L.carrierInDualBasis b i : L.dualCarrier) : V) = b i := by
  exact L.coe_carrierInDualEquiv_symm_apply (b i)

open Classical in
/-- The change-of-basis matrix from the dual basis to the embedded carrier basis is the Gram
matrix. -/
theorem dualCarrierBasis_toMatrix_carrierInDualBasis (L : IntegralLattice V)
    [L.IsNondegenerate] {ι : Type v} [Finite ι]
    (b : Basis ι ℤ L) :
    (L.dualCarrierBasis b).toMatrix
        ((↑) ∘ L.carrierInDualBasis b) = L.gramMatrix b := by
  ext i j
  rw [Basis.toMatrix_apply]
  apply Int.cast_injective (α := ℚ)
  rw [L.intCast_gramMatrix_apply]
  simp only [L.dualCarrierBasis_repr, Function.comp_apply, Basis.dualBasis_repr,
    L.dualPairingEquiv_cast, coe_carrierInDualBasis]
  exact L.isSymm.eq _ _

open Classical in
/-- The determinant of the carrier basis inside the dual basis is the signed Gram determinant. -/
theorem dualCarrierBasis_det_carrierInDualBasis (L : IntegralLattice V)
    [L.IsNondegenerate] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ L) :
    (L.dualCarrierBasis b).det ((↑) ∘ L.carrierInDualBasis b) = L.gramDet b := by
  rw [Basis.det_apply, L.dualCarrierBasis_toMatrix_carrierInDualBasis b, L.gramDet_def]

open Classical in
/-- The discriminant group has cardinality equal to the absolute value of the Gram determinant in
any carrier basis. -/
theorem natCard_discriminantGroup_eq_natAbs_gramDet (L : IntegralLattice V)
    [L.IsNondegenerate] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ L) :
    Nat.card L.DiscriminantGroup = (L.gramDet b).natAbs := by
  rw [← L.dualCarrierBasis_det_carrierInDualBasis b]
  exact (Submodule.natAbs_det_basis_change (L.dualCarrierBasis b) L.carrierInDual
    (L.carrierInDualBasis b)).symm

/-- **The order of the discriminant group is the lattice discriminant.** -/
@[simp]
theorem natCard_discriminantGroup (L : IntegralLattice V) [L.IsNondegenerate] :
    Nat.card L.DiscriminantGroup = L.discriminant := by
  classical
  rw [L.natCard_discriminantGroup_eq_natAbs_gramDet (Module.Free.chooseBasis ℤ L),
    L.discriminant_eq_natAbs_gramDet (Module.Free.chooseBasis ℤ L)]

/-- The discriminant group of a lattice constructed from a nonsingular integral symmetric matrix
has cardinality equal to the absolute value of that matrix's determinant. -/
@[simp]
theorem natCard_discriminantGroup_ofGramMatrix {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm) (hdet : G.det ≠ 0) :
    Nat.card (ofGramMatrix b G hG).DiscriminantGroup = G.det.natAbs := by
  let hnondegenerate : (ofGramMatrix b G hG).IsNondegenerate :=
    ⟨(determinant_ne_zero_iff _).mp (by simpa using hdet)⟩
  rw [@natCard_discriminantGroup V _ _ (ofGramMatrix b G hG) hnondegenerate,
    discriminant_ofGramMatrix]

end TauCeti.IntegralLattice
