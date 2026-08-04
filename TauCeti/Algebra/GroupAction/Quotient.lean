/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Stabilizers and orbits of the translation action on `G ⧸ H`

A group `G` acts on the quotient `G ⧸ H` by translation, and so does any subgroup `K` of `G`.
This file records two basic facts about that action.

The stabilizer of the coset `sH` in `G` is the conjugate subgroup `sHs⁻¹`
(`TauCeti.stabilizer_quotientGroup_mk`); this is Mathlib's `MulAction.stabilizer_quotient`,
which covers the trivial coset, transported along
`MulAction.stabilizer_smul_eq_stabilizer_map_conj`.

The `K`-orbit of the coset `sH` is the image of the double coset `KsH`
(`TauCeti.preimage_orbit_eq_doubleCoset`), so the partition of `G ⧸ H` into `K`-orbits is the
partition of `G` into `K`-`H` double cosets.

## Main statements

* `TauCeti.stabilizer_quotientGroup_mk`: the stabilizer of `sH` in `G` is `sHs⁻¹`.
* `TauCeti.mem_doubleCoset_iff_mk_mem_orbit`: an element lies in `KsH` exactly when its coset
  lies in the `K`-orbit of `sH`.
* `TauCeti.preimage_orbit_eq_doubleCoset`: the double coset `KsH` is the preimage of the
  `K`-orbit of `sH`.
-/

public section

open MulAction
open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G]

/-- The stabilizer of the coset `sH`, for the translation action of `G` on `G ⧸ H`, is the
conjugate subgroup `sHs⁻¹`.  This is Mathlib's `MulAction.stabilizer_quotient` transported off the
trivial coset along `MulAction.stabilizer_smul_eq_stabilizer_map_conj`. -/
theorem stabilizer_quotientGroup_mk (H : Subgroup G) (s : G) :
    stabilizer G ((s : G ⧸ H)) = MulAut.conj s • H := by
  have hs : ((s : G) : G ⧸ H) = s • ((1 : G) : G ⧸ H) := by
    rw [Quotient.smul_coe, smul_eq_mul, mul_one]
  rw [hs, stabilizer_smul_eq_stabilizer_map_conj, stabilizer_quotient,
    Subgroup.pointwise_smul_def]
  rfl

/-- The double coset `KsH` consists exactly of those `x` whose class in `G ⧸ H` lies in the
`K`-orbit of the class of `s`. -/
theorem mem_doubleCoset_iff_mk_mem_orbit (s : G) (H K : Subgroup G) {x : G} :
    x ∈ DoubleCoset.doubleCoset s (K : Set G) (H : Set G) ↔
      ((x : G ⧸ H)) ∈ orbit K ((s : G ⧸ H)) := by
  rw [DoubleCoset.mem_doubleCoset, mem_orbit_iff]
  -- `K` acts on `G ⧸ H` through `Subgroup.subtype K` (`MulAction.mulLeftCosetsCompSubtypeVal`),
  -- so `MulAction.compHom_smul_def` is what turns a `K`-translate back into a `G`-translate.
  constructor
  · rintro ⟨k, hk, h, hh, rfl⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [compHom_smul_def (Subgroup.subtype K), Subgroup.coe_subtype, Quotient.smul_coe,
      smul_eq_mul, QuotientGroup.eq]
    simpa [mul_assoc] using hh
  · rintro ⟨k, hkx⟩
    rw [compHom_smul_def (Subgroup.subtype K), Subgroup.coe_subtype, Quotient.smul_coe,
      smul_eq_mul, QuotientGroup.eq] at hkx
    exact ⟨k, k.2, ((k : G) * s)⁻¹ * x, hkx, (mul_inv_cancel_left _ _).symm⟩

/-- The double coset `KsH` is the preimage, under `G → G ⧸ H`, of the `K`-orbit of the coset `sH`.
So the partition of `G` into `K`-`H` double cosets is the partition of `G ⧸ H` into `K`-orbits. -/
theorem preimage_orbit_eq_doubleCoset (s : G) (H K : Subgroup G) :
    QuotientGroup.mk ⁻¹' (orbit K ((s : G ⧸ H)))
      = DoubleCoset.doubleCoset s (K : Set G) (H : Set G) :=
  Set.ext fun _ => (mem_doubleCoset_iff_mk_mem_orbit s H K).symm

end TauCeti
