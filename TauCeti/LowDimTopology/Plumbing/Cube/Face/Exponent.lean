/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Cube.Generator

/-!
# Exponent sums around plumbing-lattice face squares

The cubical generators for lattice homology have two codimension-one faces in each direction:
a lower face and an upper face. The `U`-exponents attached to these faces are differences between
the cube weight and the face weight. This file records the corresponding codimension-two
bookkeeping: in a square determined by two distinct directions, the sum of the two exponents along
one path equals the sum along the other path.

These identities are the weight part of the standard `∂² = 0` cubical cancellation in Némethi's
lattice homology. `CubeGenerator.lean` already proves that the two paths around each square reach
the same codimension-two generator; the lemmas here add that they also carry the same total
`U`-power.

## Main results

* `TauCeti.PlumbingCube.characteristicLowerFaceExponent_add_lowerFace_comm`: lower-lower square.
* `TauCeti.PlumbingCube.characteristicUpperFaceExponent_add_upperFace_comm`: upper-upper square.
* `TauCeti.PlumbingCube.characteristicLowerFaceExponent_add_upperFace_comm`: lower-then-upper
  equals upper-then-lower.
* `TauCeti.PlumbingCube.characteristicUpperFaceExponent_add_lowerFace_comm`: upper-then-lower
  equals lower-then-upper.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), whose differential is built from cubical face weights of a plumbing lattice.
The face-exponent convention follows Némethi, [arXiv:0709.0841](https://arxiv.org/abs/0709.0841).
-/

public section

namespace TauCeti

namespace PlumbingCube

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (P : PlumbingGraph V) (k : P.characteristicVectors)
variable (C : PlumbingCube V) {v w : V}

/-- The lower-face exponent, cast back to `ℤ`, is the difference between the bundled cube weight
and the lower face weight. -/
theorem characteristicLowerFaceExponent_natCast_lowerFace
    (hv : v ∈ C.directions) :
    (characteristicLowerFaceExponent P k C v : ℤ) =
      characteristicWeight P k C - characteristicWeight P k (C.lowerFace v hv) := by
  rw [characteristicLowerFaceExponent_natCast]
  have hface : C.eraseDirection v = C.lowerFace v hv := by
    apply PlumbingCube.ext
    · simp
    · simp
  rw [hface]

/-- The lower-lower codimension-two square has the same total `U`-exponent along either path. -/
theorem characteristicLowerFaceExponent_add_lowerFace_comm
    (hv : v ∈ C.directions) (hw : w ∈ C.directions) (hne : v ≠ w) :
    characteristicLowerFaceExponent P k C v +
        characteristicLowerFaceExponent P k (C.lowerFace v hv) w =
      characteristicLowerFaceExponent P k C w +
        characteristicLowerFaceExponent P k (C.lowerFace w hw) v := by
  apply Nat.cast_injective (R := ℤ)
  rw [Int.natCast_add, Int.natCast_add]
  rw [characteristicLowerFaceExponent_natCast_lowerFace P k C hv,
    characteristicLowerFaceExponent_natCast_lowerFace P k (C.lowerFace v hv)
      (by rw [lowerFace_directions]; exact Finset.mem_erase_of_ne_of_mem hne.symm hw),
    characteristicLowerFaceExponent_natCast_lowerFace P k C hw,
    characteristicLowerFaceExponent_natCast_lowerFace P k (C.lowerFace w hw)
      (by rw [lowerFace_directions]; exact Finset.mem_erase_of_ne_of_mem hne hv)]
  rw [C.lowerFace_lowerFace_comm hv hw hne]
  omega

/-- The upper-upper codimension-two square has the same total `U`-exponent along either path. -/
theorem characteristicUpperFaceExponent_add_upperFace_comm
    (hv : v ∈ C.directions) (hw : w ∈ C.directions) (hne : v ≠ w) :
    characteristicUpperFaceExponent P k C (v := v) hv +
        characteristicUpperFaceExponent P k (C.upperFace v hv)
          (v := w)
          (by rw [upperFace_directions]; exact Finset.mem_erase_of_ne_of_mem hne.symm hw) =
      characteristicUpperFaceExponent P k C (v := w) hw +
        characteristicUpperFaceExponent P k (C.upperFace w hw)
          (v := v)
          (by rw [upperFace_directions]; exact Finset.mem_erase_of_ne_of_mem hne hv) := by
  apply Nat.cast_injective (R := ℤ)
  rw [Int.natCast_add, Int.natCast_add]
  rw [characteristicUpperFaceExponent_natCast, characteristicUpperFaceExponent_natCast,
    characteristicUpperFaceExponent_natCast, characteristicUpperFaceExponent_natCast]
  rw [C.upperFace_upperFace_comm hv hw hne]
  omega

/-- The lower-then-upper mixed codimension-two square has the same total `U`-exponent as the
upper-then-lower path to the same corner. -/
theorem characteristicLowerFaceExponent_add_upperFace_comm
    (hv : v ∈ C.directions) (hw : w ∈ C.directions) (hne : v ≠ w) :
    characteristicLowerFaceExponent P k C v +
        characteristicUpperFaceExponent P k (C.lowerFace v hv)
          (v := w)
          (by rw [lowerFace_directions]; exact Finset.mem_erase_of_ne_of_mem hne.symm hw) =
      characteristicUpperFaceExponent P k C (v := w) hw +
        characteristicLowerFaceExponent P k (C.upperFace w hw) v := by
  apply Nat.cast_injective (R := ℤ)
  rw [Int.natCast_add, Int.natCast_add]
  rw [characteristicLowerFaceExponent_natCast_lowerFace P k C hv,
    characteristicUpperFaceExponent_natCast, characteristicUpperFaceExponent_natCast,
    characteristicLowerFaceExponent_natCast_lowerFace P k (C.upperFace w hw)
      (by rw [upperFace_directions]; exact Finset.mem_erase_of_ne_of_mem hne hv)]
  rw [C.lowerFace_upperFace_comm hv hw hne]
  omega

/-- The upper-then-lower mixed codimension-two square has the same total `U`-exponent as the
lower-then-upper path to the same corner. -/
theorem characteristicUpperFaceExponent_add_lowerFace_comm
    (hv : v ∈ C.directions) (hw : w ∈ C.directions) (hne : v ≠ w) :
    characteristicUpperFaceExponent P k C (v := v) hv +
        characteristicLowerFaceExponent P k (C.upperFace v hv) w =
      characteristicLowerFaceExponent P k C w +
        characteristicUpperFaceExponent P k (C.lowerFace w hw)
          (v := v)
          (by rw [lowerFace_directions]; exact Finset.mem_erase_of_ne_of_mem hne hv) := by
  simpa [add_comm] using (characteristicLowerFaceExponent_add_upperFace_comm
    (P := P) (k := k) (C := C) (v := w) (w := v) hw hv hne.symm).symm

end PlumbingCube

end TauCeti
