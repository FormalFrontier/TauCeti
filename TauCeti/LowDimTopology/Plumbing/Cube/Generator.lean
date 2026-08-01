/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LowDimTopology.Plumbing.Cube.Weight.Recursion

/-!
# Plumbing-lattice cube generators and their faces

This file packages the cubical generators used in Némethi's lattice homology. A cube generator is
the pair of a lattice base point `x : V → ℤ` and a finite set `S : Finset V` of basis directions.
Its codimension-one faces in a direction `v ∈ S` are the lower face `(x, S.erase v)` and the
upper face `(x + E_v, S.erase v)`.

Taking faces in two distinct present directions `v ≠ w` produces a codimension-two face, and the
order of the two directions does not matter: `PlumbingCube.lowerFace_lowerFace_comm`,
`PlumbingCube.upperFace_upperFace_comm`, `PlumbingCube.lowerFace_upperFace_comm`, and
`PlumbingCube.upperFace_lowerFace_comm` identify the two ways of reaching each corner. These
commuting squares are the geometric skeleton of the lattice-homology differential's `∂² = 0`: the
boundary of the boundary revisits each codimension-two face along the two edges of a square, and
the squares identify those two contributions as the *same* generator (before the `U`-power
bookkeeping, which lives in the weight files). All four corners share the direction set
`(S.erase v).erase w`, drop the cubical dimension by two, and have vertices among those of the
ambient cube.

The earlier plumbing files define vertices, characteristic cube weights, and the lower/upper
face exponents as functions of `(x, S)`. This file provides the bundled generator API that the
lattice-homology differential can use directly.

## Main definitions

* `TauCeti.PlumbingCube`: a bundled plumbing-lattice cube generator.
* `TauCeti.PlumbingCube.eraseDirection`: the raw lower cube obtained by erasing a direction.
* `TauCeti.PlumbingCube.lowerFace` and `TauCeti.PlumbingCube.upperFace`: the two
  codimension-one faces in a present direction.
* `TauCeti.PlumbingCube.characteristicWeight`: the characteristic cube weight of a bundled
  generator.
* `TauCeti.PlumbingCube.characteristicLowerFaceExponent` and
  `TauCeti.PlumbingCube.characteristicUpperFaceExponent`: the bundled face exponents.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), whose opening item asks for Némethi's lattice (co)homology from lattice
points and weight functions. The lower/upper face convention and exponents are the standard
cubical-boundary data in Némethi, [arXiv:0709.0841](https://arxiv.org/abs/0709.0841).
-/

public section

namespace TauCeti

/-- A plumbing-lattice cube generator: a lattice base point together with a finite set of basis
directions. In Némethi's lattice homology this is the cubical generator usually denoted by a pair
`(x, S)`. -/
structure PlumbingCube (V : Type*) where
  /-- The lattice base point of the cube. -/
  base : V → ℤ
  /-- The finite set of basis directions spanning the cube. -/
  directions : Finset V

namespace PlumbingCube

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- Two plumbing cubes are equal when their base points and direction sets agree. -/
@[ext]
theorem ext {C D : PlumbingCube V} (hbase : C.base = D.base)
    (hdirections : C.directions = D.directions) : C = D := by
  cases C
  cases D
  simp_all

/-- The cubical dimension of a plumbing cube, namely the number of basis directions. -/
abbrev dimension (C : PlumbingCube V) : ℕ :=
  C.directions.card

/-- The raw lower cube obtained by keeping the base point and erasing a direction from the direction
set. If the direction is absent, this is the original cube. -/
irreducible_def eraseDirection (C : PlumbingCube V) (v : V) : PlumbingCube V where
  base := C.base
  directions := C.directions.erase v

/-- The lower codimension-one face in a present direction `v`: keep the base point and remove `v`
from the direction set. -/
irreducible_def lowerFace (C : PlumbingCube V) (v : V)
    (_hv : v ∈ C.directions) : PlumbingCube V :=
  C.eraseDirection v

/-- The upper codimension-one face in a present direction `v`: shift the base point by `E_v` and
remove `v` from the direction set. -/
irreducible_def upperFace (C : PlumbingCube V) (v : V)
    (_hv : v ∈ C.directions) : PlumbingCube V where
  base := C.base + Pi.single v (1 : ℤ)
  directions := C.directions.erase v

omit [DecidableEq V] in
@[simp]
theorem dimension_mk (x : V → ℤ) (S : Finset V) :
    dimension ({ base := x, directions := S } : PlumbingCube V) = S.card :=
  rfl

omit [DecidableEq V] in
/-- The dimension of a plumbing cube is at most the number of plumbing vertices. -/
theorem dimension_le_card [Fintype V] (C : PlumbingCube V) :
    C.dimension ≤ Fintype.card V := by
  classical
  exact Finset.card_le_univ C.directions

@[simp]
theorem eraseDirection_mk (x : V → ℤ) (S : Finset V) (v : V) :
    eraseDirection ({ base := x, directions := S } : PlumbingCube V) v =
      ({ base := x, directions := S.erase v } : PlumbingCube V) :=
  by simp [eraseDirection_def]

@[simp]
theorem lowerFace_mk (x : V → ℤ) (S : Finset V) (v : V) (hv : v ∈ S) :
    lowerFace ({ base := x, directions := S } : PlumbingCube V) v hv =
      ({ base := x, directions := S.erase v } : PlumbingCube V) :=
  by simp [lowerFace_def]

@[simp]
theorem upperFace_mk (x : V → ℤ) (S : Finset V) (v : V) (hv : v ∈ S) :
    upperFace ({ base := x, directions := S } : PlumbingCube V) v hv =
      ({ base := x + Pi.single v (1 : ℤ), directions := S.erase v } : PlumbingCube V) :=
  by simp [upperFace_def]

@[simp]
theorem eraseDirection_base (C : PlumbingCube V) (v : V) :
    (C.eraseDirection v).base = C.base :=
  by simp [eraseDirection_def]

@[simp]
theorem eraseDirection_directions (C : PlumbingCube V) (v : V) :
    (C.eraseDirection v).directions = C.directions.erase v :=
  by simp [eraseDirection_def]

@[simp]
theorem lowerFace_base (C : PlumbingCube V) (v : V) (hv : v ∈ C.directions) :
    (C.lowerFace v hv).base = C.base :=
  by simp [lowerFace_def]

@[simp]
theorem lowerFace_directions (C : PlumbingCube V) (v : V) (hv : v ∈ C.directions) :
    (C.lowerFace v hv).directions = C.directions.erase v :=
  by simp [lowerFace_def]

@[simp]
theorem upperFace_base (C : PlumbingCube V) (v : V) (hv : v ∈ C.directions) :
    (C.upperFace v hv).base = C.base + Pi.single v (1 : ℤ) :=
  by simp [upperFace_def]

@[simp]
theorem upperFace_directions (C : PlumbingCube V) (v : V) (hv : v ∈ C.directions) :
    (C.upperFace v hv).directions = C.directions.erase v :=
  by simp [upperFace_def]

variable [DecidableEq (V → ℤ)]

/-- The vertices of a bundled plumbing cube. -/
noncomputable irreducible_def vertices (C : PlumbingCube V) : Finset (V → ℤ) :=
  PlumbingGraph.cubeVertices C.base C.directions

@[simp]
theorem vertices_mk (x : V → ℤ) (S : Finset V) :
    vertices ({ base := x, directions := S } : PlumbingCube V) =
      PlumbingGraph.cubeVertices x S :=
  by simp [vertices_def]

/-- Membership in the vertices of a bundled cube, expressed by a direction subset. -/
theorem mem_vertices (C : PlumbingCube V) (y : V → ℤ) :
    y ∈ C.vertices ↔ ∃ T ⊆ C.directions, PlumbingGraph.cubeVertex C.base T = y :=
  by simpa [vertices_def] using PlumbingGraph.mem_cubeVertices C.base C.directions y

/-- The base point is a vertex of every bundled cube. -/
@[simp]
theorem base_mem_vertices (C : PlumbingCube V) :
    C.base ∈ C.vertices :=
  by simp [vertices_def]

/-- The lower face's vertices are vertices of the ambient cube. -/
theorem vertices_eraseDirection_subset (C : PlumbingCube V) (v : V) :
    (C.eraseDirection v).vertices ⊆ C.vertices :=
  by
    simpa [vertices_def, eraseDirection_base, eraseDirection_directions] using
      PlumbingGraph.cubeVertices_subset (Finset.erase_subset v C.directions) C.base

/-- The lower face's vertices are vertices of the ambient cube. -/
theorem vertices_lowerFace_subset (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    (C.lowerFace v hv).vertices ⊆ C.vertices :=
  by simpa [lowerFace_def] using C.vertices_eraseDirection_subset v

/-- The upper face's vertices are vertices of the ambient cube when the face direction belongs to
the ambient cube. -/
theorem vertices_upperFace_subset (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    (C.upperFace v hv).vertices ⊆ C.vertices :=
  by
    simpa [vertices_def, upperFace_base, upperFace_directions] using
      PlumbingGraph.cubeVertices_upperFace_subset (x := C.base) hv

/-- The vertices of a bundled cube split as the union of the vertices of its lower and upper faces
in any present direction. -/
theorem vertices_eq_union_faces (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    C.vertices = (C.lowerFace v hv).vertices ∪ (C.upperFace v hv).vertices :=
  by
    simpa [vertices_def, lowerFace_base, lowerFace_directions, upperFace_base,
      upperFace_directions] using
      PlumbingGraph.cubeVertices_eq_union_erase hv C.base

omit [DecidableEq (V → ℤ)] in
/-- Removing a present direction drops the cubical dimension by one for the lower face. -/
@[simp]
theorem dimension_lowerFace_of_mem (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    (C.lowerFace v hv).dimension = C.dimension - 1 := by
  rw [dimension, dimension, lowerFace_directions, Finset.card_erase_of_mem hv]

omit [DecidableEq (V → ℤ)] in
/-- Removing a present direction drops the cubical dimension by one for the upper face. -/
@[simp]
theorem dimension_upperFace_of_mem (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    (C.upperFace v hv).dimension = C.dimension - 1 := by
  rw [dimension, dimension, upperFace_directions, Finset.card_erase_of_mem hv]

/-- The characteristic cube weight of a bundled plumbing cube. -/
noncomputable irreducible_def characteristicWeight [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) : ℤ :=
  P.characteristicCubeWeight k C.base C.directions

@[simp]
theorem characteristicWeight_mk [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (x : V → ℤ) (S : Finset V) :
    characteristicWeight P k ({ base := x, directions := S } : PlumbingCube V) =
      P.characteristicCubeWeight k x S :=
  by simp [characteristicWeight_def]

/-- The nonnegative `U`-exponent contributed by the raw lower cube obtained by erasing a direction.
When the direction is present, this is the exponent of the lower face. -/
noncomputable irreducible_def characteristicLowerFaceExponent [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) (v : V) : ℕ :=
  P.characteristicLowerFaceExponent k C.base C.directions v

/-- The nonnegative `U`-exponent contributed by the upper face of a bundled cube. -/
noncomputable irreducible_def characteristicUpperFaceExponent [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V}
    (hv : v ∈ C.directions) : ℕ :=
  P.characteristicUpperFaceExponent k C.base C.directions hv

@[simp]
theorem characteristicLowerFaceExponent_mk [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (x : V → ℤ) (S : Finset V) (v : V) :
    characteristicLowerFaceExponent P k ({ base := x, directions := S } : PlumbingCube V) v =
      P.characteristicLowerFaceExponent k x S v :=
  by simp [characteristicLowerFaceExponent_def]

@[simp]
theorem characteristicUpperFaceExponent_mk [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (x : V → ℤ) (S : Finset V) {v : V} (hv : v ∈ S) :
    characteristicUpperFaceExponent P k ({ base := x, directions := S } : PlumbingCube V) hv =
      P.characteristicUpperFaceExponent k x S hv :=
  by simp [characteristicUpperFaceExponent_def]

/-- The lower exponent, cast back to `ℤ`, is the difference between the bundled cube weight and the
weight after erasing the direction. -/
@[simp]
theorem characteristicLowerFaceExponent_natCast [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) (v : V) :
    (characteristicLowerFaceExponent P k C v : ℤ) =
      characteristicWeight P k C - characteristicWeight P k (C.eraseDirection v) :=
  by
    simp [characteristicLowerFaceExponent_def, characteristicWeight_def, eraseDirection_base,
      eraseDirection_directions]

/-- The upper-face exponent, cast back to `ℤ`, is the difference between the bundled cube weight
and the upper face weight. -/
@[simp]
theorem characteristicUpperFaceExponent_natCast [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    (characteristicUpperFaceExponent P k C hv : ℤ) =
      characteristicWeight P k C - characteristicWeight P k (C.upperFace v hv) :=
  by
    simp [characteristicUpperFaceExponent_def, characteristicWeight_def, upperFace_base,
      upperFace_directions]

/-- The lower exponent is zero exactly when erasing the direction leaves the bundled weight
unchanged. -/
theorem characteristicLowerFaceExponent_eq_zero_iff [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) (v : V) :
    characteristicLowerFaceExponent P k C v = 0 ↔
      characteristicWeight P k C = characteristicWeight P k (C.eraseDirection v) :=
  by
    simpa [characteristicLowerFaceExponent_def, characteristicWeight_def, eraseDirection_base,
      eraseDirection_directions] using
      P.characteristicLowerFaceExponent_eq_zero_iff (k := k) (x := C.base) (S := C.directions)
        (v := v)

/-- The upper-face exponent is zero exactly when the upper face has the same bundled weight as the
ambient cube. -/
theorem characteristicUpperFaceExponent_eq_zero_iff [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    characteristicUpperFaceExponent P k C hv = 0 ↔
      characteristicWeight P k C = characteristicWeight P k (C.upperFace v hv) :=
  by
    simpa [characteristicUpperFaceExponent_def, characteristicWeight_def, upperFace_base,
      upperFace_directions] using
      P.characteristicUpperFaceExponent_eq_zero_iff (k := k) (x := C.base) (S := C.directions)
        hv

/-- In any bundled cube direction, at least one face exponent is zero. -/
@[simp]
theorem min_characteristicFaceExponent_eq_zero [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    min (characteristicLowerFaceExponent P k C v)
      (characteristicUpperFaceExponent P k C hv) = 0 :=
  by
    simp [characteristicLowerFaceExponent_def, characteristicUpperFaceExponent_def]

/-- Erasing a direction gives a cube whose characteristic weight is bounded by the ambient cube
weight. -/
theorem characteristicWeight_eraseDirection_le [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) (v : V) :
    characteristicWeight P k (C.eraseDirection v) ≤ characteristicWeight P k C :=
  by
    simpa [characteristicWeight_def, eraseDirection_base, eraseDirection_directions] using
      P.characteristicCubeWeight_mono k (Finset.erase_subset v C.directions) C.base

/-- The lower face's characteristic weight is bounded by the ambient cube weight. -/
theorem characteristicWeight_lowerFace_le [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    characteristicWeight P k (C.lowerFace v hv) ≤ characteristicWeight P k C :=
  by simpa [lowerFace_def] using characteristicWeight_eraseDirection_le P k C v

/-- The upper face's characteristic weight is bounded by the ambient cube weight. -/
theorem characteristicWeight_upperFace_le [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    characteristicWeight P k (C.upperFace v hv) ≤ characteristicWeight P k C :=
  by
    simpa [characteristicWeight_def, upperFace_base, upperFace_directions] using
      P.characteristicUpperFaceWeight_le (x := C.base) k hv

/-- In any present direction, the characteristic weight of a cube is the maximum of the weights
of its lower and upper faces. -/
theorem characteristicWeight_eq_max_faces [Fintype V] (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) :
    characteristicWeight P k C =
      max (characteristicWeight P k (C.lowerFace v hv))
        (characteristicWeight P k (C.upperFace v hv)) :=
  by
    simpa [characteristicWeight_def, lowerFace_base, lowerFace_directions, upperFace_base,
      upperFace_directions] using
      P.characteristicCubeWeight_eq_max_erase k C.base hv

/-! ### Codimension-two faces

Taking a face in two distinct present directions `v ≠ w` gives a codimension-two face. The four
corners (one per choice of lower/upper in each direction) are independent of the order in which the
directions are removed, so each corner is well defined; they share the direction set
`(C.directions.erase v).erase w`, drop the cubical dimension by two, and have vertices among those
of the ambient cube. These commuting squares are the standard cubical-boundary squares underlying
`∂² = 0` in Némethi's lattice homology, [arXiv:0709.0841](https://arxiv.org/abs/0709.0841). -/

variable (C : PlumbingCube V) {v w : V}

section
omit [DecidableEq (V → ℤ)]

/-- The two lower faces in distinct directions `v` and `w` agree: both are the cube based at
`C.base` with directions `(C.directions.erase v).erase w`. -/
theorem lowerFace_lowerFace_comm (hv : v ∈ C.directions) (hw : w ∈ C.directions) (hne : v ≠ w) :
    (C.lowerFace v hv).lowerFace w
        (by rw [lowerFace_directions]; exact Finset.mem_erase_of_ne_of_mem hne.symm hw) =
      (C.lowerFace w hw).lowerFace v
        (by rw [lowerFace_directions]; exact Finset.mem_erase_of_ne_of_mem hne hv) := by
  apply PlumbingCube.ext
  · simp
  · simp only [lowerFace_directions]
    exact Finset.erase_right_comm

/-- The two upper faces in distinct directions `v` and `w` agree: both are the cube based at
`C.base + E_v + E_w` with directions `(C.directions.erase v).erase w`, since the two basis shifts
commute. -/
theorem upperFace_upperFace_comm (hv : v ∈ C.directions) (hw : w ∈ C.directions) (hne : v ≠ w) :
    (C.upperFace v hv).upperFace w
        (by rw [upperFace_directions]; exact Finset.mem_erase_of_ne_of_mem hne.symm hw) =
      (C.upperFace w hw).upperFace v
        (by rw [upperFace_directions]; exact Finset.mem_erase_of_ne_of_mem hne hv) := by
  apply PlumbingCube.ext
  · simp only [upperFace_base]
    exact add_right_comm _ _ _
  · simp only [upperFace_directions]
    exact Finset.erase_right_comm

/-- Taking the lower face in direction `v` then the upper face in direction `w` agrees with taking
the upper face in direction `w` then the lower face in direction `v`: both are the mixed corner
based at `C.base + E_w`. -/
theorem lowerFace_upperFace_comm (hv : v ∈ C.directions) (hw : w ∈ C.directions) (hne : v ≠ w) :
    (C.lowerFace v hv).upperFace w
        (by rw [lowerFace_directions]; exact Finset.mem_erase_of_ne_of_mem hne.symm hw) =
      (C.upperFace w hw).lowerFace v
        (by rw [upperFace_directions]; exact Finset.mem_erase_of_ne_of_mem hne hv) := by
  apply PlumbingCube.ext
  · simp
  · simp only [upperFace_directions, lowerFace_directions]
    exact Finset.erase_right_comm

/-- Taking the upper face in direction `v` then the lower face in direction `w` agrees with taking
the lower face in direction `w` then the upper face in direction `v`: both are the mixed corner
based at `C.base + E_v`. -/
theorem upperFace_lowerFace_comm (hv : v ∈ C.directions) (hw : w ∈ C.directions) (hne : v ≠ w) :
    (C.upperFace v hv).lowerFace w
        (by rw [upperFace_directions]; exact Finset.mem_erase_of_ne_of_mem hne.symm hw) =
      (C.lowerFace w hw).upperFace v
        (by rw [lowerFace_directions]; exact Finset.mem_erase_of_ne_of_mem hne hv) := by
  apply PlumbingCube.ext
  · simp
  · simp only [upperFace_directions, lowerFace_directions]
    exact Finset.erase_right_comm

/-- The direction set of the lower-lower codimension-two face is the ambient direction set with the
two chosen directions removed. -/
theorem lowerFace_lowerFace_directions (hv : v ∈ C.directions)
    (hwv : w ∈ (C.lowerFace v hv).directions) :
    ((C.lowerFace v hv).lowerFace w hwv).directions = (C.directions.erase v).erase w := by
  simp

/-- The direction set of the upper-upper codimension-two face is the ambient direction set with the
two chosen directions removed. -/
theorem upperFace_upperFace_directions (hv : v ∈ C.directions)
    (hwv : w ∈ (C.upperFace v hv).directions) :
    ((C.upperFace v hv).upperFace w hwv).directions = (C.directions.erase v).erase w := by
  simp

/-- The direction set of the lower-upper codimension-two face is the ambient direction set with the
two chosen directions removed. -/
theorem lowerFace_upperFace_directions (hv : v ∈ C.directions)
    (hwv : w ∈ (C.lowerFace v hv).directions) :
    ((C.lowerFace v hv).upperFace w hwv).directions = (C.directions.erase v).erase w := by
  simp

/-- The direction set of the upper-lower codimension-two face is the ambient direction set with the
two chosen directions removed. -/
theorem upperFace_lowerFace_directions (hv : v ∈ C.directions)
    (hwv : w ∈ (C.upperFace v hv).directions) :
    ((C.upperFace v hv).lowerFace w hwv).directions = (C.directions.erase v).erase w := by
  simp

/-- The lower-lower codimension-two face keeps the ambient base point. -/
theorem lowerFace_lowerFace_base (hv : v ∈ C.directions)
    (hwv : w ∈ (C.lowerFace v hv).directions) :
    ((C.lowerFace v hv).lowerFace w hwv).base = C.base := by
  simp

/-- The upper-upper codimension-two face sits at the far corner `C.base + E_v + E_w`. -/
theorem upperFace_upperFace_base (hv : v ∈ C.directions)
    (hwv : w ∈ (C.upperFace v hv).directions) :
    ((C.upperFace v hv).upperFace w hwv).base = C.base + Pi.single v (1 : ℤ) + Pi.single w 1 := by
  simp

/-- The lower-upper codimension-two face sits at the mixed corner `C.base + E_w`. -/
theorem lowerFace_upperFace_base (hv : v ∈ C.directions)
    (hwv : w ∈ (C.lowerFace v hv).directions) :
    ((C.lowerFace v hv).upperFace w hwv).base = C.base + Pi.single w (1 : ℤ) := by
  simp

/-- The upper-lower codimension-two face sits at the mixed corner `C.base + E_v`. -/
theorem upperFace_lowerFace_base (hv : v ∈ C.directions)
    (hwv : w ∈ (C.upperFace v hv).directions) :
    ((C.upperFace v hv).lowerFace w hwv).base = C.base + Pi.single v (1 : ℤ) := by
  simp

/-- The lower-lower codimension-two face has cubical dimension two less than the ambient cube. -/
theorem dimension_lowerFace_lowerFace (hv : v ∈ C.directions)
    (hwv : w ∈ (C.lowerFace v hv).directions) :
    ((C.lowerFace v hv).lowerFace w hwv).dimension = C.dimension - 2 := by
  rw [dimension_lowerFace_of_mem, dimension_lowerFace_of_mem]
  omega

/-- The upper-upper codimension-two face has cubical dimension two less than the ambient cube. -/
theorem dimension_upperFace_upperFace (hv : v ∈ C.directions)
    (hwv : w ∈ (C.upperFace v hv).directions) :
    ((C.upperFace v hv).upperFace w hwv).dimension = C.dimension - 2 := by
  rw [dimension_upperFace_of_mem, dimension_upperFace_of_mem]
  omega

/-- The lower-upper codimension-two face has cubical dimension two less than the ambient cube. -/
theorem dimension_lowerFace_upperFace (hv : v ∈ C.directions)
    (hwv : w ∈ (C.lowerFace v hv).directions) :
    ((C.lowerFace v hv).upperFace w hwv).dimension = C.dimension - 2 := by
  rw [dimension_upperFace_of_mem, dimension_lowerFace_of_mem]
  omega

/-- The upper-lower codimension-two face has cubical dimension two less than the ambient cube. -/
theorem dimension_upperFace_lowerFace (hv : v ∈ C.directions)
    (hwv : w ∈ (C.upperFace v hv).directions) :
    ((C.upperFace v hv).lowerFace w hwv).dimension = C.dimension - 2 := by
  rw [dimension_lowerFace_of_mem, dimension_upperFace_of_mem]
  omega

end

/-- The vertices of the lower-lower codimension-two face are vertices of the ambient cube. -/
theorem vertices_lowerFace_lowerFace_subset (hv : v ∈ C.directions)
    (hwv : w ∈ (C.lowerFace v hv).directions) :
    ((C.lowerFace v hv).lowerFace w hwv).vertices ⊆ C.vertices :=
  ((C.lowerFace v hv).vertices_lowerFace_subset hwv).trans (C.vertices_lowerFace_subset hv)

/-- The vertices of the upper-upper codimension-two face are vertices of the ambient cube. -/
theorem vertices_upperFace_upperFace_subset (hv : v ∈ C.directions)
    (hwv : w ∈ (C.upperFace v hv).directions) :
    ((C.upperFace v hv).upperFace w hwv).vertices ⊆ C.vertices :=
  ((C.upperFace v hv).vertices_upperFace_subset hwv).trans (C.vertices_upperFace_subset hv)

/-- The vertices of the lower-upper codimension-two face are vertices of the ambient cube. -/
theorem vertices_lowerFace_upperFace_subset (hv : v ∈ C.directions)
    (hwv : w ∈ (C.lowerFace v hv).directions) :
    ((C.lowerFace v hv).upperFace w hwv).vertices ⊆ C.vertices :=
  ((C.lowerFace v hv).vertices_upperFace_subset hwv).trans (C.vertices_lowerFace_subset hv)

/-- The vertices of the upper-lower codimension-two face are vertices of the ambient cube. -/
theorem vertices_upperFace_lowerFace_subset (hv : v ∈ C.directions)
    (hwv : w ∈ (C.upperFace v hv).directions) :
    ((C.upperFace v hv).lowerFace w hwv).vertices ⊆ C.vertices :=
  ((C.upperFace v hv).vertices_lowerFace_subset hwv).trans (C.vertices_upperFace_subset hv)

end PlumbingCube

end TauCeti
