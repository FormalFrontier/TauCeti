/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Degree
public import TauCeti.NumberTheory.NumberField.InfinitePlace

/-!
# The candidate genus field of an imaginary quadratic field is totally complex

For squarefree `d`, `candidateGenusField hd` is a finite extension of `ℚ` inside `ℂ`, hence a number
field. When `d < 0` it contains a square root of `d < 0`
(`exists_mem_candidateGenusField_sq_eq`), so it is totally complex — a special case of
`TauCeti.NumberField.isTotallyComplex_of_sq_ratCast_of_neg`.

Every subfield of a totally complex field is again totally complex, so in particular the embedded
base `ℚ(√d)` is totally complex; a totally complex base has no real infinite places, so the
candidate genus field is unramified at every infinite place over its base. This settles the
archimedean half of the genus-field identification in the imaginary case.

## Main results

* `TauCeti.Multiquadratic.instNumberFieldCandidateGenusField`: the candidate genus field is a number
  field.
* `TauCeti.Multiquadratic.isTotallyComplex_candidateGenusField`: for `d < 0` it is totally complex.
-/

public section

open NumberField

namespace TauCeti.Multiquadratic

/-- The candidate genus field is a number field: a finite extension of `ℚ` (inside `ℂ`, so of
characteristic zero). -/
noncomputable instance instNumberFieldCandidateGenusField {d : ℤ} {hd : Squarefree d} :
    NumberField (candidateGenusField hd) where
  to_charZero := inferInstance
  to_finiteDimensional := finiteDimensional_candidateGenusField

/-- **The candidate genus field of an imaginary quadratic field is totally complex.** For squarefree
`d < 0`, `candidateGenusField hd` contains a square root of the negative rational `d`, so no
embedding into `ℂ` is real. -/
theorem isTotallyComplex_candidateGenusField {d : ℤ} (hd : Squarefree d) (hneg : d < 0) :
    IsTotallyComplex (candidateGenusField hd) := by
  obtain ⟨x, hxmem, hx2⟩ := exists_mem_candidateGenusField_sq_eq hd
  refine TauCeti.NumberField.isTotallyComplex_of_sq_ratCast_of_neg
    (x := (⟨x, hxmem⟩ : candidateGenusField hd)) (r := ((d : ℤ) : ℚ)) ?_ (by exact_mod_cast hneg)
  apply Subtype.ext
  push_cast
  exact_mod_cast hx2

end TauCeti.Multiquadratic
