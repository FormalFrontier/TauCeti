/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.ClassGroup

/-!
# Quadratic conjugation (compatibility module)

This module preserves the public import path
`TauCeti.NumberTheory.NumberField.Quadratic.Conjugation` after the quadratic-conjugation
development was split into a directory:

* `Conjugation/Basic.lean` — the field/ring automorphism `quadraticConj` /
  `ringOfIntegersQuadraticConj` and its involutivity;
* `Conjugation/Norm.lean` — the norm-principality theorem `I · σI` is principal;
* `Conjugation/ClassGroup.lean` — the induced action on `Cl(𝓞 K)`: involution, inversion, and
  triviality on `Cl(𝓞 K)/Cl(𝓞 K)²`.

It re-exports the whole development (via `Conjugation.ClassGroup`, which transitively imports the
other two) so existing consumers importing the former single-file path continue to compile.
-/
