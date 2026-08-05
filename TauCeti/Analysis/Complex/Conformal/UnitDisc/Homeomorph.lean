/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Basic

/-!
# Unit-disc automorphisms as homeomorphisms

This file packages the standard unit-disc automorphisms from
`TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Basic` as homeomorphisms of
`Complex.UnitDisc`.  The underlying map is the existing equivalence
`unitDiscStandardAutomorphismEquiv`; this file adds the continuity API needed before treating
the disc automorphisms as a topological automorphism group in the Schwarz--Pick layer of the
conformal-mapping roadmap.

This L2 material is coordinated with the upstream Mathlib RMT effort in
leanprover-community/mathlib4#33505.  Mathlib already contains the preceding human-curated
work in `Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`;
this file only packages Tau Ceti's existing unit-disc automorphism formulas topologically.
-/

public section

namespace TauCeti

open _root_.Complex
open scoped ComplexConjugate

/--
The standard automorphism of the complex unit disc, bundled as a homeomorphism.

It is the composition of the Moebius homeomorphism sending `a` to `0` with the fixed
circle rotation by `u`.
-/
noncomputable def unitDiscStandardAutomorphismHomeomorph
    (u : Circle) (a : Complex.UnitDisc) : Complex.UnitDisc ≃ₜ Complex.UnitDisc :=
  (unitDiscMoebiusHomeomorph a).trans (Homeomorph.smul u)

/-- The standard automorphism homeomorphism applies by the existing equivalence formula. -/
@[simp]
lemma unitDiscStandardAutomorphismHomeomorph_apply
    (u : Circle) (a z : Complex.UnitDisc) :
    unitDiscStandardAutomorphismHomeomorph u a z =
      unitDiscStandardAutomorphismEquiv u a z :=
  by
  rw [unitDiscStandardAutomorphismEquiv_apply]
  calc
    unitDiscStandardAutomorphismHomeomorph u a z
        = Homeomorph.smul u (unitDiscMoebiusHomeomorph a z) := rfl
    _ = u • unitDiscMoebius a z := by
      rw [Homeomorph.smul_apply, unitDiscMoebiusHomeomorph_apply]

/-- The underlying equivalence of the standard automorphism homeomorphism is the existing one. -/
@[simp]
lemma unitDiscStandardAutomorphismHomeomorph_toEquiv
    (u : Circle) (a : Complex.UnitDisc) :
    (unitDiscStandardAutomorphismHomeomorph u a).toEquiv =
      unitDiscStandardAutomorphismEquiv u a :=
  by
    ext z
    exact congrArg (fun w : Complex.UnitDisc => (w : ℂ))
      (unitDiscStandardAutomorphismHomeomorph_apply u a z)

/-- The inverse standard automorphism homeomorphism is inverse rotation followed by the
inverse Moebius homeomorphism. -/
@[simp]
lemma unitDiscStandardAutomorphismHomeomorph_symm
    (u : Circle) (a : Complex.UnitDisc) :
    (unitDiscStandardAutomorphismHomeomorph u a).symm =
      (Homeomorph.smul u⁻¹).trans (unitDiscMoebiusHomeomorph (-a)) := by
  apply Homeomorph.ext
  intro z
  calc
    (unitDiscStandardAutomorphismHomeomorph u a).symm z
        = ((unitDiscStandardAutomorphismHomeomorph u a).toEquiv).symm z := rfl
    _ = unitDiscMoebiusHomeomorph (-a) ((Homeomorph.smul u⁻¹) z) := by
      rw [congrArg Equiv.symm (unitDiscStandardAutomorphismHomeomorph_toEquiv u a),
        unitDiscStandardAutomorphismEquiv_symm]
      calc
        unitDiscMoebiusEquiv (-a) ((MulAction.toPerm u⁻¹ : Equiv.Perm Complex.UnitDisc) z)
            = unitDiscMoebiusHomeomorph (-a) ((Homeomorph.smul u⁻¹) z) := by
          rw [unitDiscMoebiusEquiv_apply, unitDiscMoebiusHomeomorph_apply,
            Homeomorph.smul_apply, MulAction.toPerm_apply]

/-- The scalar formula for the standard disc-automorphism homeomorphism. -/
@[norm_cast]
lemma coe_unitDiscStandardAutomorphismHomeomorph_apply
    (u : Circle) (a z : Complex.UnitDisc) :
    (unitDiscStandardAutomorphismHomeomorph u a z : ℂ) =
      (u : ℂ) *
        (((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ))) :=
  by
    rw [unitDiscStandardAutomorphismHomeomorph_apply]
    exact coe_unitDiscStandardAutomorphismEquiv_apply u a z

/-- With zero center, the standard automorphism homeomorphism is just rotation. -/
@[simp]
lemma unitDiscStandardAutomorphismHomeomorph_zero (u : Circle) :
    unitDiscStandardAutomorphismHomeomorph u 0 =
      Homeomorph.smul u := by
  ext z
  simp [unitDiscStandardAutomorphismHomeomorph]

/-- With unit rotation factor, the standard automorphism homeomorphism is the Moebius one. -/
@[simp]
lemma unitDiscStandardAutomorphismHomeomorph_one (a : Complex.UnitDisc) :
    unitDiscStandardAutomorphismHomeomorph 1 a = unitDiscMoebiusHomeomorph a := by
  ext z
  simp [unitDiscStandardAutomorphismHomeomorph]

end TauCeti
