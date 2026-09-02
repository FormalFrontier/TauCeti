/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Mathlib.Analysis.Quaternion` is imported publicly for `Quaternion.ofComplex`, the `ℝ`-algebra
-- embedding `ℂ →ₐ[ℝ] ℍ[ℝ]` that every statement below is about; it re-exports
-- `Mathlib.Algebra.Quaternion`, hence the `ℍ[·]` notation and the division ring structure on
-- `ℍ[ℝ]`, which is why neither is imported again here.
public import Mathlib.Analysis.Quaternion
-- `Mathlib.LinearAlgebra.Complex.Module` is imported publicly for `Complex.lift`, the universal
-- property saying that an `ℝ`-algebra map out of `ℂ` is exactly a square root of `-1`, and for
-- `Complex.conjAe`, the conjugation this file realizes by `j`.
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# The two embeddings of `ℂ` in the quaternions are conjugate

Complex conjugation on the copy of `ℂ` inside the real quaternions is conjugation by `j`:

`ofComplex (conj z) = j * ofComplex z * j⁻¹`.

This is the second half of the "Skolem-Noether in the small" worked example of the semisimple
algebras roadmap; the first half, that every `ℝ`-algebra automorphism of `ℍ[ℝ]` is inner, is an
example in `TauCeti/Algebra/CentralSimple/SkolemNoether.lean`, read straight off
`TauCeti.exists_unit_conj_of_algEquiv`.

The two halves are not the same theorem. `TauCeti.skolemNoether` conjugates two `K`-algebra maps
`B →ₐ[K] A` when **both** `A` and `B` are central simple over `K`, and `ℂ` is not central over `ℝ`:
its centre is all of `ℂ`, not the image of `ℝ`. Centrality of the source cannot simply be dropped
either -- the negative control in that same file exhibits complex conjugation as an `ℝ`-algebra
automorphism of `ℂ` that is **not** inner in `ℂ`. So the statement above is an instance of the
noncentral Skolem-Noether theorem, which that roadmap defers, and it is proved here by hand.

The proof uses none of the central simple machinery. An `ℝ`-algebra map `ℂ →ₐ[ℝ] A` is the same
thing as a square root of `-1` in `A` (Mathlib's `Complex.lift`), so what has to be proved is that
any two square roots of `-1` in `ℍ[ℝ]` are conjugate. Given `x * x = u * u = -1`, the element
`w = 1 - u * x` satisfies `w * x = u * w`, both sides being `x + u`; and `w` vanishes exactly when
`u * x = 1`. Since `x⁻¹ = -x`, that excluded case is `u = -x`, and for `x = i` it is settled by
`j`, which anticommutes with `i`. So every square root of `-1` is conjugate to `i`, hence any two
are conjugate to each other. Complex conjugation is exactly the excluded case, which is why `j` is
the witness the roadmap names.

## Main definitions

* `TauCeti.Quaternion.jUnit`: the quaternion `j`, as a unit of the division ring `ℍ[ℝ]`.

## Main statements

* `TauCeti.Quaternion.conj_jUnit_ofComplex_I`: conjugation by `j` negates `i`.
* `TauCeti.Quaternion.exists_unit_conj_of_mul_self_eq_neg_one`: any two square roots of `-1` in
  `ℍ[ℝ]` are conjugate by a unit.
* `TauCeti.Quaternion.exists_unit_conj_complexAlgHom`: **noncentral Skolem-Noether for
  `ℂ ⊆ ℍ[ℝ]`** -- any two `ℝ`-algebra maps `ℂ →ₐ[ℝ] ℍ[ℝ]` are conjugate by a unit of `ℍ[ℝ]`.
* `TauCeti.Quaternion.ofComplex_conjAe`: **complex conjugation on `ℂ ⊆ ℍ[ℝ]` is conjugation by
  `j`**, the roadmap's statement, with the explicit witness.

## Implementation notes

Squares are written `u * u = -1` rather than `u ^ 2 = -1`, matching the subtype
`{I' // I' * I' = -1}` that Mathlib's `Complex.lift` is stated over, so that no `sq`/`pow`
translation is needed where the universal property is used. That universal property is consumed
rather than restated: the square relation is `(Complex.lift.symm f).prop`, and the coordinate
formula for an `ℝ`-algebra map out of `ℂ` is `Complex.lift.apply_symm_apply` followed by
`Complex.liftAux_apply`.

Two steps of the argument are stated as `private` lemmas because they are wanted only here, and in
a generality -- any division ring for the conjugacy of the square roots of `-1`, any `ℝ`-algebra
for the detection of a conjugacy on `Complex.I` -- that no statement of this file uses.

`TauCeti.Quaternion.jUnit` carries its inverse as data rather than being built with `Units.mk0`
from a nonvanishing proof: `↑jUnit⁻¹` is then a quaternion literal definitionally, which turns the
one coordinate computation of the file into a rewrite rather than a division. The body is not
exposed, so the two coercion lemmas below are proved `(rfl)` rather than `rfl`.

The two coordinate identities are stated with the type ascriptions written out, `(⟨0, 0, 1, 0⟩ :
ℍ[ℝ]) * …`, and are consumed by `exact`/`rw` rather than being inlined into the proofs that need
them. `Quaternion R` is a plain `def` for `ℍ[R,-1,-1]`, so an ascribed anonymous constructor
elaborates at the *unfolded* type and `QuaternionAlgebra.mk_mul_mk` applies to it, whereas the same
literal reached through a declaration of type `ℍ[ℝ]` does not match that `simp` lemma at all and
the product stays stuck. Neither `TauCeti.Quaternion.coe_jUnit` nor
`TauCeti.Quaternion.coe_inv_jUnit` is a `simp` lemma for the same reason: rewriting with them puts
a literal where nothing can act on it unless the goal is already in the ascribed form.

## References

This is the `ℂ ⊆ ℍ` half of the "Skolem-Noether in the small" worked example of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, CUP (2006), §2.7, and
I. N. Herstein, *Noncommutative Rings*, MAA (1968), Ch. 4.
-/

public section

open scoped Quaternion

namespace TauCeti

namespace Quaternion

/-- **The quaternion `j`, as a unit** of the division ring `ℍ[ℝ]`. Its inverse `-j` is supplied as
data, so that `↑jUnit⁻¹` reduces to a quaternion literal without a division. -/
def jUnit : ℍ[ℝ]ˣ where
  val := ⟨0, 0, 1, 0⟩
  inv := ⟨0, 0, -1, 0⟩
  val_inv := (by ext <;> simp : (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) * (⟨0, 0, -1, 0⟩ : ℍ[ℝ]) = 1)
  inv_val := (by ext <;> simp : (⟨0, 0, -1, 0⟩ : ℍ[ℝ]) * (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) = 1)

theorem coe_jUnit : (jUnit : ℍ[ℝ]) = ⟨0, 0, 1, 0⟩ := (rfl)

theorem coe_inv_jUnit : ((jUnit⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) = ⟨0, 0, -1, 0⟩ := (rfl)

/-- The coordinates of `i`: the image of `Complex.I` under the standard embedding. -/
theorem ofComplex_I : _root_.Quaternion.ofComplex Complex.I = (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) := by
  ext <;> simp [_root_.Quaternion.coe_ofComplex, _root_.Quaternion.coeComplex]

/-- **Conjugation by `j` negates `i`.** This is the one computation with quaternion coordinates
that the file needs: `j` anticommutes with `i`. -/
theorem conj_jUnit_ofComplex_I :
    (jUnit : ℍ[ℝ]) * _root_.Quaternion.ofComplex Complex.I * ((jUnit⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ])
      = -_root_.Quaternion.ofComplex Complex.I := by
  have h : (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) * (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) * (⟨0, 0, -1, 0⟩ : ℍ[ℝ])
      = -(⟨0, 1, 0, 0⟩ : ℍ[ℝ]) := by ext <;> simp
  rw [ofComplex_I, coe_jUnit, coe_inv_jUnit]
  exact h

/-- **Two square roots of `-1` that are not negatives of one another are conjugate.** The
conjugating element is `1 - u * x`: it satisfies `(1 - u * x) * x = u * (1 - u * x)`, both sides
being `x + u`, and it is nonzero exactly by the hypothesis `u * x ≠ 1`, which says `u ≠ -x`
because `x⁻¹ = -x`. -/
private theorem exists_unit_conj_of_mul_ne_one {x u : ℍ[ℝ]} (hx : x * x = -1) (hu : u * u = -1)
    (h : u * x ≠ 1) :
    ∃ w : ℍ[ℝ]ˣ, u = (w : ℍ[ℝ]) * x * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) := by
  have hw : (1 : ℍ[ℝ]) - u * x ≠ 0 := fun hz => h (by rw [sub_eq_zero] at hz; exact hz.symm)
  have h1 : u * x * x = -u := by rw [mul_assoc, hx, mul_neg_one]
  have h2 : u * (u * x) = -x := by rw [← mul_assoc, hu, neg_one_mul]
  have key : ((1 : ℍ[ℝ]) - u * x) * x = u * ((1 : ℍ[ℝ]) - u * x) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, h1, h2, sub_neg_eq_add, sub_neg_eq_add]
    exact add_comm x u
  refine ⟨Units.mk0 _ hw, ?_⟩
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, key, mul_assoc, mul_inv_cancel₀ hw, mul_one]

/-- **Every square root of `-1` in `ℍ[ℝ]` is conjugate to `i`.** In the generic case the
conjugating unit is `1 - u * i`; the one element that excludes is `-i`, which `j` conjugates `i`
to. -/
theorem exists_unit_conj_ofComplex_I {u : ℍ[ℝ]} (hu : u * u = -1) :
    ∃ w : ℍ[ℝ]ˣ,
      u = (w : ℍ[ℝ]) * _root_.Quaternion.ofComplex Complex.I * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) := by
  have hx : _root_.Quaternion.ofComplex Complex.I * _root_.Quaternion.ofComplex Complex.I = -1 :=
    (Complex.lift.symm _root_.Quaternion.ofComplex).prop
  by_cases h : u * _root_.Quaternion.ofComplex Complex.I = 1
  · have h2 : -u = _root_.Quaternion.ofComplex Complex.I := by
      have h3 : u * _root_.Quaternion.ofComplex Complex.I * _root_.Quaternion.ofComplex Complex.I
          = 1 * _root_.Quaternion.ofComplex Complex.I := by rw [h]
      rwa [mul_assoc, hx, mul_neg_one, one_mul] at h3
    exact ⟨jUnit, by rw [conj_jUnit_ofComplex_I, ← h2, neg_neg]⟩
  · exact exists_unit_conj_of_mul_ne_one hx hu h

/-- **Any two square roots of `-1` in `ℍ[ℝ]` are conjugate** by a unit of `ℍ[ℝ]`: both are
conjugate to `i`. -/
theorem exists_unit_conj_of_mul_self_eq_neg_one {u v : ℍ[ℝ]} (hu : u * u = -1) (hv : v * v = -1) :
    ∃ w : ℍ[ℝ]ˣ, v = (w : ℍ[ℝ]) * u * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) := by
  obtain ⟨a, ha⟩ := exists_unit_conj_ofComplex_I hu
  obtain ⟨b, hb⟩ := exists_unit_conj_ofComplex_I hv
  refine ⟨b * a⁻¹, ?_⟩
  rw [ha, hb]
  simp only [Units.val_mul, mul_inv_rev, inv_inv, mul_assoc, Units.inv_mul_cancel_left]

/-- **Conjugation of an `ℝ`-algebra map out of `ℂ` is detected on `Complex.I`.** If `g` agrees with
the `w`-conjugate of `f` at `i` then it agrees with it everywhere: both maps are read off their
value at `i` through `Complex.lift`, and conjugation fixes the scalars. -/
private theorem conj_unit_complexAlgHom_apply (w : ℍ[ℝ]ˣ) (f g : ℂ →ₐ[ℝ] ℍ[ℝ])
    (h : g Complex.I = (w : ℍ[ℝ]) * f Complex.I * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ])) (z : ℂ) :
    g z = (w : ℍ[ℝ]) * f z * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) := by
  have hA : (w : ℍ[ℝ]) * algebraMap ℝ ℍ[ℝ] z.re * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ])
      = algebraMap ℝ ℍ[ℝ] z.re := by
    rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]
  have hB : (w : ℍ[ℝ]) * (z.im • f Complex.I) * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ])
      = z.im • ((w : ℍ[ℝ]) * f Complex.I * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ])) := by
    rw [mul_smul_comm, smul_mul_assoc]
  conv_lhs => rw [← Complex.lift.apply_symm_apply g]
  conv_rhs => rw [← Complex.lift.apply_symm_apply f]
  simp only [Complex.lift_apply, Complex.liftAux_apply, Complex.lift_symm_apply_coe]
  rw [h, mul_add, add_mul, hA, hB]

/-- **Noncentral Skolem-Noether for `ℂ ⊆ ℍ[ℝ]`**: any two `ℝ`-algebra maps `ℂ →ₐ[ℝ] ℍ[ℝ]` are
conjugate by a unit of `ℍ[ℝ]`. The source `ℂ` is simple but **not** central over `ℝ`, so
`TauCeti.skolemNoether` does not apply and the conjugating unit is produced directly, from the
conjugacy of the square roots of `-1`. -/
theorem exists_unit_conj_complexAlgHom (f g : ℂ →ₐ[ℝ] ℍ[ℝ]) :
    ∃ w : ℍ[ℝ]ˣ, ∀ z : ℂ, g z = (w : ℍ[ℝ]) * f z * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) := by
  have hf : f Complex.I * f Complex.I = -1 := (Complex.lift.symm f).prop
  have hg : g Complex.I * g Complex.I = -1 := (Complex.lift.symm g).prop
  obtain ⟨w, hw⟩ := exists_unit_conj_of_mul_self_eq_neg_one hf hg
  exact ⟨w, conj_unit_complexAlgHom_apply w f g hw⟩

/-- **Complex conjugation on `ℂ ⊆ ℍ[ℝ]` is conjugation by `j`**, the roadmap's statement, with the
explicit witness in place of the existential of
`TauCeti.Quaternion.exists_unit_conj_complexAlgHom`. -/
theorem ofComplex_conjAe (z : ℂ) :
    _root_.Quaternion.ofComplex (Complex.conjAe z)
      = (jUnit : ℍ[ℝ]) * _root_.Quaternion.ofComplex z * ((jUnit⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) := by
  refine conj_unit_complexAlgHom_apply jUnit _root_.Quaternion.ofComplex
    (_root_.Quaternion.ofComplex.comp Complex.conjAe.toAlgHom) ?_ z
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Complex.conjAe_coe, Complex.conj_I, map_neg,
    conj_jUnit_ofComplex_I]

end Quaternion

end TauCeti
