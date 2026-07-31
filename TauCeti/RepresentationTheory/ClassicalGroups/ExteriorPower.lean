/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower
public import TauCeti.RepresentationTheory.ClassicalGroups.Determinant
public import TauCeti.RepresentationTheory.ClassicalGroups.Diagonal
public import TauCeti.RepresentationTheory.ExteriorPower
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Exterior powers of the standard representation

This file specializes exterior powers of representations to the standard representation of the
general linear group. The resulting action applies a matrix to every factor of a pure wedge.

In the top degree `d = n` the action collapses to a scalar: a matrix acts on `⋀[k]^n (Fin n → k)`
by its determinant, so that exterior power is the determinant representation.

## Main definitions

* `TauCeti.extPowerRep` is the exterior-power representation of `GL n k`.
* `TauCeti.extPowerFDRep` is its bundled finite-dimensional form.
* `TauCeti.topExtPowerEquivDet` identifies the top exterior power with the determinant
  representation, and `TauCeti.extPowerFDRepDetIso` is its bundled form.

## Main results

* `TauCeti.char_extPowerRep_diagonal` identifies the character on diagonal matrices with an
  elementary symmetric polynomial.
* `TauCeti.extPowerRep_self_apply` and `TauCeti.char_extPowerRep_self` compute the top-degree
  action and character as the determinant.

Importing this file also makes `exteriorPower.eq_zero_of_finrank_lt` available, which says that
`⋀[k]^d (Fin n → k)`, and hence `extPowerRep k n d`, is zero once `n < d`. The degree-zero and
degree-one identifications of `extPowerRep k n` are the generic
`(stdRep k n).exteriorPowerZeroEquiv` and `(stdRep k n).exteriorPowerOneEquiv`.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 1, “Symmetric and exterior power representations”.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open CategoryTheory
open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n d : ℕ)

section CommRing

variable [CommRing k]

/-- The `d`th exterior power of the standard representation of `GL n k`. -/
noncomputable abbrev extPowerRep :
    Representation k (GL (Fin n) k) (⋀[k]^d (Fin n → k)) :=
  (stdRep k n).exteriorPower d

/-- The exterior power of the standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev extPowerFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (extPowerRep k n d)

/-- In the top degree a matrix acts on the exterior power by multiplication by its determinant.

This is deliberately not a `simp` lemma: `Representation.exteriorPower_apply` and `stdRep_apply`
already rewrite the left-hand side to `exteriorPower.map n (Matrix.mulVecLin ↑g)`, so it is not in
`simp` normal form and the rewrite could never fire. The `simp`-normal statement is Mathlib's
`exteriorPower.map_eq_det_smul`, applied here to `Pi.basisFun k (Fin n)`. -/
theorem extPowerRep_self_apply (g : GL (Fin n) k) :
    extPowerRep k n n g = Matrix.det (g : Matrix (Fin n) (Fin n) k) • LinearMap.id := by
  rw [Representation.exteriorPower_apply, stdRep_apply, ← Matrix.toLin'_apply',
    exteriorPower.map_eq_det_smul (Pi.basisFun k (Fin n)), LinearMap.det_toLin']

/-- **The top exterior power of the standard representation is the determinant representation.**
The identification sends a wedge of `n` vectors to the determinant of the matrix they form. -/
noncomputable def topExtPowerEquivDet : (extPowerRep k n n).Equiv (detRep k n) :=
  .mk (exteriorPower.topEquiv (Pi.basisFun k (Fin n))) fun g ↦ by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      extPowerRep_self_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, map_smul,
      smul_eq_mul, detPowerRep_apply, zpow_one, Matrix.GeneralLinearGroup.val_det_apply]

/-- The underlying linear equivalence of `TauCeti.topExtPowerEquivDet` is the top-degree
identification of the exterior power with the scalars. -/
@[simp]
theorem topExtPowerEquivDet_toLinearEquiv :
    (topExtPowerEquivDet k n).toLinearEquiv = exteriorPower.topEquiv (Pi.basisFun k (Fin n)) :=
  (rfl)

/-- The identification sends a wedge of `n` vectors to the determinant of the matrix they form. -/
@[simp]
theorem topExtPowerEquivDet_apply_ιMulti (v : Fin n → (Fin n → k)) :
    topExtPowerEquivDet k n (exteriorPower.ιMulti k n v) = (Matrix.of v).det := by
  simp [topExtPowerEquivDet, ← Pi.basisFun_det_apply]

/-- The identification of the top exterior power with the determinant representation, bundled as
an isomorphism in `FDRep`. -/
noncomputable def extPowerFDRepDetIso : extPowerFDRep k n n ≅ detFDRep k n :=
  Action.mkIso (topExtPowerEquivDet k n).toLinearEquiv.toFGModuleCatIso fun g ↦ by
    apply FGModuleCat.hom_ext
    exact (topExtPowerEquivDet k n).isIntertwining' g

/-- The forward map of the bundled identification is the underlying representation
equivalence. -/
@[simp]
theorem extPowerFDRepDetIso_hom_hom :
    (extPowerFDRepDetIso k n).hom.hom =
      ConcreteCategory.ofHom (topExtPowerEquivDet k n).toLinearMap := by
  rw [extPowerFDRepDetIso]
  rfl

/-- The inverse map of the bundled identification is the inverse representation equivalence. -/
@[simp]
theorem extPowerFDRepDetIso_inv_hom :
    (extPowerFDRepDetIso k n).inv.hom =
      ConcreteCategory.ofHom (topExtPowerEquivDet k n).symm.toLinearMap := by
  rw [extPowerFDRepDetIso]
  rfl

end CommRing

section Field

variable [Field k]

/-- The character of the `d`th exterior power on a diagonal matrix is the `d`th elementary
symmetric polynomial in its diagonal entries. -/
@[simp]
theorem char_extPowerRep_diagonal (t : Fin n → kˣ) :
    (extPowerRep k n d).character (diagGL t) =
      MvPolynomial.eval (fun i => (t i : k)) (MvPolynomial.esymm (Fin n) k d) := by
  rw [Representation.character, Representation.exteriorPower_apply]
  rw [exteriorPower.trace_map_of_apply_basis (Pi.basisFun k (Fin n))
    (stdRep k n (diagGL t)) (fun i => (t i : k)) d
    (stdRep_diagGL_apply_basisFun t)]
  simp only [MvPolynomial.esymm, MvPolynomial.eval_sum, MvPolynomial.eval_prod,
    MvPolynomial.eval_X]
  -- Both sides sum the same products over the `d`-element subsets of `Fin n`, indexed by
  -- `Set.powersetCard` on the left and by `Finset.powersetCard` on the right.
  exact (Finset.sum_subtype (Finset.powersetCard d Finset.univ)
    (fun _ => Finset.mem_powersetCard_univ) fun s => ∏ i ∈ s, (t i : k)).symm

/-- The character of the top exterior power of the standard representation is the determinant.

This is deliberately not a `simp` lemma: on a diagonal matrix its left-hand side is also matched by
`TauCeti.char_extPowerRep_diagonal`, whose elementary-symmetric right-hand side is a different
normal form. -/
theorem char_extPowerRep_self (g : GL (Fin n) k) :
    (extPowerRep k n n).character g = Matrix.det (g : Matrix (Fin n) (Fin n) k) := by
  rw [Representation.char_iso (topExtPowerEquivDet k n), char_detPowerRep k n 1 g, zpow_one,
    Matrix.GeneralLinearGroup.val_det_apply]

end Field

end TauCeti
