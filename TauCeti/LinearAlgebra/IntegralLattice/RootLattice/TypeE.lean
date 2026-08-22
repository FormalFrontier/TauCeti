/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.LinearAlgebra.Matrix.Cartan
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Cardinality
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.StandardCoordinates
public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular
import Mathlib.Data.ZMod.QuotientGroup

/-!
# The exceptional root lattices `E₆`, `E₇`, `E₈` and their discriminant forms

The root lattice of an exceptional simply laced type is the integral lattice whose Gram
matrix in the simple-root basis is the corresponding Cartan matrix.  This file constructs the three
of them inside `Fin n → ℚ`, proves them even and nondegenerate, and computes their discriminant
forms:

```text
det E₆ = 3,   A_{E₆} ≃+ ℤ/3,   q(ϖ₁) = 2/3,
det E₇ = 2,   A_{E₇} ≃+ ℤ/2,   q(ϖ₇) = 3/4,
det E₈ = 1,   A_{E₈} = 0,      E₈ is unimodular.
```

The generators are the classes of the minuscule fundamental weights, `ϖ₁` for `E₆` and `ϖ₇` for
`E₇`, written in the simple-root coordinates that the inverse Cartan matrix dictates:

```text
3 ϖ₁ = 4α₁ + 3α₂ + 5α₃ + 6α₄ + 4α₅ + 2α₆,
2 ϖ₇ = 2α₁ + 3α₂ + 4α₃ + 6α₄ + 5α₅ + 4α₆ + 3α₇.
```

Those coordinates are verified against the lattice rather than assumed:
`form_typeE₆MinusculeWeight_typeE₆SimpleRoot` proves `⟨ϖ₁, αᵢ⟩ = δ_{i,1}` directly from the row
combinations of `CartanMatrix.E 6`, and likewise in type `E₇`.  The self-pairings
`⟨ϖ₁, ϖ₁⟩ = 4/3` and `⟨ϖ₇, ϖ₇⟩ = 3/2` follow, and give the displayed half-norm values.  The class
of `ϖ₁` has additive order exactly `3` because the first simple-root coordinate of `ϖ₁` is `4/3`,
and the discriminant group has that same order, so `ϖ₁` generates; the same argument with the
second coordinate `3/2` of `ϖ₇` and the order `2` settles type `E₇`.

The half-norm convention is the one fixed by the integral-lattices roadmap: `q_L(x) = ⟨x,x⟩ / 2`
in `ℚ/ℤ`.  Nikulin's full-norm values for these rows are `4/3` and `3/2`.

The Cartan matrices, their symmetry and their determinants are Mathlib's, in Bourbaki's numbering:
the branch node of the diagram is `α₄`, and `α₂` is the short arm.

## Main declarations

* `TauCeti.IntegralLattice.typeE₆RootLattice`, `typeE₇RootLattice`, `typeE₈RootLattice`: the three
  lattices, with Gram matrices `CartanMatrix.E 6`, `CartanMatrix.E 7`, `CartanMatrix.E 8`.
* `TauCeti.IntegralLattice.form_typeE₆SimpleRoot_typeE₆SimpleRoot` and its analogues: the
  simple-root Gram matrix is the Cartan matrix.
* `TauCeti.IntegralLattice.isEven_typeE₆RootLattice` and its analogues: the lattices are even.
* `TauCeti.IntegralLattice.determinant_typeE₆RootLattice` and its analogues: the determinants are
  `3`, `2`, `1`.
* `TauCeti.IntegralLattice.typeE₆MinusculeWeight`, `typeE₇MinusculeWeight`: the minuscule
  fundamental weights `ϖ₁` and `ϖ₇`.
* `TauCeti.IntegralLattice.typeE₆DiscriminantGroupEquiv`: `ZMod 3 ≃+ A_{E₆}`.
* `TauCeti.IntegralLattice.typeE₇DiscriminantGroupEquiv`: `ZMod 2 ≃+ A_{E₇}`.
* `TauCeti.IntegralLattice.typeE₆StandardQuadraticModule` and its type-`E₇` analogue: the
  standard cyclic quadratic modules on `ZMod 3` and `ZMod 2`.
* `TauCeti.IntegralLattice.typeE₆DiscriminantQuadraticIsometry` and its type-`E₇` analogue:
  the standard cyclic modules are isometric to the corresponding discriminant forms.
* `TauCeti.IntegralLattice.discriminantQuadraticMap_typeE₆MinusculeWeightClass`: `q(ϖ₁) = 2/3`.
* `TauCeti.IntegralLattice.discriminantQuadraticMap_typeE₇MinusculeWeightClass`: `q(ϖ₇) = 3/4`.
* `TauCeti.IntegralLattice.isUnimodular_typeE₈RootLattice`: `E₈` is unimodular, so its discriminant
  form is trivial.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §8.
* W. Ebeling, *Lattices and Codes*, Chapters 1 and 3.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, plates V, VI, VII.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 5, the `E₆`, `E₇` and `E₈` rows of the ADE
  table.
-/

public section

namespace TauCeti

namespace IntegralLattice

open Finset

/- Cyclic quadratic-module construction used below. -/

private def intBilin (a : AddCircle (1 : ℚ)) : LinearMap.BilinMap ℤ ℤ (AddCircle (1 : ℚ)) :=
  LinearMap.mk₂ ℤ (fun x y : ℤ ↦ (x * y) • a)
    (fun x y z ↦ by rw [add_mul, add_smul])
    (fun r x y ↦ by rw [smul_eq_mul, mul_assoc, mul_smul])
    (fun x y z ↦ by rw [mul_add, add_smul])
    (fun r x y ↦ by rw [smul_eq_mul, mul_left_comm, mul_smul])

private def intQuadratic (a : AddCircle (1 : ℚ)) : QuadraticMap ℤ ℤ (AddCircle (1 : ℚ)) :=
  (intBilin a).toQuadraticMap

private theorem zmultiples_le_radical_intQuadratic (n : ℕ) (a : AddCircle (1 : ℚ))
    (hq : ((n : ℤ) * n) • a = 0) (hp : (2 * (n : ℤ)) • a = 0) :
    (AddSubgroup.zmultiples (n : ℤ)).toIntSubmodule ≤ (intQuadratic a).radical := by
  intro x hx
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  constructor
  -- Evaluate the quadratic map on this explicit generator multiple.
  · change (((k * (n : ℤ)) * (k * n)) • a) = 0
    have hcoeff : (k * (n : ℤ)) * (k * n) = (k * k) * (n * n) := by ring
    rw [hcoeff, mul_smul, hq, smul_zero]
  · apply LinearMap.ext
    intro y
    -- The second radical condition is the vanishing of the polar map.
    change QuadraticMap.polar (intQuadratic a) (k • (n : ℤ)) y = 0
    rw [intQuadratic, LinearMap.BilinMap.polar_toQuadraticMap]
    simp only [intBilin, LinearMap.mk₂_apply, smul_eq_mul]
    -- Expose the two evaluations of the underlying integer bilinear map.
    change ((k * (n : ℤ) * y) • a) + ((y * (k * n)) • a) = 0
    rw [← add_smul]
    have hcoeff : k * (n : ℤ) * y + y * (k * n) = (k * y) * (2 * n) := by ring
    rw [hcoeff, mul_smul, hp, smul_zero]

private def intQuotientEquivZMod (n : ℕ) :
    (ℤ ⧸ (AddSubgroup.zmultiples (n : ℤ)).toIntSubmodule) ≃ₗ[ℤ] ZMod n :=
  { Int.quotientZMultiplesNatEquivZMod n with
    map_smul' := by
      intro k x
      convert! (Int.quotientZMultiplesNatEquivZMod n).toAddMonoidHom.map_zsmul k x using 1 }

private def cyclicQuadraticMap (n : ℕ) (a : AddCircle (1 : ℚ))
    (hq : ((n : ℤ) * n) • a = 0) (hp : (2 * (n : ℤ)) • a = 0) :
    QuadraticMap ℤ (ZMod n) (AddCircle (1 : ℚ)) :=
  ((intQuadratic a).lift (AddSubgroup.zmultiples (n : ℤ)).toIntSubmodule
      (zmultiples_le_radical_intQuadratic n a hq hp)).comp
      (intQuotientEquivZMod n).symm.toLinearMap

private theorem cyclicQuadraticMap_one (n : ℕ) (a : AddCircle (1 : ℚ))
    (hq : ((n : ℤ) * n) • a = 0) (hp : (2 * (n : ℤ)) • a = 0) :
    cyclicQuadraticMap n a hq hp 1 = a := by
  unfold cyclicQuadraticMap
  rw [QuadraticMap.comp_apply]
  have he : (intQuotientEquivZMod n).symm 1 = Submodule.Quotient.mk (1 : ℤ) := by
    apply (intQuotientEquivZMod n).injective
    rw [LinearEquiv.apply_symm_apply]
    have hs : (QuotientAddGroup.quotientAddEquivOfEq (ZMod.ker_intCastAddHom n)).symm
        (QuotientAddGroup.mk 1) = QuotientAddGroup.mk 1 := by
      apply (QuotientAddGroup.quotientAddEquivOfEq (ZMod.ker_intCastAddHom n)).injective
      rw [AddEquiv.apply_symm_apply, QuotientAddGroup.quotientAddEquivOfEq_mk]
    -- Expose the composition defining the quotient-to-`ZMod` equivalence.
    change (1 : ZMod n) = Int.quotientZMultiplesNatEquivZMod n (QuotientAddGroup.mk 1)
    rw [Int.quotientZMultiplesNatEquivZMod, AddEquiv.trans_apply, hs]
    -- The generator of `ZMod n` is definitionally the image of the integer generator.
    change (1 : ZMod n) = ((1 : ℤ) : ZMod n)
    simp
  -- Expose the lifted quadratic map at the quotient representative.
  change (intQuadratic a).lift (AddSubgroup.zmultiples (n : ℤ)).toIntSubmodule _
    ((intQuotientEquivZMod n).symm 1) = a
  rw [he, QuadraticMap.lift_mk]
  simp [intQuadratic, intBilin]

private noncomputable def quadraticMapIsometryOfGenerator (n : ℕ)
    {A : Type*} [AddCommGroup A]
    (q : QuadraticMap ℤ (ZMod n) (AddCircle (1 : ℚ)))
    (r : QuadraticMap ℤ A (AddCircle (1 : ℚ))) (e : ZMod n ≃+ A)
    (he : r (e 1) = q 1) : q.IsometryEquiv r where
  toLinearEquiv := e.toIntLinearEquiv
  map_app' x := by
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
    -- Identify the bundled linear equivalence with its underlying additive equivalence.
    change r (e (k : ZMod n)) = q (k : ZMod n)
    rw [← zsmul_one, map_zsmul, r.map_smul, q.map_smul, he]

/-! ## The root lattice of type `E₆` -/

/-- The root lattice of type `E₆`: the rank-six integral lattice on `Fin 6 → ℚ` whose Gram
matrix in the standard basis of simple roots is `CartanMatrix.E 6`. -/
noncomputable def typeE₆RootLattice : IntegralLattice (Fin 6 → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin 6)) (CartanMatrix.E 6) (CartanMatrix.E_isSymm 6)

/-- The `i`-th simple root of the type `E₆` root lattice, as a vector of the ambient space. -/
-- This is sealed so `Pi.basisFun_apply` does not rewrite beneath it and destabilize the simp API.
noncomputable def typeE₆SimpleRoot (i : Fin 6) : Fin 6 → ℚ := Pi.basisFun ℚ (Fin 6) i

/-- The `i`-th simple root of type `E₆` is the `i`-th standard coordinate vector. -/
@[simp]
theorem typeE₆SimpleRoot_apply (i j : Fin 6) :
    typeE₆SimpleRoot i j = if j = i then 1 else 0 := by
  simp [typeE₆SimpleRoot, Pi.basisFun_apply, Pi.single_apply]

/-- **The Gram matrix of the type `E₆` root lattice in its simple-root basis is the Cartan matrix
`CartanMatrix.E 6`.** -/
@[simp]
theorem form_typeE₆SimpleRoot_typeE₆SimpleRoot (i j : Fin 6) :
    typeE₆RootLattice.form (typeE₆SimpleRoot i) (typeE₆SimpleRoot j) =
      (((CartanMatrix.E 6) i j : ℤ) : ℚ) := by
  rw [typeE₆SimpleRoot, typeE₆SimpleRoot, typeE₆RootLattice]
  exact form_ofGramMatrix_basisFun_basisFun _ _ i j

/-- A vector belongs to the type `E₆` root lattice exactly when all of its simple-root coordinates
are integers. -/
@[simp]
theorem mem_typeE₆RootLattice_carrier_iff (x : Fin 6 → ℚ) :
    x ∈ typeE₆RootLattice.carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i := by
  rw [typeE₆RootLattice]
  exact mem_ofGramMatrix_basisFun_carrier_iff _ _ x

/-- The determinant of the type `E₆` Cartan matrix is nonzero. -/
private theorem det_cartanMatrixE₆_ne_zero : (CartanMatrix.E 6).det ≠ 0 := by
  rw [CartanMatrix.E₆_det]
  norm_num

/-- The type `E₆` root lattice is nondegenerate because its Cartan matrix is nonsingular. -/
noncomputable instance instIsNondegenerateTypeE₆RootLattice :
    typeE₆RootLattice.IsNondegenerate := by
  rw [typeE₆RootLattice]
  refine isNondegenerate_ofGramMatrix _ _ _ ?_
  convert det_cartanMatrixE₆_ne_zero

/-- The type `E₆` root lattice is even: every diagonal Cartan entry is `2`. -/
theorem isEven_typeE₆RootLattice : typeE₆RootLattice.IsEven := by
  rw [typeE₆RootLattice, isEven_ofGramMatrix_iff]
  decide

/-- **The determinant of the type `E₆` root lattice is `3`.** -/
@[simp]
theorem determinant_typeE₆RootLattice : typeE₆RootLattice.determinant = 3 := by
  rw [typeE₆RootLattice, determinant_ofGramMatrix]
  convert CartanMatrix.E₆_det

/-- The discriminant of the type `E₆` root lattice is `3`. -/
@[simp]
theorem discriminant_typeE₆RootLattice : typeE₆RootLattice.discriminant = 3 := by
  rw [discriminant_def, determinant_typeE₆RootLattice]
  decide

/-- **The discriminant group of the type `E₆` root lattice has order `3`.** -/
-- This is not a `simp` lemma because `Nat.card_eq_fintype_card` rewrites its left-hand side.
theorem natCard_discriminantGroup_typeE₆RootLattice :
    Nat.card typeE₆RootLattice.DiscriminantGroup = 3 := by
  rw [natCard_discriminantGroup, discriminant_typeE₆RootLattice]

/-! ### The minuscule fundamental weight of type `E₆` -/

/-- The simple-root coordinates of `3ϖ₁` in type `E₆`, from Bourbaki plate V:
`3ϖ₁ = 4α₁ + 3α₂ + 5α₃ + 6α₄ + 4α₅ + 2α₆`. -/
private def typeE₆WeightCoeff : Fin 6 → ℤ := ![4, 3, 5, 6, 4, 2]

/-- The minuscule fundamental weight `ϖ₁` of type `E₆`, in simple-root coordinates. -/
noncomputable def typeE₆MinusculeWeight : Fin 6 → ℚ :=
  fun j ↦ (typeE₆WeightCoeff j : ℚ) / 3

@[simp]
theorem typeE₆MinusculeWeight_apply (j : Fin 6) :
    typeE₆MinusculeWeight j =
      ((![4, 3, 5, 6, 4, 2] : Fin 6 → ℤ) j : ℚ) / 3 := by
  rw [typeE₆MinusculeWeight, typeE₆WeightCoeff]

/-- The row combinations of `CartanMatrix.E 6` against the coordinates of `3ϖ₁`. -/
private theorem sum_cartanMatrixE₆_mul_weightCoeff :
    ∀ i : Fin 6, ∑ j, (CartanMatrix.E 6) i j * typeE₆WeightCoeff j = if i = 0 then 3 else 0 := by
  decide

/-- The row combinations of `CartanMatrix.E 6` against the coordinates of `ϖ₁`. -/
private theorem sum_cartanMatrixE₆_mul_minusculeWeight (i : Fin 6) :
    (∑ j, (((CartanMatrix.E 6) i j : ℤ) : ℚ) * typeE₆MinusculeWeight j) =
      if i = 0 then 1 else 0 := by
  have hcast : ((∑ j, (CartanMatrix.E 6) i j * typeE₆WeightCoeff j : ℤ) : ℚ)
      = ((if i = 0 then (3 : ℤ) else 0 : ℤ) : ℚ) := by
    rw [sum_cartanMatrixE₆_mul_weightCoeff i]
  push_cast at hcast
  have hexp : (∑ j, (((CartanMatrix.E 6) i j : ℤ) : ℚ) * typeE₆MinusculeWeight j)
      = (∑ j, (((CartanMatrix.E 6) i j : ℤ) : ℚ) * ((typeE₆WeightCoeff j : ℤ) : ℚ)) / 3 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [typeE₆MinusculeWeight]; ring
  rw [hexp, hcast]
  split_ifs <;> norm_num

/-- **The minuscule weight `ϖ₁` pairs to `1` with the first simple root and to `0` with the
others.** -/
@[simp]
theorem form_typeE₆MinusculeWeight_typeE₆SimpleRoot (i : Fin 6) :
    typeE₆RootLattice.form typeE₆MinusculeWeight (typeE₆SimpleRoot i) = if i = 0 then 1 else 0 := by
  rw [typeE₆SimpleRoot, typeE₆RootLattice, form_ofGramMatrix_basisFun_right]
  exact sum_cartanMatrixE₆_mul_minusculeWeight i

/-- **The self-pairing of the minuscule weight `ϖ₁` of type `E₆` is `4/3`.** -/
@[simp]
theorem form_typeE₆MinusculeWeight_self :
    typeE₆RootLattice.form typeE₆MinusculeWeight typeE₆MinusculeWeight = 4 / 3 := by
  rw [typeE₆RootLattice, form_ofGramMatrix_basisFun_apply]
  simp_rw [sum_cartanMatrixE₆_mul_minusculeWeight]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0)]
  · have hcoeff : typeE₆WeightCoeff 0 = 4 := by decide
    rw [typeE₆MinusculeWeight, hcoeff]
    norm_num
  · intro b _ hb
    simp [hb]

/-- The minuscule weight `ϖ₁` lies in the dual lattice: it pairs integrally with every simple
root, hence with the whole lattice. -/
theorem typeE₆MinusculeWeight_mem_dualCarrier :
    typeE₆MinusculeWeight ∈ typeE₆RootLattice.dualCarrier := by
  rw [typeE₆RootLattice, mem_ofGramMatrix_basisFun_dualCarrier_iff]
  intro i
  rw [sum_cartanMatrixE₆_mul_minusculeWeight i]
  split_ifs
  · exact ⟨1, by norm_num⟩
  · exact ⟨0, by norm_num⟩

/-- The minuscule weight `ϖ₁` of type `E₆`, as a vector of the dual lattice. -/
noncomputable def typeE₆MinusculeWeightDual : typeE₆RootLattice.dualCarrier :=
  ⟨typeE₆MinusculeWeight, typeE₆MinusculeWeight_mem_dualCarrier⟩

@[simp]
theorem coe_typeE₆MinusculeWeightDual :
    (typeE₆MinusculeWeightDual : Fin 6 → ℚ) = typeE₆MinusculeWeight := by
  rw [typeE₆MinusculeWeightDual]

/-- The discriminant class of the minuscule weight `ϖ₁` of type `E₆`. -/
noncomputable def typeE₆MinusculeWeightClass : typeE₆RootLattice.DiscriminantGroup :=
  Submodule.Quotient.mk typeE₆MinusculeWeightDual

/-- **An integer multiple of `ϖ₁` lies in the type `E₆` root lattice exactly when `3` divides
it**: the first simple-root coordinate of `ϖ₁` is `4/3`. -/
theorem zsmul_typeE₆MinusculeWeightClass_eq_zero_iff (k : ℤ) :
    k • typeE₆MinusculeWeightClass = 0 ↔ (3 : ℤ) ∣ k := by
  rw [typeE₆MinusculeWeightClass, ← Submodule.Quotient.mk_smul,
    discriminantGroup_mk_eq_zero_iff, mem_typeE₆RootLattice_carrier_iff]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := h 0
    simp only [typeE₆MinusculeWeightDual, SetLike.val_smul, Pi.smul_apply,
      typeE₆MinusculeWeight, zsmul_eq_mul] at hz
    have hcoeff : typeE₆WeightCoeff 0 = 4 := by decide
    rw [hcoeff] at hz
    push_cast at hz
    have hq : (3 : ℚ) * (z : ℚ) = 4 * (k : ℚ) := by
      field_simp at hz
      linarith
    have hz' : (3 : ℤ) * z = 4 * k := by exact_mod_cast hq
    exact ⟨z - k, by linarith⟩
  · rintro ⟨m, rfl⟩ i
    refine ⟨m * typeE₆WeightCoeff i, ?_⟩
    simp only [typeE₆MinusculeWeightDual, SetLike.val_smul, Pi.smul_apply,
      typeE₆MinusculeWeight, zsmul_eq_mul]
    push_cast
    ring

/-- **The class of the minuscule weight `ϖ₁` has additive order `3`.** -/
@[simp]
theorem addOrderOf_typeE₆MinusculeWeightClass :
    addOrderOf typeE₆MinusculeWeightClass = 3 := by
  have hiff : ∀ k : ℤ, ((addOrderOf typeE₆MinusculeWeightClass : ℤ) ∣ k) ↔ (3 : ℤ) ∣ k := by
    intro k
    rw [addOrderOf_dvd_iff_zsmul_eq_zero]
    exact zsmul_typeE₆MinusculeWeightClass_eq_zero_iff k
  have h : (addOrderOf typeE₆MinusculeWeightClass : ℤ) = 3 :=
    Int.dvd_antisymm (Int.natCast_nonneg _) (by norm_num) ((hiff _).mpr dvd_rfl)
      ((hiff _).mp dvd_rfl)
  exact_mod_cast h

/-- **The class of the minuscule weight `ϖ₁` generates the discriminant group of type `E₆`.** -/
theorem zmultiples_typeE₆MinusculeWeightClass_eq_top :
    AddSubgroup.zmultiples typeE₆MinusculeWeightClass = ⊤ := by
  apply AddSubgroup.eq_top_of_card_eq
  rw [Nat.card_zmultiples, addOrderOf_typeE₆MinusculeWeightClass,
    natCard_discriminantGroup_typeE₆RootLattice]

/-- **The discriminant group of the type `E₆` root lattice is cyclic of order `3`**, with the class
of the minuscule weight `ϖ₁` as the image of `1`. -/
noncomputable def typeE₆DiscriminantGroupEquiv :
    ZMod 3 ≃+ typeE₆RootLattice.DiscriminantGroup :=
  zmodAddEquivOfGenerator
    (fun x ↦ by rw [zmultiples_typeE₆MinusculeWeightClass_eq_top]; exact AddSubgroup.mem_top x)
    natCard_discriminantGroup_typeE₆RootLattice

@[simp]
theorem typeE₆DiscriminantGroupEquiv_apply_one :
    typeE₆DiscriminantGroupEquiv 1 = typeE₆MinusculeWeightClass :=
  zmodAddEquivOfGenerator_apply_one _ _

/-- **The discriminant quadratic value of the minuscule weight `ϖ₁` of type `E₆` is `2/3`**, in the
half-norm convention. -/
@[simp]
theorem discriminantQuadraticMap_typeE₆MinusculeWeightClass :
    typeE₆RootLattice.discriminantQuadraticMap isEven_typeE₆RootLattice
        typeE₆MinusculeWeightClass = (((2 : ℚ) / 3 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [typeE₆MinusculeWeightClass, discriminantQuadraticMap_mk]
  congr 1
  rw [coe_typeE₆MinusculeWeightDual, form_typeE₆MinusculeWeight_self]
  norm_num

/-- **The discriminant bilinear value of the minuscule weight `ϖ₁` of type `E₆` is `1/3`.** -/
@[simp]
theorem discriminantPairing_typeE₆MinusculeWeightClass :
    typeE₆RootLattice.discriminantPairing typeE₆MinusculeWeightClass typeE₆MinusculeWeightClass =
      (((1 : ℚ) / 3 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [typeE₆MinusculeWeightClass, discriminantPairing_mk, coe_typeE₆MinusculeWeightDual,
    form_typeE₆MinusculeWeight_self, ← sub_eq_zero, ← AddCircle.coe_sub,
    AddCircle.coe_eq_zero_iff_mem_one]
  exact Submodule.mem_one.mpr ⟨1, by norm_num⟩

private theorem typeE₆QuadraticValue_sq_torsion :
    (9 : ℤ) • ((((2 : ℚ) / 3 : ℚ) : AddCircle (1 : ℚ))) = 0 := by
  -- Expand the integer action through the quotient map `ℚ → ℚ/ℤ`.
  change ((((9 : ℚ) * (2 / 3)) : ℚ) : AddCircle (1 : ℚ)) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact ⟨6, by norm_num⟩

private theorem typeE₆QuadraticValue_polar_torsion :
    (6 : ℤ) • ((((2 : ℚ) / 3 : ℚ) : AddCircle (1 : ℚ))) = 0 := by
  -- Expand the integer action through the quotient map `ℚ → ℚ/ℤ`.
  change ((((6 : ℚ) * (2 / 3)) : ℚ) : AddCircle (1 : ℚ)) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact ⟨4, by norm_num⟩

/-- The quadratic map on `ZMod 3` whose generator has value `2/3`. -/
noncomputable def typeE₆StandardQuadraticMap :
    QuadraticMap ℤ (ZMod 3) (AddCircle (1 : ℚ)) :=
  cyclicQuadraticMap 3 (((2 : ℚ) / 3 : ℚ) : AddCircle (1 : ℚ))
    typeE₆QuadraticValue_sq_torsion typeE₆QuadraticValue_polar_torsion

/-- The standard cyclic quadratic module of type `E₆`, on `ZMod 3`. -/
@[expose] noncomputable def typeE₆StandardQuadraticModule : FiniteQuadraticModule where
  toFiniteBilinearModule := {
    carrier := ZMod 3
    pairing := LinearMap.toAddMonoidHom'.comp typeE₆StandardQuadraticMap.polarBilin.toAddMonoidHom
    pairing_comm := fun x y ↦ QuadraticMap.polar_comm typeE₆StandardQuadraticMap x y }
  quadratic := typeE₆StandardQuadraticMap
  polar_eq_pairing' := fun _ _ ↦ rfl

/-- The generator of the standard type-`E₆` quadratic map has value `2/3`. -/
@[simp]
theorem typeE₆StandardQuadraticMap_one :
    typeE₆StandardQuadraticMap 1 =
      (((2 : ℚ) / 3 : ℚ) : AddCircle (1 : ℚ)) :=
  cyclicQuadraticMap_one 3 _ _ _

/-- The standard cyclic quadratic module of type `E₆` is isometric to the discriminant
quadratic module of the `E₆` root lattice. -/
noncomputable def typeE₆DiscriminantQuadraticIsometry :
    FiniteQuadraticModule.Isometry typeE₆StandardQuadraticModule
      (typeE₆RootLattice.discriminantQuadraticModule isEven_typeE₆RootLattice) :=
  quadraticMapIsometryOfGenerator 3 typeE₆StandardQuadraticMap
    (typeE₆RootLattice.discriminantQuadraticMap isEven_typeE₆RootLattice)
    typeE₆DiscriminantGroupEquiv (by
      rw [typeE₆DiscriminantGroupEquiv_apply_one,
        discriminantQuadraticMap_typeE₆MinusculeWeightClass, typeE₆StandardQuadraticMap_one])

/-- The underlying additive equivalence of the type-`E₆` quadratic isometry. -/
@[simp]
theorem typeE₆DiscriminantQuadraticIsometry_toAddEquiv :
    typeE₆DiscriminantQuadraticIsometry.toAddEquiv = typeE₆DiscriminantGroupEquiv := by
  rw [typeE₆DiscriminantQuadraticIsometry]
  rfl

/-- The type-`E₆` quadratic isometry acts through the discriminant-group equivalence. -/
@[simp]
theorem typeE₆DiscriminantQuadraticIsometry_apply (x : ZMod 3) :
    typeE₆DiscriminantQuadraticIsometry x = typeE₆DiscriminantGroupEquiv x := by
  rw [typeE₆DiscriminantQuadraticIsometry]
  rfl

/-! ## The root lattice of type `E₇` -/

/-- The root lattice of type `E₇`: the rank-seven integral lattice on `Fin 7 → ℚ` whose
Gram matrix in the standard basis of simple roots is `CartanMatrix.E 7`. -/
noncomputable def typeE₇RootLattice : IntegralLattice (Fin 7 → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin 7)) (CartanMatrix.E 7) (CartanMatrix.E_isSymm 7)

/-- The `i`-th simple root of the type `E₇` root lattice, as a vector of the ambient space. -/
-- This is sealed so `Pi.basisFun_apply` does not rewrite beneath it and destabilize the simp API.
noncomputable def typeE₇SimpleRoot (i : Fin 7) : Fin 7 → ℚ := Pi.basisFun ℚ (Fin 7) i

/-- The `i`-th simple root of type `E₇` is the `i`-th standard coordinate vector. -/
@[simp]
theorem typeE₇SimpleRoot_apply (i j : Fin 7) :
    typeE₇SimpleRoot i j = if j = i then 1 else 0 := by
  simp [typeE₇SimpleRoot, Pi.basisFun_apply, Pi.single_apply]

/-- **The Gram matrix of the type `E₇` root lattice in its simple-root basis is the Cartan matrix
`CartanMatrix.E 7`.** -/
@[simp]
theorem form_typeE₇SimpleRoot_typeE₇SimpleRoot (i j : Fin 7) :
    typeE₇RootLattice.form (typeE₇SimpleRoot i) (typeE₇SimpleRoot j) =
      (((CartanMatrix.E 7) i j : ℤ) : ℚ) := by
  rw [typeE₇SimpleRoot, typeE₇SimpleRoot, typeE₇RootLattice]
  exact form_ofGramMatrix_basisFun_basisFun _ _ i j

/-- A vector belongs to the type `E₇` root lattice exactly when all of its simple-root coordinates
are integers. -/
@[simp]
theorem mem_typeE₇RootLattice_carrier_iff (x : Fin 7 → ℚ) :
    x ∈ typeE₇RootLattice.carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i := by
  rw [typeE₇RootLattice]
  exact mem_ofGramMatrix_basisFun_carrier_iff _ _ x

/-- The determinant of the type `E₇` Cartan matrix is nonzero. -/
private theorem det_cartanMatrixE₇_ne_zero : (CartanMatrix.E 7).det ≠ 0 := by
  rw [CartanMatrix.E₇_det]
  norm_num

/-- The type `E₇` root lattice is nondegenerate because its Cartan matrix is nonsingular. -/
noncomputable instance instIsNondegenerateTypeE₇RootLattice :
    typeE₇RootLattice.IsNondegenerate := by
  rw [typeE₇RootLattice]
  refine isNondegenerate_ofGramMatrix _ _ _ ?_
  convert det_cartanMatrixE₇_ne_zero

/-- The type `E₇` root lattice is even: every diagonal Cartan entry is `2`. -/
theorem isEven_typeE₇RootLattice : typeE₇RootLattice.IsEven := by
  rw [typeE₇RootLattice, isEven_ofGramMatrix_iff]
  decide

/-- **The determinant of the type `E₇` root lattice is `2`.** -/
@[simp]
theorem determinant_typeE₇RootLattice : typeE₇RootLattice.determinant = 2 := by
  rw [typeE₇RootLattice, determinant_ofGramMatrix]
  convert CartanMatrix.E₇_det

/-- The discriminant of the type `E₇` root lattice is `2`. -/
@[simp]
theorem discriminant_typeE₇RootLattice : typeE₇RootLattice.discriminant = 2 := by
  rw [discriminant_def, determinant_typeE₇RootLattice]
  decide

/-- **The discriminant group of the type `E₇` root lattice has order `2`.** -/
-- This is not a `simp` lemma because `Nat.card_eq_fintype_card` rewrites its left-hand side.
theorem natCard_discriminantGroup_typeE₇RootLattice :
    Nat.card typeE₇RootLattice.DiscriminantGroup = 2 := by
  rw [natCard_discriminantGroup, discriminant_typeE₇RootLattice]

/-! ### The minuscule fundamental weight of type `E₇` -/

/-- The simple-root coordinates of `2ϖ₇` in type `E₇`, from Bourbaki plate VI:
`2ϖ₇ = 2α₁ + 3α₂ + 4α₃ + 6α₄ + 5α₅ + 4α₆ + 3α₇`. -/
private def typeE₇WeightCoeff : Fin 7 → ℤ := ![2, 3, 4, 6, 5, 4, 3]

/-- The minuscule fundamental weight `ϖ₇` of type `E₇`, in simple-root coordinates. -/
noncomputable def typeE₇MinusculeWeight : Fin 7 → ℚ :=
  fun j ↦ (typeE₇WeightCoeff j : ℚ) / 2

@[simp]
theorem typeE₇MinusculeWeight_apply (j : Fin 7) :
    typeE₇MinusculeWeight j =
      ((![2, 3, 4, 6, 5, 4, 3] : Fin 7 → ℤ) j : ℚ) / 2 := by
  rw [typeE₇MinusculeWeight, typeE₇WeightCoeff]

/-- The row combinations of `CartanMatrix.E 7` against the coordinates of `2ϖ₇`. -/
private theorem sum_cartanMatrixE₇_mul_weightCoeff :
    ∀ i : Fin 7, ∑ j, (CartanMatrix.E 7) i j * typeE₇WeightCoeff j = if i = 6 then 2 else 0 := by
  decide

/-- The row combinations of `CartanMatrix.E 7` against the coordinates of `ϖ₇`. -/
private theorem sum_cartanMatrixE₇_mul_minusculeWeight (i : Fin 7) :
    (∑ j, (((CartanMatrix.E 7) i j : ℤ) : ℚ) * typeE₇MinusculeWeight j) =
      if i = 6 then 1 else 0 := by
  have hcast : ((∑ j, (CartanMatrix.E 7) i j * typeE₇WeightCoeff j : ℤ) : ℚ)
      = ((if i = 6 then (2 : ℤ) else 0 : ℤ) : ℚ) := by
    rw [sum_cartanMatrixE₇_mul_weightCoeff i]
  push_cast at hcast
  have hexp : (∑ j, (((CartanMatrix.E 7) i j : ℤ) : ℚ) * typeE₇MinusculeWeight j)
      = (∑ j, (((CartanMatrix.E 7) i j : ℤ) : ℚ) * ((typeE₇WeightCoeff j : ℤ) : ℚ)) / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [typeE₇MinusculeWeight]; ring
  rw [hexp, hcast]
  split_ifs <;> norm_num

/-- **The minuscule weight `ϖ₇` pairs to `1` with the seventh simple root and to `0` with the
others.** -/
@[simp]
theorem form_typeE₇MinusculeWeight_typeE₇SimpleRoot (i : Fin 7) :
    typeE₇RootLattice.form typeE₇MinusculeWeight (typeE₇SimpleRoot i) = if i = 6 then 1 else 0 := by
  rw [typeE₇SimpleRoot, typeE₇RootLattice, form_ofGramMatrix_basisFun_right]
  exact sum_cartanMatrixE₇_mul_minusculeWeight i

/-- **The self-pairing of the minuscule weight `ϖ₇` of type `E₇` is `3/2`.** -/
@[simp]
theorem form_typeE₇MinusculeWeight_self :
    typeE₇RootLattice.form typeE₇MinusculeWeight typeE₇MinusculeWeight = 3 / 2 := by
  rw [typeE₇RootLattice, form_ofGramMatrix_basisFun_apply]
  simp_rw [sum_cartanMatrixE₇_mul_minusculeWeight]
  rw [Finset.sum_eq_single_of_mem 6 (Finset.mem_univ 6)]
  · have hcoeff : typeE₇WeightCoeff 6 = 3 := by decide
    rw [typeE₇MinusculeWeight, hcoeff]
    norm_num
  · intro b _ hb
    simp [hb]

/-- The minuscule weight `ϖ₇` lies in the dual lattice: it pairs integrally with every simple
root, hence with the whole lattice. -/
theorem typeE₇MinusculeWeight_mem_dualCarrier :
    typeE₇MinusculeWeight ∈ typeE₇RootLattice.dualCarrier := by
  rw [typeE₇RootLattice, mem_ofGramMatrix_basisFun_dualCarrier_iff]
  intro i
  rw [sum_cartanMatrixE₇_mul_minusculeWeight i]
  split_ifs
  · exact ⟨1, by norm_num⟩
  · exact ⟨0, by norm_num⟩

/-- The minuscule weight `ϖ₇` of type `E₇`, as a vector of the dual lattice. -/
noncomputable def typeE₇MinusculeWeightDual : typeE₇RootLattice.dualCarrier :=
  ⟨typeE₇MinusculeWeight, typeE₇MinusculeWeight_mem_dualCarrier⟩

@[simp]
theorem coe_typeE₇MinusculeWeightDual :
    (typeE₇MinusculeWeightDual : Fin 7 → ℚ) = typeE₇MinusculeWeight := by
  rw [typeE₇MinusculeWeightDual]

/-- The discriminant class of the minuscule weight `ϖ₇` of type `E₇`. -/
noncomputable def typeE₇MinusculeWeightClass : typeE₇RootLattice.DiscriminantGroup :=
  Submodule.Quotient.mk typeE₇MinusculeWeightDual

/-- **An integer multiple of `ϖ₇` lies in the type `E₇` root lattice exactly when `2` divides
it**: the second simple-root coordinate of `ϖ₇` is `3/2`. -/
theorem zsmul_typeE₇MinusculeWeightClass_eq_zero_iff (k : ℤ) :
    k • typeE₇MinusculeWeightClass = 0 ↔ (2 : ℤ) ∣ k := by
  rw [typeE₇MinusculeWeightClass, ← Submodule.Quotient.mk_smul,
    discriminantGroup_mk_eq_zero_iff, mem_typeE₇RootLattice_carrier_iff]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := h 1
    simp only [typeE₇MinusculeWeightDual, SetLike.val_smul, Pi.smul_apply,
      typeE₇MinusculeWeight, zsmul_eq_mul] at hz
    have hcoeff : typeE₇WeightCoeff 1 = 3 := by decide
    rw [hcoeff] at hz
    push_cast at hz
    have hq : (2 : ℚ) * (z : ℚ) = 3 * (k : ℚ) := by
      field_simp at hz
      linarith
    have hz' : (2 : ℤ) * z = 3 * k := by exact_mod_cast hq
    exact ⟨z - k, by linarith⟩
  · rintro ⟨m, rfl⟩ i
    refine ⟨m * typeE₇WeightCoeff i, ?_⟩
    simp only [typeE₇MinusculeWeightDual, SetLike.val_smul, Pi.smul_apply,
      typeE₇MinusculeWeight, zsmul_eq_mul]
    push_cast
    ring

/-- **The class of the minuscule weight `ϖ₇` has additive order `2`.** -/
@[simp]
theorem addOrderOf_typeE₇MinusculeWeightClass :
    addOrderOf typeE₇MinusculeWeightClass = 2 := by
  have hiff : ∀ k : ℤ, ((addOrderOf typeE₇MinusculeWeightClass : ℤ) ∣ k) ↔ (2 : ℤ) ∣ k := by
    intro k
    rw [addOrderOf_dvd_iff_zsmul_eq_zero]
    exact zsmul_typeE₇MinusculeWeightClass_eq_zero_iff k
  have h : (addOrderOf typeE₇MinusculeWeightClass : ℤ) = 2 :=
    Int.dvd_antisymm (Int.natCast_nonneg _) (by norm_num) ((hiff _).mpr dvd_rfl)
      ((hiff _).mp dvd_rfl)
  exact_mod_cast h

/-- **The class of the minuscule weight `ϖ₇` generates the discriminant group of type `E₇`.** -/
theorem zmultiples_typeE₇MinusculeWeightClass_eq_top :
    AddSubgroup.zmultiples typeE₇MinusculeWeightClass = ⊤ := by
  apply AddSubgroup.eq_top_of_card_eq
  rw [Nat.card_zmultiples, addOrderOf_typeE₇MinusculeWeightClass,
    natCard_discriminantGroup_typeE₇RootLattice]

/-- **The discriminant group of the type `E₇` root lattice is cyclic of order `2`**, with the class
of the minuscule weight `ϖ₇` as the image of `1`. -/
noncomputable def typeE₇DiscriminantGroupEquiv :
    ZMod 2 ≃+ typeE₇RootLattice.DiscriminantGroup :=
  zmodAddEquivOfGenerator
    (fun x ↦ by rw [zmultiples_typeE₇MinusculeWeightClass_eq_top]; exact AddSubgroup.mem_top x)
    natCard_discriminantGroup_typeE₇RootLattice

@[simp]
theorem typeE₇DiscriminantGroupEquiv_apply_one :
    typeE₇DiscriminantGroupEquiv 1 = typeE₇MinusculeWeightClass :=
  zmodAddEquivOfGenerator_apply_one _ _

/-- **The discriminant quadratic value of the minuscule weight `ϖ₇` of type `E₇` is `3/4`**, in the
half-norm convention. -/
@[simp]
theorem discriminantQuadraticMap_typeE₇MinusculeWeightClass :
    typeE₇RootLattice.discriminantQuadraticMap isEven_typeE₇RootLattice
        typeE₇MinusculeWeightClass = (((3 : ℚ) / 4 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [typeE₇MinusculeWeightClass, discriminantQuadraticMap_mk]
  congr 1
  rw [coe_typeE₇MinusculeWeightDual, form_typeE₇MinusculeWeight_self]
  norm_num

/-- **The discriminant bilinear value of the minuscule weight `ϖ₇` of type `E₇` is `1/2`.** -/
@[simp]
theorem discriminantPairing_typeE₇MinusculeWeightClass :
    typeE₇RootLattice.discriminantPairing typeE₇MinusculeWeightClass typeE₇MinusculeWeightClass =
      (((1 : ℚ) / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [typeE₇MinusculeWeightClass, discriminantPairing_mk, coe_typeE₇MinusculeWeightDual,
    form_typeE₇MinusculeWeight_self, ← sub_eq_zero, ← AddCircle.coe_sub,
    AddCircle.coe_eq_zero_iff_mem_one]
  exact Submodule.mem_one.mpr ⟨1, by norm_num⟩

private theorem typeE₇QuadraticValue_torsion :
    (4 : ℤ) • ((((3 : ℚ) / 4 : ℚ) : AddCircle (1 : ℚ))) = 0 := by
  -- Expand the integer action through the quotient map `ℚ → ℚ/ℤ`.
  change ((((4 : ℚ) * (3 / 4)) : ℚ) : AddCircle (1 : ℚ)) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact ⟨3, by norm_num⟩

/-- The quadratic map on `ZMod 2` whose generator has value `3/4`. -/
noncomputable def typeE₇StandardQuadraticMap :
    QuadraticMap ℤ (ZMod 2) (AddCircle (1 : ℚ)) :=
  cyclicQuadraticMap 2 (((3 : ℚ) / 4 : ℚ) : AddCircle (1 : ℚ))
    typeE₇QuadraticValue_torsion typeE₇QuadraticValue_torsion

/-- The standard cyclic quadratic module of type `E₇`, on `ZMod 2`. -/
@[expose] noncomputable def typeE₇StandardQuadraticModule : FiniteQuadraticModule where
  toFiniteBilinearModule := {
    carrier := ZMod 2
    pairing := LinearMap.toAddMonoidHom'.comp typeE₇StandardQuadraticMap.polarBilin.toAddMonoidHom
    pairing_comm := fun x y ↦ QuadraticMap.polar_comm typeE₇StandardQuadraticMap x y }
  quadratic := typeE₇StandardQuadraticMap
  polar_eq_pairing' := fun _ _ ↦ rfl

/-- The generator of the standard type-`E₇` quadratic map has value `3/4`. -/
@[simp]
theorem typeE₇StandardQuadraticMap_one :
    typeE₇StandardQuadraticMap 1 =
      (((3 : ℚ) / 4 : ℚ) : AddCircle (1 : ℚ)) :=
  cyclicQuadraticMap_one 2 _ _ _

/-- The standard cyclic quadratic module of type `E₇` is isometric to the discriminant
quadratic module of the `E₇` root lattice. -/
noncomputable def typeE₇DiscriminantQuadraticIsometry :
    FiniteQuadraticModule.Isometry typeE₇StandardQuadraticModule
      (typeE₇RootLattice.discriminantQuadraticModule isEven_typeE₇RootLattice) :=
  quadraticMapIsometryOfGenerator 2 typeE₇StandardQuadraticMap
    (typeE₇RootLattice.discriminantQuadraticMap isEven_typeE₇RootLattice)
    typeE₇DiscriminantGroupEquiv (by
      rw [typeE₇DiscriminantGroupEquiv_apply_one,
        discriminantQuadraticMap_typeE₇MinusculeWeightClass, typeE₇StandardQuadraticMap_one])

/-- The underlying additive equivalence of the type-`E₇` quadratic isometry. -/
@[simp]
theorem typeE₇DiscriminantQuadraticIsometry_toAddEquiv :
    typeE₇DiscriminantQuadraticIsometry.toAddEquiv = typeE₇DiscriminantGroupEquiv := by
  rw [typeE₇DiscriminantQuadraticIsometry]
  rfl

/-- The type-`E₇` quadratic isometry acts through the discriminant-group equivalence. -/
@[simp]
theorem typeE₇DiscriminantQuadraticIsometry_apply (x : ZMod 2) :
    typeE₇DiscriminantQuadraticIsometry x = typeE₇DiscriminantGroupEquiv x := by
  rw [typeE₇DiscriminantQuadraticIsometry]
  rfl

/-! ## The root lattice of type `E₈` -/

/-- The root lattice of type `E₈`: the rank-eight integral lattice on `Fin 8 → ℚ` whose
Gram matrix in the standard basis of simple roots is `CartanMatrix.E 8`. -/
noncomputable def typeE₈RootLattice : IntegralLattice (Fin 8 → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin 8)) (CartanMatrix.E 8) (CartanMatrix.E_isSymm 8)

/-- The `i`-th simple root of the type `E₈` root lattice, as a vector of the ambient space. -/
-- This is sealed so `Pi.basisFun_apply` does not rewrite beneath it and destabilize the simp API.
noncomputable def typeE₈SimpleRoot (i : Fin 8) : Fin 8 → ℚ := Pi.basisFun ℚ (Fin 8) i

/-- The `i`-th simple root of type `E₈` is the `i`-th standard coordinate vector. -/
@[simp]
theorem typeE₈SimpleRoot_apply (i j : Fin 8) :
    typeE₈SimpleRoot i j = if j = i then 1 else 0 := by
  simp [typeE₈SimpleRoot, Pi.basisFun_apply, Pi.single_apply]

/-- **The Gram matrix of the type `E₈` root lattice in its simple-root basis is the Cartan matrix
`CartanMatrix.E 8`.** -/
@[simp]
theorem form_typeE₈SimpleRoot_typeE₈SimpleRoot (i j : Fin 8) :
    typeE₈RootLattice.form (typeE₈SimpleRoot i) (typeE₈SimpleRoot j) =
      (((CartanMatrix.E 8) i j : ℤ) : ℚ) := by
  rw [typeE₈SimpleRoot, typeE₈SimpleRoot, typeE₈RootLattice]
  exact form_ofGramMatrix_basisFun_basisFun _ _ i j

/-- A vector belongs to the type `E₈` root lattice exactly when all of its simple-root coordinates
are integers. -/
@[simp]
theorem mem_typeE₈RootLattice_carrier_iff (x : Fin 8 → ℚ) :
    x ∈ typeE₈RootLattice.carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i := by
  rw [typeE₈RootLattice]
  exact mem_ofGramMatrix_basisFun_carrier_iff _ _ x

/-- The determinant of the type `E₈` Cartan matrix is nonzero. -/
private theorem det_cartanMatrixE₈_ne_zero : (CartanMatrix.E 8).det ≠ 0 := by
  rw [CartanMatrix.E₈_det]
  norm_num

/-- The type `E₈` root lattice is nondegenerate because its Cartan matrix is nonsingular. -/
noncomputable instance instIsNondegenerateTypeE₈RootLattice :
    typeE₈RootLattice.IsNondegenerate := by
  rw [typeE₈RootLattice]
  refine isNondegenerate_ofGramMatrix _ _ _ ?_
  convert det_cartanMatrixE₈_ne_zero

/-- The type `E₈` root lattice is even: every diagonal Cartan entry is `2`. -/
theorem isEven_typeE₈RootLattice : typeE₈RootLattice.IsEven := by
  rw [typeE₈RootLattice, isEven_ofGramMatrix_iff]
  decide

/-- **The determinant of the type `E₈` root lattice is `1`.** -/
@[simp]
theorem determinant_typeE₈RootLattice : typeE₈RootLattice.determinant = 1 := by
  rw [typeE₈RootLattice, determinant_ofGramMatrix]
  convert CartanMatrix.E₈_det

/-- The discriminant of the type `E₈` root lattice is `1`. -/
@[simp]
theorem discriminant_typeE₈RootLattice : typeE₈RootLattice.discriminant = 1 := by
  rw [discriminant_def, determinant_typeE₈RootLattice]
  decide

/-- **The type `E₈` root lattice is unimodular**: its Cartan determinant is `1`. -/
theorem isUnimodular_typeE₈RootLattice : typeE₈RootLattice.IsUnimodular := by
  rw [isUnimodular_iff_isUnit_determinant, determinant_typeE₈RootLattice]
  exact isUnit_one

/-- **The type `E₈` root lattice is self-dual.** -/
@[simp]
theorem dualCarrier_typeE₈RootLattice :
    typeE₈RootLattice.dualCarrier = typeE₈RootLattice.carrier :=
  (typeE₈RootLattice.isUnimodular_def.mp isUnimodular_typeE₈RootLattice).symm

/-- **The discriminant group of the type `E₈` root lattice is trivial.** -/
instance instSubsingletonDiscriminantGroupTypeE₈RootLattice :
    Subsingleton typeE₈RootLattice.DiscriminantGroup :=
  typeE₈RootLattice.isUnimodular_iff_subsingleton_discriminantGroup.mp
    isUnimodular_typeE₈RootLattice

/-- **The discriminant group of the type `E₈` root lattice has order `1`.** -/
-- This is not a `simp` lemma because `Nat.card_eq_fintype_card` rewrites its left-hand side.
theorem natCard_discriminantGroup_typeE₈RootLattice :
    Nat.card typeE₈RootLattice.DiscriminantGroup = 1 := by
  rw [natCard_discriminantGroup, discriminant_typeE₈RootLattice]

/-- **The discriminant quadratic form of the type `E₈` root lattice is trivial**, its discriminant
group having a single element. -/
@[simp]
theorem discriminantQuadraticMap_typeE₈RootLattice (x : typeE₈RootLattice.DiscriminantGroup) :
    typeE₈RootLattice.discriminantQuadraticMap isEven_typeE₈RootLattice x = 0 := by
  rw [Subsingleton.elim x 0, map_zero]

end IntegralLattice

end TauCeti
