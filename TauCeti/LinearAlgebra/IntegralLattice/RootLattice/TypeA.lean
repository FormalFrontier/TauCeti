/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Cardinality
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.Matrix.CartanTypeA
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical

/-!
# The root lattice of type `Aₙ` and its discriminant form

The positive root lattice of type `Aₙ` is the rank-`n` integral lattice whose Gram matrix in the
simple-root basis is the Cartan matrix `CartanMatrix.A n`.  This file constructs it inside
`Fin n → ℚ`, proves it even and nondegenerate, and computes its discriminant form:

```text
det Aₙ = n + 1,   A_{Aₙ} ≃+ ℤ/(n+1),   q(ω₁) = n / (2 (n + 1)).
```

The generator is the class of the first fundamental weight `ω₁`, written in the simple-root
coordinates `ω₁ = ∑ⱼ ((n - j) / (n + 1)) αⱼ` that the inverse Cartan matrix dictates.  Those
coordinates are verified against the lattice, not assumed:
`form_typeAFundamentalWeight_simpleRoot` proves `⟨ω₁, αᵢ⟩ = δ_{i,0}` directly from the row
combinations of `CartanMatrix.A n`, which then gives `⟨ω₁, ω₁⟩ = n / (n + 1)` and hence the
displayed half-norm value.  When `n > 0`, the class of `ω₁` has additive order exactly `n + 1`
because its last simple-root coordinate is `1 / (n + 1)`; at rank zero, the order statement is
trivial.  The discriminant group has that same order, so `ω₁` generates.

The half-norm convention is the one fixed by the integral-lattices roadmap: `q_L(x) = ⟨x,x⟩ / 2`
in `ℚ/ℤ`.  Nikulin's full-norm value for this row is `n / (n + 1)`.

## Main declarations

* `TauCeti.IntegralLattice.typeARootLattice`: the lattice, with Gram matrix `CartanMatrix.A n`.
* `TauCeti.IntegralLattice.form_typeASimpleRoot_typeASimpleRoot`: its simple-root Gram matrix is
  `CartanMatrix.A n`.
* `TauCeti.IntegralLattice.isEven_typeARootLattice`: it is even.
* `TauCeti.IntegralLattice.determinant_typeARootLattice`: its determinant is `n + 1`.
* `TauCeti.IntegralLattice.typeAFundamentalWeight`: the first fundamental weight `ω₁`.
* `TauCeti.IntegralLattice.typeAFundamentalWeightClass`: its class in the discriminant group.
* `TauCeti.IntegralLattice.form_typeAFundamentalWeight_self`: `⟨ω₁, ω₁⟩ = n / (n + 1)`.
* `TauCeti.IntegralLattice.addOrderOf_typeAFundamentalWeightClass`: the class of `ω₁` has order
  `n + 1`.
* `TauCeti.IntegralLattice.zmultiples_typeAFundamentalWeightClass`: that class generates the
  discriminant group.
* `TauCeti.IntegralLattice.typeADiscriminantGroupEquiv`: the resulting isomorphism
  `ZMod (n + 1) ≃+ A_{Aₙ}`.
* `TauCeti.IntegralLattice.discriminantQuadraticMap_typeAFundamentalWeightClass`:
  `q(ω₁) = n / (2 (n + 1))`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §6.1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 5, the `Aₙ` row of the ADE table.
-/

public section

namespace TauCeti

namespace IntegralLattice

open Finset

variable (n : ℕ)

/-! ## The lattice -/

/-- The positive root lattice of type `Aₙ`: the rank-`n` integral lattice on `Fin n → ℚ` whose
Gram matrix in the standard basis of simple roots is `CartanMatrix.A n`. -/
noncomputable def typeARootLattice : IntegralLattice (Fin n → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin n)) (CartanMatrix.A n) (CartanMatrix.A_isSymm n)

/-- The `i`-th simple root of the type `Aₙ` root lattice, as a vector of the ambient space.

This is sealed rather than an `abbrev`: reducibility would let `Pi.basisFun_apply` rewrite
underneath it, taking the Gram-matrix and pairing lemmas below out of `simp` normal form. -/
noncomputable def typeASimpleRoot (i : Fin n) : Fin n → ℚ := Pi.basisFun ℚ (Fin n) i

/-- The `i`-th simple root is the `i`-th standard coordinate vector. -/
@[simp]
theorem typeASimpleRoot_apply (i j : Fin n) :
    typeASimpleRoot n i j = if j = i then 1 else 0 := by
  simp [typeASimpleRoot, Pi.single_apply]

private theorem typeASimpleRoot_eq_basisFun (i : Fin n) :
    typeASimpleRoot n i = Pi.basisFun ℚ (Fin n) i := rfl

/-- The form of the type `Aₙ` root lattice, expanded in the standard coordinates. -/
theorem typeARootLattice_form_apply (x y : Fin n → ℚ) :
    (typeARootLattice n).form x y =
      ∑ i, ∑ j, x i * ((CartanMatrix.A n i j : ℤ) : ℚ) * y j := by
  -- `ofGramMatrix` and its `form` lemma are stated with classical decidability, so the
  -- `Matrix.toBilin` rewrite has to elaborate against the same instance.
  let _ : DecidableEq (Fin n) := Classical.decEq _
  rw [typeARootLattice, ofGramMatrix_form, Matrix.toBilin_apply]
  simp [Pi.basisFun_repr]

/-- Pairing an arbitrary vector against a simple root collapses the double sum to a single one. -/
theorem typeARootLattice_form_simpleRoot (x : Fin n → ℚ) (i : Fin n) :
    (typeARootLattice n).form x (typeASimpleRoot n i) =
      ∑ k, x k * ((CartanMatrix.A n k i : ℤ) : ℚ) := by
  classical
  rw [typeARootLattice_form_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp [typeASimpleRoot_apply]

/-- **The Gram matrix of the type `Aₙ` root lattice in its simple-root basis is the Cartan
matrix `CartanMatrix.A n`.** -/
@[simp]
theorem form_typeASimpleRoot_typeASimpleRoot (i j : Fin n) :
    (typeARootLattice n).form (typeASimpleRoot n i) (typeASimpleRoot n j) =
      ((CartanMatrix.A n i j : ℤ) : ℚ) := by
  have h := congrArg (fun z : ℤ ↦ (z : ℚ))
    (integralForm_ofGramMatrix_apply (Pi.basisFun ℚ (Fin n)) (CartanMatrix.A n)
      (CartanMatrix.A_isSymm n) i j)
  simpa only [integralForm_cast, ofGramMatrix.coe_basis, typeARootLattice,
    typeASimpleRoot_eq_basisFun] using h

/-- A vector belongs to the type `Aₙ` root lattice exactly when all of its simple-root
coordinates are integers. -/
@[simp]
theorem mem_typeARootLattice_carrier_iff (x : Fin n → ℚ) :
    x ∈ (typeARootLattice n).carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i := by
  classical
  rw [typeARootLattice, ofGramMatrix_carrier, Module.Basis.mem_span_iff_repr_mem]
  simp [Pi.basisFun_repr]

noncomputable instance instIsNondegenerateTypeARootLattice :
    (typeARootLattice n).IsNondegenerate := by
  refine isNondegenerate_ofGramMatrix _ _ _ ?_
  convert (isFiniteType_cartanMatrix_A n).det_ne_zero

/-- The type `Aₙ` root lattice is even: every diagonal Cartan entry is `2`. -/
theorem isEven_typeARootLattice : (typeARootLattice n).IsEven := by
  rw [typeARootLattice, isEven_ofGramMatrix_iff]
  intro i
  rw [← chainEntry_eq_cartanMatrix_A, chainEntry_self]
  exact even_two

/-- **The determinant of the type `Aₙ` root lattice is `n + 1`.** -/
@[simp]
theorem determinant_typeARootLattice : (typeARootLattice n).determinant = (n : ℤ) + 1 := by
  rw [typeARootLattice, determinant_ofGramMatrix]
  convert CartanMatrix.A_det n

/-- The discriminant of the type `Aₙ` root lattice is `n + 1`. -/
@[simp]
theorem discriminant_typeARootLattice : (typeARootLattice n).discriminant = n + 1 := by
  rw [discriminant_def, determinant_typeARootLattice]
  omega

/-- **The discriminant group of the type `Aₙ` root lattice has order `n + 1`.**

This is deliberately not a `simp` lemma: `Nat.card_eq_fintype_card` rewrites the left-hand side,
so the `simpNF` linter rejects the tagged form. -/
theorem natCard_discriminantGroup_typeARootLattice :
    Nat.card (typeARootLattice n).DiscriminantGroup = n + 1 := by
  rw [natCard_discriminantGroup, discriminant_typeARootLattice]

/-! ## The first fundamental weight -/

/-- The first fundamental weight of type `Aₙ`, in simple-root coordinates:
`ω₁ = ∑ⱼ ((n - j) / (n + 1)) αⱼ`. -/
noncomputable def typeAFundamentalWeight : Fin n → ℚ :=
  fun j ↦ ((n : ℚ) - j.val) / ((n : ℚ) + 1)

@[simp]
theorem typeAFundamentalWeight_apply (j : Fin n) :
    typeAFundamentalWeight n j = ((n : ℚ) - j.val) / ((n : ℚ) + 1) := (rfl)

variable {n}

private theorem natCast_add_one_ne_zero : ((n : ℚ) + 1) ≠ 0 := by positivity

/-- The row combination of `CartanMatrix.A n` against the fundamental-weight coordinates. -/
private theorem sum_chainEntry_mul_weight (i : ℕ) (hin : i < n) :
    ∑ k ∈ range n, ((chainEntry i k : ℤ) : ℚ) * (((n : ℚ) - k) / ((n : ℚ) + 1)) =
      if i = 0 then 1 else 0 := by
  have hn : ((n : ℚ) + 1) ≠ 0 := natCast_add_one_ne_zero
  have hweight : ∀ k : ℕ,
      ((n : ℚ) - k) / ((n : ℚ) + 1) =
        (-1 / ((n : ℚ) + 1)) * (k : ℚ) + (n : ℚ) / ((n : ℚ) + 1) := by
    intro k
    field_simp
    ring
  rw [Finset.sum_congr rfl fun k _ ↦ by rw [hweight],
    sum_range_chainEntry_mul_affine hin]
  by_cases hi : i = 0
  · subst i
    simp only [ite_true, Nat.zero_add]
    by_cases hn_one : 1 = n
    · subst n
      norm_num
    · simp only [hn_one, ite_false]
      field_simp
      ring
  · simp only [hi, ite_false]
    by_cases hend : i + 1 = n
    · simp only [hend, ite_true]
      field_simp
      ring
    · simp only [hend, ite_false]

variable (n)

/-- **The first fundamental weight pairs to `1` with the first simple root and to `0` with the
others.** -/
@[simp]
theorem form_typeAFundamentalWeight_simpleRoot (i : Fin n) :
    (typeARootLattice n).form (typeAFundamentalWeight n) (typeASimpleRoot n i) =
      if i.val = 0 then 1 else 0 := by
  classical
  rw [typeARootLattice_form_simpleRoot]
  have hconv : (∑ k, (typeAFundamentalWeight n) k * ((CartanMatrix.A n k i : ℤ) : ℚ)) =
      ∑ k ∈ range n, ((chainEntry i.val k : ℤ) : ℚ) *
        (((n : ℚ) - k) / ((n : ℚ) + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k ↦ ((chainEntry i.val k : ℤ) : ℚ) * (((n : ℚ) - k) / ((n : ℚ) + 1))) n]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← chainEntry_eq_cartanMatrix_A, chainEntry_comm]
    simp only [typeAFundamentalWeight]
    ring
  rw [hconv]
  exact sum_chainEntry_mul_weight i.val i.isLt

/-- **The self-pairing of the first fundamental weight is `n / (n + 1)`.** -/
@[simp]
theorem form_typeAFundamentalWeight_self :
    (typeARootLattice n).form (typeAFundamentalWeight n) (typeAFundamentalWeight n) =
      (n : ℚ) / ((n : ℚ) + 1) := by
  classical
  have hexpand : typeAFundamentalWeight n =
      ∑ j : Fin n, (typeAFundamentalWeight n j) • typeASimpleRoot n j := by
    ext k
    simp [typeASimpleRoot, Pi.basisFun_apply, Pi.single_apply]
  nth_rewrite 2 [hexpand]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, form_typeAFundamentalWeight_simpleRoot]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
    · simp [typeAFundamentalWeight]
    · intro b _ hb
      have hb0 : b.val ≠ 0 := fun h ↦ hb (Fin.ext h)
      simp [hb0]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-! ## The discriminant group -/

/-- The first fundamental weight lies in the dual lattice: it pairs integrally with every simple
root, hence with the whole lattice. -/
theorem typeAFundamentalWeight_mem_dualCarrier :
    typeAFundamentalWeight n ∈ (typeARootLattice n).dualCarrier := by
  classical
  rw [dualCarrier, LinearMap.BilinForm.mem_dualSubmodule]
  intro y hy
  rw [typeARootLattice, ofGramMatrix_carrier] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [← typeASimpleRoot_eq_basisFun, form_typeAFundamentalWeight_simpleRoot]
      split_ifs
      · exact Submodule.mem_one.mpr ⟨1, by norm_num⟩
      · exact Submodule.mem_one.mpr ⟨0, by norm_num⟩
  | zero => simp
  | add a b _ _ ha hb => simpa using add_mem ha hb
  | smul c a _ ha =>
      rw [map_zsmul]
      exact Submodule.smul_mem (1 : Submodule ℤ ℚ) c ha

/-- The first fundamental weight, as a vector of the dual lattice. -/
noncomputable def typeAFundamentalWeightDual : (typeARootLattice n).dualCarrier :=
  ⟨typeAFundamentalWeight n, typeAFundamentalWeight_mem_dualCarrier n⟩

@[simp]
theorem coe_typeAFundamentalWeightDual :
    (typeAFundamentalWeightDual n : Fin n → ℚ) = typeAFundamentalWeight n := (rfl)

/-- The discriminant class of the first fundamental weight. -/
noncomputable def typeAFundamentalWeightClass :
    (typeARootLattice n).DiscriminantGroup :=
  Submodule.Quotient.mk (typeAFundamentalWeightDual n)

/-- **An integer multiple of the first fundamental weight lies in the root lattice exactly when
`n + 1` divides it**.  For `n > 0`, this is forced by the last simple-root coordinate
`1 / (n + 1)` of `ω₁`; at rank zero, the result is trivial. -/
theorem zsmul_typeAFundamentalWeightClass_eq_zero_iff (k : ℤ) :
    k • typeAFundamentalWeightClass n = 0 ↔ ((n : ℤ) + 1) ∣ k := by
  classical
  have hn : ((n : ℚ) + 1) ≠ 0 := natCast_add_one_ne_zero
  rw [typeAFundamentalWeightClass, ← Submodule.Quotient.mk_smul,
    discriminantGroup_mk_eq_zero_iff, mem_typeARootLattice_carrier_iff]
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · obtain ⟨z, hz⟩ := h ⟨n - 1, by omega⟩
      refine ⟨z, ?_⟩
      have hcoord : ((n : ℚ) - ((n - 1 : ℕ) : ℚ)) = 1 := by
        rw [Nat.cast_sub hpos, Nat.cast_one]
        ring
      simp only [typeAFundamentalWeightDual, SetLike.val_smul, Pi.smul_apply,
        typeAFundamentalWeight, zsmul_eq_mul, hcoord] at hz
      have hzk : ((n : ℚ) + 1) * (z : ℚ) = (k : ℚ) := by
        field_simp at hz
        linarith
      exact_mod_cast hzk.symm
  · rintro ⟨m, rfl⟩ j
    refine ⟨m * ((n : ℤ) - j.val), ?_⟩
    simp only [typeAFundamentalWeightDual, SetLike.val_smul, Pi.smul_apply,
      typeAFundamentalWeight, zsmul_eq_mul]
    push_cast
    field_simp

/-- **The class of the first fundamental weight has additive order `n + 1`.** -/
@[simp]
theorem addOrderOf_typeAFundamentalWeightClass :
    addOrderOf (typeAFundamentalWeightClass n) = n + 1 := by
  have hiff : ∀ k : ℤ,
      ((addOrderOf (typeAFundamentalWeightClass n) : ℤ) ∣ k) ↔ ((n : ℤ) + 1) ∣ k := by
    intro k
    rw [addOrderOf_dvd_iff_zsmul_eq_zero]
    exact zsmul_typeAFundamentalWeightClass_eq_zero_iff n k
  have h₁ : (addOrderOf (typeAFundamentalWeightClass n) : ℤ) ∣ ((n : ℤ) + 1) :=
    (hiff _).mpr dvd_rfl
  have h₂ : ((n : ℤ) + 1) ∣ (addOrderOf (typeAFundamentalWeightClass n) : ℤ) :=
    (hiff _).mp dvd_rfl
  have : (addOrderOf (typeAFundamentalWeightClass n) : ℤ) = (n : ℤ) + 1 :=
    Int.dvd_antisymm (Int.natCast_nonneg _) (by positivity) h₁ h₂
  exact_mod_cast this

/-- **The class of the first fundamental weight generates the discriminant group.** -/
theorem zmultiples_typeAFundamentalWeightClass :
    AddSubgroup.zmultiples (typeAFundamentalWeightClass n) = ⊤ := by
  apply AddSubgroup.eq_top_of_card_eq
  rw [Nat.card_zmultiples, addOrderOf_typeAFundamentalWeightClass,
    natCard_discriminantGroup_typeARootLattice]

/-- **The discriminant group of the type `Aₙ` root lattice is cyclic of order `n + 1`**, with the
class of the first fundamental weight as the image of `1`. -/
noncomputable def typeADiscriminantGroupEquiv :
    ZMod (n + 1) ≃+ (typeARootLattice n).DiscriminantGroup :=
  zmodAddEquivOfGenerator
    (fun x ↦ by rw [zmultiples_typeAFundamentalWeightClass]; exact AddSubgroup.mem_top x)
    (natCard_discriminantGroup_typeARootLattice n)

@[simp]
theorem typeADiscriminantGroupEquiv_apply_one :
    typeADiscriminantGroupEquiv n 1 = typeAFundamentalWeightClass n :=
  zmodAddEquivOfGenerator_apply_one _ _

/-- **The discriminant quadratic value of the first fundamental weight is `n / (2 (n + 1))`**, in
the half-norm convention. -/
@[simp]
theorem discriminantQuadraticMap_typeAFundamentalWeightClass :
    (typeARootLattice n).discriminantQuadraticMap (isEven_typeARootLattice n)
        (typeAFundamentalWeightClass n) =
      (((n : ℚ) / (2 * ((n : ℚ) + 1)) : ℚ) : AddCircle (1 : ℚ)) := by
  have hn : ((n : ℚ) + 1) ≠ 0 := natCast_add_one_ne_zero
  rw [typeAFundamentalWeightClass, discriminantQuadraticMap_mk]
  congr 1
  rw [coe_typeAFundamentalWeightDual, form_typeAFundamentalWeight_self]
  field_simp

end IntegralLattice

end TauCeti
