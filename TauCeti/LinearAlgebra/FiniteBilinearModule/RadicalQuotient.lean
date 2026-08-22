/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Basic

/-!
# Quotients of a finite bilinear module by a subgroup of its radical

A subgroup `K` of the radical of a finite bilinear module `A` pairs trivially with everything, so
the pairing descends to the quotient `A / K`:

```text
b (x + K) (y + K) = b x y.
```

The resulting module is nondegenerate exactly when `K` is the whole radical, since the radical of
the quotient is the image of `rad(A)`. Taking `K = rad(A)` therefore gives the canonical
nondegenerate quotient, and other choices of `K` arise when a specific subgroup is being divided
out.

Both `quotientOfLeRadical` and `radicalQuotient` are exposed, so their carriers reduce to the
`Submodule` quotient and a map out of either can be built directly with `Submodule.liftQ` or
`QuadraticMap.lift`.

## Main declarations

* `TauCeti.FiniteBilinearModule.quotientOfLeRadical`: the quotient by a subgroup of the radical.
* `TauCeti.FiniteBilinearModule.radical_quotientOfLeRadical`: the radical of the quotient is the
  image of the radical.
* `TauCeti.FiniteBilinearModule.isNondegenerate_quotientOfLeRadical_iff`: nondegeneracy holds
  exactly when the subgroup exhausts the radical.
* `TauCeti.FiniteBilinearModule.card_quotientOfLeRadical`: the order of the quotient is the index
  of the subgroup.
* `TauCeti.FiniteBilinearModule.quotientOfLeRadicalMk_eq_iff`: two elements have the same class
  exactly when they differ by an element of the subgroup.
* `TauCeti.FiniteBilinearModule.radicalQuotient`: the nondegenerate quotient by the radical.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

namespace TauCeti.FiniteBilinearModule

universe u

variable (A : FiniteBilinearModule.{u})

/-! ## Quotient by a subgroup of the radical -/

/-- The underlying additive quotient of a finite bilinear module by a subgroup.

This is a `Submodule` quotient, so `Submodule.liftQ` and `QuadraticMap.lift` apply to it. It is
the carrier of `quotientOfLeRadical` when the subgroup lies in the radical. -/
abbrev QuotientByAddSubgroup (K : AddSubgroup A) := A.carrier ⧸ K.toIntSubmodule

/-- A subgroup of the radical, read as a `ℤ`-submodule, lies in the kernel of the pairing. -/
theorem toIntSubmodule_le_ker_toBilin {K : AddSubgroup A} (hK : K ≤ A.radical) :
    K.toIntSubmodule ≤ A.toBilin.ker := by
  intro x hx
  rw [LinearMap.mem_ker]
  ext y
  rw [LinearMap.zero_apply, A.toBilin_apply]
  exact A.mem_radical_iff x |>.mp (hK hx) y

/-- The pairing of a finite bilinear module, descended through a subgroup of its radical.

This is the underlying `ℤ`-bilinear map of `quotientOfLeRadical`. -/
noncomputable def quotientOfLeRadicalBilin (K : AddSubgroup A) (hK : K ≤ A.radical) :
    A.QuotientByAddSubgroup K →ₗ[ℤ] A.QuotientByAddSubgroup K →ₗ[ℤ] AddCircle (1 : ℚ) :=
  LinearMap.IsRefl.liftQ₂ A.toBilin K.toIntSubmodule A.isRefl_toBilin
    (A.toIntSubmodule_le_ker_toBilin hK)

/-- The descended pairing is computed by the original pairing on representatives. -/
@[simp]
theorem quotientOfLeRadicalBilin_mk (K : AddSubgroup A) (hK : K ≤ A.radical) (x y : A) :
    A.quotientOfLeRadicalBilin K hK (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      A.pairing x y := by
  rw [quotientOfLeRadicalBilin, LinearMap.liftQ₂_mk, A.toBilin_apply]

/-- The finite bilinear module obtained by quotienting by a subgroup of the radical.

The package is exposed so that its carrier projection reduces to the `Submodule` quotient
`QuotientByAddSubgroup`, which is what a map out of the quotient needs. -/
@[expose] noncomputable def quotientOfLeRadical (K : AddSubgroup A) (hK : K ≤ A.radical) :
    FiniteBilinearModule where
  carrier := A.QuotientByAddSubgroup K
  finite := Finite.of_surjective K.toIntSubmodule.mkQ K.toIntSubmodule.mkQ_surjective
  pairing :=
    { toFun := fun x ↦ (A.quotientOfLeRadicalBilin K hK x).toAddMonoidHom
      map_zero' := by
        exact congrArg LinearMap.toAddMonoidHom (map_zero (A.quotientOfLeRadicalBilin K hK))
      map_add' := by
        intro x y
        exact congrArg LinearMap.toAddMonoidHom (map_add (A.quotientOfLeRadicalBilin K hK) x y) }
  pairing_comm := by
    intro x y
    induction x using Submodule.Quotient.induction_on with | H x =>
    induction y using Submodule.Quotient.induction_on with | H y =>
    -- `CharacterModule` is an opaque `def` alias for additive homomorphisms, so its evaluation
    -- cannot be simplified to the quotient bilinear map by a public rewrite lemma.
    change A.quotientOfLeRadicalBilin K hK (Submodule.Quotient.mk x)
      (Submodule.Quotient.mk y) = A.quotientOfLeRadicalBilin K hK (Submodule.Quotient.mk y)
        (Submodule.Quotient.mk x)
    rw [A.quotientOfLeRadicalBilin_mk K hK, A.quotientOfLeRadicalBilin_mk K hK]
    exact A.pairing_comm x y

/-- The quotient map onto the quotient by a subgroup of the radical. -/
noncomputable def quotientOfLeRadicalMk (K : AddSubgroup A) (hK : K ≤ A.radical) :
    A →+ A.quotientOfLeRadical K hK :=
  K.toIntSubmodule.mkQ.toAddMonoidHom

/-- The quotient pairing is represented by the original pairing on representatives. -/
@[simp]
theorem quotientOfLeRadical_pairing_mk (K : AddSubgroup A) (hK : K ≤ A.radical) (x y : A) :
    (A.quotientOfLeRadical K hK).pairing (A.quotientOfLeRadicalMk K hK x)
      (A.quotientOfLeRadicalMk K hK y) = A.pairing x y := by
  -- Unfold the opaque `CharacterModule` alias to expose evaluation of the quotient lift.
  change A.quotientOfLeRadicalBilin K hK (Submodule.Quotient.mk x)
    (Submodule.Quotient.mk y) = A.pairing x y
  exact A.quotientOfLeRadicalBilin_mk K hK x y

/-- The quotient map by a subgroup of the radical is surjective. -/
theorem quotientOfLeRadicalMk_surjective (K : AddSubgroup A) (hK : K ≤ A.radical) :
    Function.Surjective (A.quotientOfLeRadicalMk K hK) :=
  K.toIntSubmodule.mkQ_surjective

/-- The kernel of the quotient map by a subgroup of the radical is that subgroup. -/
@[simp]
theorem quotientOfLeRadicalMk_ker (K : AddSubgroup A) (hK : K ≤ A.radical) :
    (A.quotientOfLeRadicalMk K hK).ker = K :=
  (congrArg Submodule.toAddSubgroup K.toIntSubmodule.ker_mkQ).trans
    K.toIntSubmodule_toAddSubgroup

/-- A class in the quotient vanishes exactly when its representative lies in the subgroup. -/
@[simp]
theorem quotientOfLeRadicalMk_eq_zero_iff (K : AddSubgroup A) (hK : K ≤ A.radical) (x : A) :
    A.quotientOfLeRadicalMk K hK x = 0 ↔ x ∈ K := by
  rw [← AddMonoidHom.mem_ker, A.quotientOfLeRadicalMk_ker K hK]

/-- Two elements have the same class in the quotient exactly when they differ by an element of the
subgroup. -/
@[simp]
theorem quotientOfLeRadicalMk_eq_iff (K : AddSubgroup A) (hK : K ≤ A.radical) (x y : A) :
    A.quotientOfLeRadicalMk K hK x = A.quotientOfLeRadicalMk K hK y ↔ x - y ∈ K := by
  rw [← sub_eq_zero, ← map_sub, A.quotientOfLeRadicalMk_eq_zero_iff K hK]

/-- **The radical of the quotient** is the image of the radical: quotienting by a subgroup of the
radical does not create new degeneracy. -/
theorem radical_quotientOfLeRadical (K : AddSubgroup A) (hK : K ≤ A.radical) :
    (A.quotientOfLeRadical K hK).radical = A.radical.map (A.quotientOfLeRadicalMk K hK) := by
  ext q
  obtain ⟨x, rfl⟩ := A.quotientOfLeRadicalMk_surjective K hK q
  constructor
  · intro hq
    refine ⟨x, (A.mem_radical_iff x).mpr fun y ↦ ?_, rfl⟩
    rw [← A.quotientOfLeRadical_pairing_mk K hK x y]
    exact (mem_radical_iff _ _).mp hq _
  · rintro ⟨z, hz, hzx⟩
    rw [mem_radical_iff]
    intro q'
    obtain ⟨y, rfl⟩ := A.quotientOfLeRadicalMk_surjective K hK q'
    rw [← hzx, A.quotientOfLeRadical_pairing_mk K hK]
    exact (A.mem_radical_iff z).mp hz y

/-- **Nondegeneracy of the quotient.** Quotienting by a subgroup of the radical leaves a
nondegenerate module exactly when that subgroup exhausts the radical. -/
theorem isNondegenerate_quotientOfLeRadical_iff (K : AddSubgroup A) (hK : K ≤ A.radical) :
    (A.quotientOfLeRadical K hK).IsNondegenerate ↔ A.radical ≤ K := by
  rw [isNondegenerate_iff_radical_eq_bot, A.radical_quotientOfLeRadical K hK, eq_bot_iff]
  constructor
  · intro h x hx
    exact (A.quotientOfLeRadicalMk_eq_zero_iff K hK x).mp (h ⟨x, hx, rfl⟩)
  · rintro h q ⟨x, hx, rfl⟩
    rw [AddSubgroup.mem_bot, A.quotientOfLeRadicalMk_eq_zero_iff K hK]
    exact h hx

/-- The order of the quotient by a subgroup of the radical is the index of that subgroup. -/
theorem card_quotientOfLeRadical (K : AddSubgroup A) (hK : K ≤ A.radical) :
    Nat.card (A.quotientOfLeRadical K hK) = K.index := by
  conv_rhs => rw [← A.quotientOfLeRadicalMk_ker K hK]
  rw [AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr (A.quotientOfLeRadicalMk_surjective K hK),
    AddSubgroup.card_top]

/-! ## Quotient by the radical -/

/-- The finite bilinear module obtained by quotienting by the radical.

Exposed for the same reason as `quotientOfLeRadical`: so that its carrier reduces to the
`Submodule` quotient and maps out of it are definable. -/
@[expose] noncomputable def radicalQuotient : FiniteBilinearModule :=
  A.quotientOfLeRadical A.radical le_rfl

/-- The quotient map from a finite bilinear module to its radical quotient. -/
noncomputable def radicalQuotientMk : A →+ radicalQuotient A :=
  A.quotientOfLeRadicalMk A.radical le_rfl

/-- The quotient pairing is represented by the original pairing on representatives. -/
@[simp]
theorem radicalQuotient_pairing_mk (x y : A) :
    (radicalQuotient A).pairing (radicalQuotientMk A x) (radicalQuotientMk A y) =
      A.pairing x y :=
  A.quotientOfLeRadical_pairing_mk A.radical le_rfl x y

/-- The quotient map to the radical quotient is surjective. -/
theorem radicalQuotientMk_surjective : Function.Surjective (radicalQuotientMk A) :=
  A.quotientOfLeRadicalMk_surjective A.radical le_rfl

/-- The kernel of the radical quotient map is the radical. -/
@[simp]
theorem radicalQuotientMk_ker : (radicalQuotientMk A).ker = A.radical :=
  A.quotientOfLeRadicalMk_ker A.radical le_rfl

/-- Two elements have the same class in the radical quotient exactly when they differ by an
element of the radical. -/
@[simp]
theorem radicalQuotientMk_eq_iff (x y : A) :
    A.radicalQuotientMk x = A.radicalQuotientMk y ↔ x - y ∈ A.radical :=
  A.quotientOfLeRadicalMk_eq_iff A.radical le_rfl x y

/-- Quotienting a finite bilinear module by its radical produces a nondegenerate module. -/
theorem isNondegenerate_radicalQuotient : (radicalQuotient A).IsNondegenerate :=
  (A.isNondegenerate_quotientOfLeRadical_iff A.radical le_rfl).mpr le_rfl

end TauCeti.FiniteBilinearModule
