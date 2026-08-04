/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.CentralCharacter

/-!
# The primitive central idempotents of a group algebra

Attached to a representation `ρ` of a finite group `G` over a field `k`, with character `χ`, is the
group-algebra element `∑_g χ(g⁻¹) g`, called `TauCeti.Representation.characterSum` here. Because the
character is a class function this element is central, so an irreducible representation `σ` sees it
as the single scalar recorded by the central character of
`TauCeti/RepresentationTheory/CharacterTable/CentralCharacter.lean`.

Two computations of one trace pin that scalar down. The trace of the action of `∑_g χ(g⁻¹) g` on
`σ` is the scalar times the degree `ψ(1)` on one side and `∑_g χ(g⁻¹) ψ(g)` on the other, which the
orthogonality relations of Mathlib's `Representation.char_orthonormal` evaluate to `|G|` or to `0`
according to whether `ρ` and `σ` are isomorphic. Two consequences follow. Taking `σ = ρ`, the
product of the scalar with the degree `χ(1)` is `|G|`, a unit, so **the degree of an irreducible
representation is itself a unit in `k`**: the characteristic of `k` divides no irreducible degree,
which is what makes dividing by degrees legitimate below. Rescaling then gives the **primitive
central idempotent**

`e_ρ = (χ(1) / |G|) ∑_g χ(g⁻¹) g`,

which acts as the identity on `ρ` and as zero on every irreducible representation not isomorphic to
`ρ`.

The multiplicative identities are obtained coefficient by coefficient rather than through a
Wedderburn decomposition. The coefficient of `x` in `(∑_g χ(g⁻¹) g) · (∑_g ψ(g⁻¹) g)` is
`∑_g χ(g⁻¹) ψ(x⁻¹ g)`, which is exactly the trace of `σ(x⁻¹)` composed with the action of
`∑_g χ(g⁻¹) g` on `σ`; that action is a scalar when `σ` is irreducible, so the trace collapses to a
multiple of `ψ(x⁻¹)`, the coefficient of `x` in `∑_g ψ(g⁻¹) g`. Orthogonality of the idempotents,
and `e_ρ² = e_ρ`, are then read off from the values of the central character.

That the `e_ρ` sum to `1` needs the classification of the irreducible representations indexing that
sum, and is not proved here.

## Main definitions

* `TauCeti.Representation.characterSum`: the group-algebra element `∑_g χ(g⁻¹) g`, with
  `TauCeti.Representation.characterSumCenter` the same element read in the centre.
* `TauCeti.Representation.primitiveCentralIdempotent`: the element
  `e_ρ = (χ(1) / |G|) ∑_g χ(g⁻¹) g` of an irreducible representation, with
  `TauCeti.Representation.primitiveCentralIdempotentCenter` the same element read in the centre.

## Main statements

* `TauCeti.Representation.characterSum_mul_characterSum`: multiplying by `∑_g χ(g⁻¹) g` rescales the
  character sum of an irreducible representation by the scalar its central character records.
* `TauCeti.Representation.centralCharacter_characterSumCenter_mul_char_one`: that scalar, times the
  degree, is `|G|` for isomorphic representations and `0` otherwise.
* `TauCeti.Representation.isUnit_char_one`: the degree of an irreducible representation is a unit
  in `k`.
* `TauCeti.Representation.asAlgebraHom_primitiveCentralIdempotent`: `e_ρ` acts as the identity on
  `ρ` and as zero on an irreducible representation not isomorphic to `ρ`.
* `TauCeti.Representation.primitiveCentralIdempotent_mul_primitiveCentralIdempotent`: the
  idempotents attached to non-isomorphic irreducible representations are orthogonal, with
  `TauCeti.Representation.isIdempotentElem_primitiveCentralIdempotent` the diagonal case and
  `TauCeti.Representation.primitiveCentralIdempotent_ne_zero` their nonvanishing.

## References

This implements the "primitive central idempotents" item of Layer 3 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).
See J.-P. Serre, *Linear Representations of Finite Groups*, Section 2.6, or I. M. Isaacs,
*Character Theory of Finite Groups*, Theorem 2.12.
-/

public section

open Module (finrank)
open scoped MonoidAlgebra

namespace TauCeti

namespace Representation

universe u v w

variable {k : Type u} {G : Type v} {V : Type w} {W : Type*}
variable [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable (ρ : Representation k G V) (σ : Representation k G W)

/-! ### The character sum -/

section Defs

variable [Fintype G]

/-- The group-algebra element `∑_g χ(g⁻¹) g` attached to a representation with character `χ`.

It is central because the character is a class function, and it is the unnormalized form of
`TauCeti.Representation.primitiveCentralIdempotent`. -/
noncomputable def characterSum : k[G] :=
  ∑ g : G, MonoidAlgebra.single g (ρ.character g⁻¹)

/-- The coefficients of `∑_g χ(g⁻¹) g` are the character values at the inverses.

This is the simp normal form: the sum of `MonoidAlgebra.single`s is evaluated. -/
@[simp]
theorem characterSum_coeff (g : G) : (characterSum ρ).coeff g = ρ.character g⁻¹ := by
  classical
  simp [characterSum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- The character sum commutes with every group element: conjugation permutes the terms, and the
character is constant on conjugacy classes. -/
theorem characterSum_commutes (h : G) :
    characterSum ρ * MonoidAlgebra.of k G h = MonoidAlgebra.of k G h * characterSum ρ := by
  simp only [characterSum, Finset.sum_mul, Finset.mul_sum, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single, one_mul, mul_one]
  refine Fintype.sum_equiv ((Equiv.mulLeft h⁻¹).trans (Equiv.mulRight h)) _ _ fun x => ?_
  simp only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight]
  rw [show h * (h⁻¹ * x * h) = x * h from by group,
    show (h⁻¹ * x * h)⁻¹ = h⁻¹ * x⁻¹ * (h⁻¹)⁻¹ from by group,
    _root_.Representation.char_conj]

/-- The character sum lies in the centre of the group algebra. -/
theorem characterSum_mem_center : characterSum ρ ∈ Subalgebra.center k k[G] := by
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of g => exact (characterSum_commutes ρ g).symm
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]
  | smul r x hx => rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hx]

/-- The character sum `∑_g χ(g⁻¹) g`, read as an element of the centre of the group algebra. -/
@[expose]
noncomputable def characterSumCenter : Subalgebra.center k k[G] :=
  ⟨characterSum ρ, characterSum_mem_center ρ⟩

/-- The underlying group-algebra element of the central character sum is the character sum. -/
@[simp]
theorem characterSumCenter_coe : (characterSumCenter ρ : k[G]) = characterSum ρ :=
  rfl

/-- The action of the character sum of `ρ` on a representation `σ`, as a linear combination of the
operators of `σ`. -/
theorem asAlgebraHom_characterSum :
    σ.asAlgebraHom (characterSum ρ) = ∑ g : G, ρ.character g⁻¹ • σ g := by
  simp [characterSum, map_sum, _root_.Representation.asAlgebraHom_single]

/-- The trace of the action of the character sum of `ρ` on `σ`, after `σ(x⁻¹)`, expanded as a sum of
products of character values.

Its right-hand side is the coefficient of `x` in the product of the two character sums, and its
left-hand side collapses to a scalar multiple of a single character value when `σ` is irreducible;
comparing the two is how `TauCeti.Representation.characterSum_mul_characterSum` is proved. -/
theorem trace_mul_asAlgebraHom_characterSum (x : G) :
    LinearMap.trace k W (σ x⁻¹ * σ.asAlgebraHom (characterSum ρ)) =
      ∑ g : G, ρ.character g⁻¹ * σ.character (x⁻¹ * g) := by
  rw [asAlgebraHom_characterSum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mul_smul_comm, ← _root_.map_mul σ, map_smul, smul_eq_mul]
  rfl

end Defs

/-! ### Multiplying by a character sum -/

section Product

variable [Fintype G] [FiniteDimensional k W] [IsAlgClosed k] [σ.IsIrreducible]

/-- **Multiplication by the character sum of `ρ`** rescales the character sum of an irreducible `σ`
by the scalar that the central character of `σ` records.

The coefficient of `x` on the left is `∑_g χ(g⁻¹) ψ(x⁻¹ g)`, which
`TauCeti.Representation.trace_mul_asAlgebraHom_characterSum` identifies with a trace; a central
element acts on an irreducible representation by a scalar, so that trace collapses to a multiple of
`ψ(x⁻¹)`, the coefficient of `x` on the right. -/
theorem characterSum_mul_characterSum :
    characterSum ρ * characterSum σ =
      centralCharacter σ (characterSumCenter ρ) • characterSum σ := by
  classical
  ext x
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ fun _ => by simp]
  have hcoeff : ∑ g : G, (characterSum ρ).coeff g * (characterSum σ).coeff (g⁻¹ * x) =
      ∑ g : G, ρ.character g⁻¹ * σ.character (x⁻¹ * g) := by
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [characterSum_coeff, characterSum_coeff, mul_inv_rev, inv_inv]
  have hscalar : σ.asAlgebraHom (characterSum ρ) =
      centralCharacter σ (characterSumCenter ρ) • LinearMap.id := by
    rw [← characterSumCenter_coe ρ]
    exact asAlgebraHom_center σ (characterSumCenter ρ)
  rw [hcoeff, ← trace_mul_asAlgebraHom_characterSum ρ σ x, hscalar,
    show (LinearMap.id : W →ₗ[k] W) = 1 from rfl, mul_smul_comm, mul_one, map_smul, smul_eq_mul]
  simp [_root_.Representation.character]

end Product

/-! ### The scalar attached to a pair of irreducible representations -/

section Scalar

variable [Fintype G] [FiniteDimensional k V] [FiniteDimensional k W] [IsAlgClosed k]
variable [Invertible (Nat.card G : k)] [ρ.IsIrreducible] [σ.IsIrreducible]

open scoped Classical in
/-- **The scalar by which the character sum of `ρ` acts on an irreducible `σ`.** In division-free
form: the value of the central character of `σ` on `∑_g χ(g⁻¹) g`, times the degree `ψ(1)` of `σ`,
is `|G|` when `ρ` and `σ` are isomorphic and `0` otherwise.

This is the orthogonality relation of the irreducible characters, read through the central
character. -/
theorem centralCharacter_characterSumCenter_mul_char_one :
    centralCharacter σ (characterSumCenter ρ) * σ.character 1 =
      Nat.card G * (if Nonempty (ρ.Equiv σ) then 1 else 0) := by
  have htrace : LinearMap.trace k W (σ.asAlgebraHom (characterSum ρ)) =
      ∑ g : G, σ.character g * ρ.character g⁻¹ := by
    have h := trace_mul_asAlgebraHom_characterSum ρ σ 1
    simp only [inv_one, _root_.map_one, one_mul] at h
    rw [h]
    exact Finset.sum_congr rfl fun g _ => mul_comm _ _
  have hcenter := trace_asAlgebraHom_center σ (characterSumCenter ρ)
  rw [characterSumCenter_coe, htrace, ← σ.char_one] at hcenter
  rw [← hcenter, ← _root_.Representation.char_orthonormal σ ρ, ← mul_assoc,
    mul_inv_cancel₀ (Invertible.ne_zero _), one_mul]

end Scalar

/-! ### The degree of an irreducible representation is a unit -/

section Degree

variable [Finite G] [FiniteDimensional k V] [IsAlgClosed k]
variable [Invertible (Nat.card G : k)] [ρ.IsIrreducible]

/-- **The degree of an irreducible representation is a unit in the base field.** Over an
algebraically closed field whose characteristic does not divide `|G|`, that characteristic divides
no irreducible degree.

This is the diagonal case of
`TauCeti.Representation.centralCharacter_characterSumCenter_mul_char_one`: the degree times the
scalar by which the character sum acts is `|G|`, which is a unit by hypothesis. -/
theorem isUnit_char_one : IsUnit (ρ.character 1) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have h := centralCharacter_characterSumCenter_mul_char_one ρ ρ
  rw [if_pos ⟨_root_.Representation.Equiv.refl ρ⟩, mul_one] at h
  exact isUnit_of_mul_isUnit_right (h ▸ isUnit_of_invertible (Nat.card G : k))

include ρ in
/-- The dimension of an irreducible representation is a unit in the base field. -/
theorem isUnit_finrank : IsUnit (finrank k V : k) := by
  have h := isUnit_char_one ρ
  rwa [_root_.Representation.char_one] at h

end Degree

/-! ### The primitive central idempotents -/

section Idempotent

variable [Fintype G]

/-- **The primitive central idempotent** `e_ρ = (χ(1) / |G|) ∑_g χ(g⁻¹) g` of an irreducible
representation over an algebraically closed field whose characteristic does not divide `|G|`.

It is the Wedderburn projector onto the block of `ρ`: it acts as the identity on `ρ` and as zero on
every irreducible representation not isomorphic to `ρ`, by
`TauCeti.Representation.asAlgebraHom_primitiveCentralIdempotent`. That property forces the
normalization, and it is what makes the element idempotent
(`TauCeti.Representation.isIdempotentElem_primitiveCentralIdempotent`); the hypotheses are exactly
the ones the idempotence needs, so the definition is stated with them rather than for a bare
formula. Use `TauCeti.Representation.characterSum` for the unnormalized element `∑_g χ(g⁻¹) g`,
which is defined for every representation. -/
noncomputable def primitiveCentralIdempotent [FiniteDimensional k V] [IsAlgClosed k]
    [Invertible (Nat.card G : k)] [ρ.IsIrreducible] : k[G] :=
  ((Nat.card G : k)⁻¹ * ρ.character 1) • characterSum ρ

variable [FiniteDimensional k V] [FiniteDimensional k W] [IsAlgClosed k]
variable [Invertible (Nat.card G : k)] [ρ.IsIrreducible] [σ.IsIrreducible]

/-- The coefficients of the primitive central idempotent.

This is the simp normal form: the definition is evaluated to the coefficient
`(χ(1) / |G|) · χ(g⁻¹)`. -/
@[simp]
theorem primitiveCentralIdempotent_coeff (g : G) :
    (primitiveCentralIdempotent ρ).coeff g =
      (Nat.card G : k)⁻¹ * ρ.character 1 * ρ.character g⁻¹ := by
  simp [primitiveCentralIdempotent]

/-- The primitive central idempotent lies in the centre of the group algebra. -/
theorem primitiveCentralIdempotent_mem_center :
    primitiveCentralIdempotent ρ ∈ Subalgebra.center k k[G] :=
  Subalgebra.smul_mem _ (characterSum_mem_center ρ) _

/-- The primitive central idempotent, read as an element of the centre of the group algebra. -/
@[expose]
noncomputable def primitiveCentralIdempotentCenter : Subalgebra.center k k[G] :=
  ⟨primitiveCentralIdempotent ρ, primitiveCentralIdempotent_mem_center ρ⟩

/-- The underlying group-algebra element of the central primitive idempotent is the primitive
central idempotent. -/
@[simp]
theorem primitiveCentralIdempotentCenter_coe :
    (primitiveCentralIdempotentCenter ρ : k[G]) = primitiveCentralIdempotent ρ :=
  rfl

/-- The primitive central idempotent is the character sum rescaled by `χ(1) / |G|`, in the
centre. -/
theorem primitiveCentralIdempotentCenter_eq_smul :
    primitiveCentralIdempotentCenter ρ =
      ((Nat.card G : k)⁻¹ * ρ.character 1) • characterSumCenter ρ := by
  apply Subtype.ext
  simp [primitiveCentralIdempotent]

open scoped Classical in
/-- **An irreducible representation sees `e_ρ` as `1` or as `0`**, according to whether it is
isomorphic to `ρ`. -/
theorem centralCharacter_primitiveCentralIdempotentCenter :
    centralCharacter σ (primitiveCentralIdempotentCenter ρ) =
      if Nonempty (ρ.Equiv σ) then 1 else 0 := by
  have hne : (Nat.card G : k) ≠ 0 := Invertible.ne_zero _
  refine mul_right_cancel₀ (isUnit_char_one σ).ne_zero ?_
  rw [primitiveCentralIdempotentCenter_eq_smul, map_smul, smul_eq_mul, mul_assoc,
    centralCharacter_characterSumCenter_mul_char_one ρ σ]
  rcases isEmpty_or_nonempty (ρ.Equiv σ) with hE | hN
  · rw [if_neg (not_nonempty_iff.2 hE)]
    ring
  · rw [if_pos hN, mul_one, one_mul, _root_.Representation.char_iso hN.some, mul_assoc,
      mul_comm (σ.character 1), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

open scoped Classical in
/-- **`e_ρ` is the Wedderburn projector onto the block of `ρ`**: it acts as the identity on `ρ`
itself and as zero on every irreducible representation not isomorphic to `ρ`. -/
theorem asAlgebraHom_primitiveCentralIdempotent :
    σ.asAlgebraHom (primitiveCentralIdempotent ρ) =
      if Nonempty (ρ.Equiv σ) then LinearMap.id else 0 := by
  rw [← primitiveCentralIdempotentCenter_coe ρ, asAlgebraHom_center σ,
    centralCharacter_primitiveCentralIdempotentCenter ρ σ]
  split <;> simp

open scoped Classical in
/-- **The primitive central idempotents are orthogonal**: `e_ρ e_σ` is `e_σ` when `ρ` and `σ` are
isomorphic, and `0` otherwise. -/
theorem primitiveCentralIdempotent_mul_primitiveCentralIdempotent :
    primitiveCentralIdempotent ρ * primitiveCentralIdempotent σ =
      if Nonempty (ρ.Equiv σ) then primitiveCentralIdempotent σ else 0 := by
  have hval : ((Nat.card G : k)⁻¹ * ρ.character 1) *
      centralCharacter σ (characterSumCenter ρ) = if Nonempty (ρ.Equiv σ) then 1 else 0 := by
    rw [← centralCharacter_primitiveCentralIdempotentCenter ρ σ,
      primitiveCentralIdempotentCenter_eq_smul, map_smul, smul_eq_mul]
  rw [primitiveCentralIdempotent, primitiveCentralIdempotent, smul_mul_smul_comm,
    characterSum_mul_characterSum ρ σ, smul_smul, mul_right_comm, hval]
  split
  · rw [one_mul]
  · rw [zero_mul, zero_smul]

/-- **Each primitive central idempotent is idempotent.** -/
theorem isIdempotentElem_primitiveCentralIdempotent :
    IsIdempotentElem (primitiveCentralIdempotent ρ) := by
  classical
  rw [IsIdempotentElem, primitiveCentralIdempotent_mul_primitiveCentralIdempotent ρ ρ,
    if_pos ⟨_root_.Representation.Equiv.refl ρ⟩]

/-- Non-isomorphic irreducible representations give orthogonal primitive central idempotents. -/
theorem primitiveCentralIdempotent_mul_eq_zero (h : IsEmpty (ρ.Equiv σ)) :
    primitiveCentralIdempotent ρ * primitiveCentralIdempotent σ = 0 := by
  classical
  rw [primitiveCentralIdempotent_mul_primitiveCentralIdempotent ρ σ,
    if_neg (not_nonempty_iff.2 h)]

/-- **A primitive central idempotent is nonzero**: its coefficient at `1` is `χ(1)² / |G|`, and the
degree of an irreducible representation is a unit. -/
theorem primitiveCentralIdempotent_ne_zero : primitiveCentralIdempotent ρ ≠ 0 := by
  intro h
  have hcoeff : (primitiveCentralIdempotent ρ).coeff 1 = 0 := by rw [h]; simp
  rw [primitiveCentralIdempotent_coeff, inv_one] at hcoeff
  have hcard : ((Nat.card G : k))⁻¹ ≠ 0 := inv_ne_zero (Invertible.ne_zero _)
  have hdeg := (isUnit_char_one ρ).ne_zero
  exact mul_ne_zero (mul_ne_zero hcard hdeg) hdeg hcoeff

end Idempotent

end Representation

end TauCeti
