/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Multilinear
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Basic
public import TauCeti.RepresentationTheory.InvariantForm

/-!
# The Frobenius-Schur trichotomy

`TauCeti.Representation.frobeniusSchurIndicator_eq_sub_finrank_invariants` computes the indicator
`ν₂(ρ) = |G|⁻¹ ∑_g χ(g²)` as the signed count `dim (Sym²V)ᴳ - dim (Λ²V)ᴳ` of invariants in the two
squares.  This file identifies those two invariant counts with counts of **bilinear forms** on `V`,
and reads the trichotomy off the identification.

The dictionary is elementary.  A functional on `Sym²V` becomes a bilinear form on `V` by composing
with the universal multilinear map, and the form it produces is symmetric because the symmetric
square does not see the order of its two arguments; a functional on `Λ²V` becomes an alternating
form for the same reason.  Both assignments are injective, because the pure tensors span.  So the
invariant functionals on the two squares inject into the invariant symmetric and the invariant
alternating forms, which meet only in `0`.  Counting on the other side, the invariant forms are the
intertwiners from `ρ` to its dual, and the character sum that counts those is the character sum that
counts the invariants of the tensor square, read along `g⁻¹` instead of `g`; so the two injections
account for every invariant form, and

`ν₂(ρ) = dim {invariant symmetric forms} - dim {invariant alternating forms}`.

On an **irreducible** representation over an algebraically closed field the invariant forms are at
most a line, and `TauCeti.Representation.IsInvariantForm.isSymm_or_isAlt` says a nonzero one is
symmetric or alternating.  The two counts are therefore `1, 0` or `0, 1` or `0, 0`, which is the
**trichotomy**: `ν₂(ρ)` is `1` when `ρ` carries a nonzero invariant symmetric form (the orthogonal
case), `-1` when it carries a nonzero invariant alternating form (the symplectic, or quaternionic,
case), and `0` when it carries no nonzero invariant form at all (the complex case).  The nonzero
invariant form of the first two cases is automatically nondegenerate, by
`TauCeti.Representation.IsInvariantForm.nondegenerate`.

Characteristic zero is used throughout, in two places: to move the counting identity from an
equation in `k` to an equation of natural numbers, and to keep a form from being symmetric and
alternating at once.

## Main definitions

* `TauCeti.Representation.symmetricInvariantForms` and
  `TauCeti.Representation.alternatingInvariantForms`: the invariant forms that are symmetric,
  respectively alternating.
* `TauCeti.Representation.ofSymmetricSquareDual` and
  `TauCeti.Representation.ofExteriorSquareDual`: a functional on the second symmetric or exterior
  power, read as a bilinear form on `V`.
* `TauCeti.Representation.invariantFormsEquivIntertwiningMapDual`: the invariant forms of `ρ` as
  the intertwiners from `ρ` to its dual.

## Main results

* `TauCeti.Representation.finrank_symmetricInvariantForms` and
  `TauCeti.Representation.finrank_alternatingInvariantForms`: the two invariant form counts are the
  invariant counts of the two squares.
* `TauCeti.Representation.frobeniusSchurIndicator_eq_sub_finrank_invariantForms`: **the indicator is
  the signed count of invariant forms**, `ν₂(ρ) = dim {symmetric} - dim {alternating}`.
* `TauCeti.Representation.frobeniusSchurIndicator_eq_one_iff`,
  `TauCeti.Representation.frobeniusSchurIndicator_eq_neg_one_iff` and
  `TauCeti.Representation.frobeniusSchurIndicator_eq_zero_iff`: **the trichotomy**, each value of
  the indicator characterized by the invariant forms, for an irreducible representation over an
  algebraically closed field of characteristic zero.
* `TauCeti.Representation.frobeniusSchurIndicator_eq_one_or_eq_zero_or_eq_neg_one`: the indicator
  of such a representation takes only the values `1`, `0` and `-1`.

## Implementation notes

The two maps out of the dual squares are only ever used through their images, so they are built as
plain linear maps rather than as equivalences onto the symmetric and alternating forms: injectivity
plus the dimension count is what forces them onto those subspaces, and proving surjectivity
directly would need the universal property of the symmetric square, which is not in Mathlib.

`TauCeti.Representation.invariantFormsEquivIntertwiningMapDual` is what connects the submodule of
invariant forms of `TauCeti/RepresentationTheory/InvariantForm.lean` to the character machinery: it
bundles the already-available `TauCeti.Representation.isInvariantForm_iff_isIntertwiningMap` into an
equivalence, which is the shape Mathlib's
`Representation.card_inv_mul_sum_char_mul_char_eq_finrank` counts.  It lives here rather than in
that file because it is the character-theoretic reading, which no other consumer of the invariant
forms uses.

Three dimension lemmas are proved for an abstract module and applied with that module supplied
explicitly.  The reason is mechanical: the `AddCommMonoid` structure on a space of bilinear forms
is the one on linear maps, and asking the elaborator to solve for an `AddCommGroup` structure
inducing it does not terminate quickly.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 7, “Invariant bilinear forms” and “The trichotomy”.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 4.
-/

public section

open scoped TensorProduct

open Module (finrank)

universe v w

variable {k : Type} {G : Type v} {V : Type w}

namespace TauCeti

namespace Representation

open LinearMap (BilinForm)

/-! ### The symmetric and the alternating invariant forms -/

section Submodules

variable [Field k] [Group G] [AddCommGroup V] [Module k V] {ρ : Representation k G V}
  {B : BilinForm k V}

/-- The **invariant symmetric** bilinear forms of `ρ`, as a submodule of all bilinear forms. -/
def symmetricInvariantForms (ρ : Representation k G V) : Submodule k (BilinForm k V) where
  carrier := {B | IsInvariantForm ρ B ∧ B.IsSymm}
  zero_mem' := ⟨isInvariantForm_zero, LinearMap.BilinForm.isSymm_zero⟩
  add_mem' hB hC := ⟨hB.1.add hC.1, hB.2.add hC.2⟩
  smul_mem' c _ hB := ⟨hB.1.smul c, hB.2.smul c⟩

/-- The **invariant alternating** bilinear forms of `ρ`, as a submodule of all bilinear forms. -/
def alternatingInvariantForms (ρ : Representation k G V) : Submodule k (BilinForm k V) where
  carrier := {B | IsInvariantForm ρ B ∧ B.IsAlt}
  zero_mem' := ⟨isInvariantForm_zero, LinearMap.BilinForm.isAlt_zero⟩
  add_mem' hB hC := ⟨hB.1.add hC.1, hB.2.add hC.2⟩
  smul_mem' c _ hB := ⟨hB.1.smul c, hB.2.smul c⟩

@[simp]
theorem mem_symmetricInvariantForms :
    B ∈ symmetricInvariantForms ρ ↔ IsInvariantForm ρ B ∧ B.IsSymm := Iff.rfl

@[simp]
theorem mem_alternatingInvariantForms :
    B ∈ alternatingInvariantForms ρ ↔ IsInvariantForm ρ B ∧ B.IsAlt := Iff.rfl

theorem symmetricInvariantForms_le (ρ : Representation k G V) :
    symmetricInvariantForms ρ ≤ invariantForms ρ :=
  fun _ hB => mem_invariantForms.mpr hB.1

theorem alternatingInvariantForms_le (ρ : Representation k G V) :
    alternatingInvariantForms ρ ≤ invariantForms ρ :=
  fun _ hB => mem_invariantForms.mpr hB.1

/-- Away from characteristic two, a form cannot be both symmetric and alternating, so the two
invariant subspaces meet only in `0`. -/
theorem symmetricInvariantForms_inf_alternatingInvariantForms (h2 : (2 : k) ≠ 0)
    (ρ : Representation k G V) :
    symmetricInvariantForms ρ ⊓ alternatingInvariantForms ρ = ⊥ := by
  refine le_antisymm (fun B hB => ?_) bot_le
  refine Submodule.mem_bot k |>.mpr (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
  have hsymm : B x y = B y x := hB.1.2.eq x y
  have halt : -B x y = B y x := hB.2.2.neg_eq x y
  have hzero : (2 : k) * B x y = 0 := by linear_combination hsymm - halt
  simpa using (mul_eq_zero.mp hzero).resolve_left h2

end Submodules

/-! ### Dimension helpers on a space of bilinear forms -/

section Helpers

/-
The three lemmas below are stated for an abstract module `W` and applied with `W` given
explicitly.  Leaving `W` to unification at those applications makes the elaborator look for an
`AddCommGroup` structure on a space of linear maps whose `AddCommMonoid` structure is already
fixed, which it does not find quickly.
-/

/-- A line spanned by a nonzero vector is one-dimensional. -/
private theorem finrank_span_singleton_eq_one {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] {w : W} (hw : w ≠ 0) : finrank K (Submodule.span K {w}) = 1 :=
  finrank_span_singleton hw

/-- A submodule containing a nonzero vector is at least one-dimensional. -/
private theorem one_le_finrank_of_mem {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {S : Submodule K W} {w : W} (hw : w ≠ 0) (hmem : w ∈ S) :
    1 ≤ finrank K S :=
  calc 1 = finrank K (Submodule.span K {w}) := (finrank_span_singleton_eq_one hw).symm
    _ ≤ finrank K S :=
        Submodule.finrank_mono (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hmem))

/-- Two submodules meeting only in `0` have dimensions adding to at most that of any submodule
containing them both. -/
private theorem finrank_add_finrank_le_of_inf_eq_bot {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W]
    {S T U : Submodule K W} (hS : S ≤ U) (hT : T ≤ U) (h : S ⊓ T = ⊥) :
    finrank K S + finrank K T ≤ finrank K U := by
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq S T
  rw [h, finrank_bot, add_zero] at hsup
  rw [← hsup]
  exact Submodule.finrank_mono (sup_le hS hT)

end Helpers

/-! ### Forms attached to functionals on the two squares -/

section Squares

variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- A functional on the second symmetric power of `V`, read as a bilinear form on `V`. -/
noncomputable def ofSymmetricSquareDual :
    Module.Dual k (Sym[k]^2V) →ₗ[k] BilinForm k V where
  toFun ψ :=
    MultilinearMap.toBilinForm
      (ψ.compMultilinearMap (SymmetricPower.tprod k (ι := Fin 2) (M := V)))
  map_add' ψ φ := by ext x y; simp
  map_smul' c ψ := by ext x y; simp

/-- A functional on the second exterior power of `V`, read as a bilinear form on `V`. -/
noncomputable def ofExteriorSquareDual :
    Module.Dual k (⋀[k]^2 V) →ₗ[k] BilinForm k V where
  toFun ψ :=
    MultilinearMap.toBilinForm
      (ψ.compMultilinearMap (exteriorPower.ιMulti k 2 (M := V)).toMultilinearMap)
  map_add' ψ φ := by ext x y; simp
  map_smul' c ψ := by ext x y; simp

@[simp]
theorem ofSymmetricSquareDual_apply (ψ : Module.Dual k (Sym[k]^2V)) (x y : V) :
    ofSymmetricSquareDual ψ x y = ψ (SymmetricPower.tprod k ![x, y]) := by
  simp [ofSymmetricSquareDual]

@[simp]
theorem ofExteriorSquareDual_apply (ψ : Module.Dual k (⋀[k]^2 V)) (x y : V) :
    ofExteriorSquareDual ψ x y = ψ (exteriorPower.ιMulti k 2 ![x, y]) := by
  simp [ofExteriorSquareDual]

/-- The form of a functional on the symmetric square is symmetric: the symmetric square does not
see the order of the two arguments. -/
theorem isSymm_ofSymmetricSquareDual (ψ : Module.Dual k (Sym[k]^2V)) :
    (ofSymmetricSquareDual ψ).IsSymm := by
  refine ⟨fun x y => ?_⟩
  have hswap : (fun i => ![x, y] (Equiv.swap 0 1 i)) = ![y, x] := by
    funext i; fin_cases i <;> simp
  simp only [ofSymmetricSquareDual_apply]
  rw [← SymmetricPower.tprod_equiv (Equiv.swap (0 : Fin 2) 1) ![x, y], hswap]

/-- The form of a functional on the exterior square is alternating: a repeated argument wedges
to zero. -/
theorem isAlt_ofExteriorSquareDual (ψ : Module.Dual k (⋀[k]^2 V)) :
    (ofExteriorSquareDual ψ).IsAlt := by
  intro x
  have hzero : exteriorPower.ιMulti k 2 ![x, x] = 0 :=
    (exteriorPower.ιMulti k 2).map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) (by simp) (by decide)
  simp [hzero]

theorem ofSymmetricSquareDual_injective :
    Function.Injective (ofSymmetricSquareDual (k := k) (V := V)) := by
  refine (injective_iff_map_eq_zero _).mpr fun ψ hψ => ?_
  refine LinearMap.ext_on (SymmetricPower.span_tprod_eq_top k (Fin 2) V) ?_
  rintro _ ⟨f, rfl⟩
  have hf : f = ![f 0, f 1] := by funext i; fin_cases i <;> simp
  have := congrArg (fun B : BilinForm k V => B (f 0) (f 1)) hψ
  simpa [hf.symm] using this

theorem ofExteriorSquareDual_injective :
    Function.Injective (ofExteriorSquareDual (k := k) (V := V)) := by
  refine (injective_iff_map_eq_zero _).mpr fun ψ hψ => ?_
  refine LinearMap.ext_on (exteriorPower.ιMulti_span k 2 V) ?_
  rintro _ ⟨f, rfl⟩
  have hf : f = ![f 0, f 1] := by funext i; fin_cases i <;> simp
  have := congrArg (fun B : BilinForm k V => B (f 0) (f 1)) hψ
  simpa [hf.symm] using this

/-- A functional invariant for the dual of a representation is unchanged by the action. -/
theorem apply_of_mem_invariants_dual {W : Type*} [AddCommGroup W] [Module k W]
    {σ : Representation k G W} {ψ : Module.Dual k W} (hψ : ψ ∈ σ.dual.invariants) (g : G)
    (u : W) : ψ (σ g u) = ψ u := by
  have h := DFunLike.congr_fun (hψ g⁻¹) u
  simpa [Representation.dual_apply, Module.Dual.transpose_apply] using h

variable (ρ : Representation k G V)

/-- An invariant functional on the symmetric square gives an invariant symmetric form. -/
theorem ofSymmetricSquareDual_mem_symmetricInvariantForms {ψ : Module.Dual k (Sym[k]^2V)}
    (hψ : ψ ∈ ((ρ.symmetricPower 2).dual).invariants) :
    ofSymmetricSquareDual ψ ∈ symmetricInvariantForms ρ := by
  refine ⟨isInvariantForm_iff.mpr fun g x y => ?_, isSymm_ofSymmetricSquareDual ψ⟩
  have hvec : (fun i => ρ g (![x, y] i)) = ![ρ g x, ρ g y] := by
    funext i; fin_cases i <;> simp
  simp only [ofSymmetricSquareDual_apply]
  rw [← hvec, ← ρ.symmetricPower_apply_tprod 2 g ![x, y],
    apply_of_mem_invariants_dual hψ g]

/-- An invariant functional on the exterior square gives an invariant alternating form. -/
theorem ofExteriorSquareDual_mem_alternatingInvariantForms {ψ : Module.Dual k (⋀[k]^2 V)}
    (hψ : ψ ∈ ((ρ.exteriorPower 2).dual).invariants) :
    ofExteriorSquareDual ψ ∈ alternatingInvariantForms ρ := by
  refine ⟨isInvariantForm_iff.mpr fun g x y => ?_, isAlt_ofExteriorSquareDual ψ⟩
  have hvec : (ρ g ∘ ![x, y]) = ![ρ g x, ρ g y] := by
    funext i; fin_cases i <;> simp
  simp only [ofExteriorSquareDual_apply]
  rw [← hvec, ← ρ.exteriorPower_apply_ιMulti 2 g ![x, y],
    apply_of_mem_invariants_dual hψ g]

end Squares

/-! ### Counting the invariant forms -/

section Counting

variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- **The invariant forms of `ρ` are the intertwiners from `ρ` to its dual.**  This is the bundled
form of `TauCeti.Representation.isInvariantForm_iff_isIntertwiningMap`, and it is what puts the
invariant forms in reach of the character machinery, which counts intertwiners. -/
noncomputable def invariantFormsEquivIntertwiningMapDual (ρ : Representation k G V) :
    invariantForms ρ ≃ₗ[k] Representation.IntertwiningMap ρ ρ.dual where
  toFun B := (B : BilinForm k V).intertwiningMap_of_isIntertwiningMap ρ ρ.dual
    ((isInvariantForm_iff_isIntertwiningMap ρ _).mp (mem_invariantForms.mp B.2)).isIntertwining
  invFun f := ⟨f.toLinearMap, mem_invariantForms.mpr
    ((isInvariantForm_iff_isIntertwiningMap ρ _).mpr ⟨f.isIntertwining⟩)⟩
  map_add' _ _ := Representation.IntertwiningMap.ext_iff.mpr rfl
  map_smul' _ _ := Representation.IntertwiningMap.ext_iff.mpr rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable [FiniteDimensional k V] [Finite G] [CharZero k]

/-- **The dual of a representation has as many invariants as the representation.** Both counts
average the same character, one along `g` and the other along `g⁻¹`. -/
theorem finrank_invariants_dual {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σ : Representation k G W) :
    finrank k σ.dual.invariants = finrank k σ.invariants := by
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hcast : (finrank k σ.dual.invariants : k) = (finrank k σ.invariants : k) := by
    rw [← Representation.card_inv_mul_sum_char_eq_finrank,
      ← Representation.card_inv_mul_sum_char_eq_finrank]
    refine congrArg _ ?_
    simp only [Representation.char_dual]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ fun _ => rfl
  exact_mod_cast hcast

/-- **The invariant forms are as many as the invariants of the two squares together.** Both counts
average `χ(g)²`, one of them along `g⁻¹`. -/
theorem finrank_invariantForms (ρ : Representation k G V) :
    finrank k (invariantForms ρ) =
      finrank k (ρ.symmetricPower 2).invariants + finrank k (ρ.exteriorPower 2).invariants := by
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hsum : ∀ g : G, ρ.character g * ρ.character g =
      (ρ.symmetricPower 2).character g + (ρ.exteriorPower 2).character g := fun g => by
    rw [← Representation.char_tensorSquare ρ g, sq]
  have hcast : (finrank k (invariantForms ρ) : k) =
      (finrank k (ρ.symmetricPower 2).invariants : k) +
        (finrank k (ρ.exteriorPower 2).invariants : k) := by
    rw [(invariantFormsEquivIntertwiningMapDual ρ).finrank_eq,
      ← Representation.card_inv_mul_sum_char_mul_char_eq_finrank,
      ← Representation.card_inv_mul_sum_char_eq_finrank,
      ← Representation.card_inv_mul_sum_char_eq_finrank, ← mul_add, ← Finset.sum_add_distrib]
    refine congrArg _ ?_
    simp only [Representation.char_dual, ← hsum]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ fun _ => rfl
  exact_mod_cast hcast

private theorem finrank_invariants_symmetricPower_le (ρ : Representation k G V) :
    finrank k (ρ.symmetricPower 2).invariants ≤ finrank k (symmetricInvariantForms ρ) := by
  have hmap : Submodule.map (ofSymmetricSquareDual (k := k) (V := V))
      ((ρ.symmetricPower 2).dual).invariants ≤ symmetricInvariantForms ρ := by
    rintro _ ⟨ψ, hψ, rfl⟩
    exact ofSymmetricSquareDual_mem_symmetricInvariantForms ρ hψ
  have hrank := (Submodule.equivMapOfInjective (ofSymmetricSquareDual (k := k) (V := V))
    ofSymmetricSquareDual_injective ((ρ.symmetricPower 2).dual).invariants).finrank_eq
  rw [← finrank_invariants_dual, hrank]
  exact Submodule.finrank_mono hmap

private theorem finrank_invariants_exteriorPower_le (ρ : Representation k G V) :
    finrank k (ρ.exteriorPower 2).invariants ≤ finrank k (alternatingInvariantForms ρ) := by
  have hmap : Submodule.map (ofExteriorSquareDual (k := k) (V := V))
      ((ρ.exteriorPower 2).dual).invariants ≤ alternatingInvariantForms ρ := by
    rintro _ ⟨ψ, hψ, rfl⟩
    exact ofExteriorSquareDual_mem_alternatingInvariantForms ρ hψ
  have hrank := (Submodule.equivMapOfInjective (ofExteriorSquareDual (k := k) (V := V))
    ofExteriorSquareDual_injective ((ρ.exteriorPower 2).dual).invariants).finrank_eq
  rw [← finrank_invariants_dual, hrank]
  exact Submodule.finrank_mono hmap

omit [Finite G] in
private theorem finrank_symmetricInvariantForms_add_le (ρ : Representation k G V) :
    finrank k (symmetricInvariantForms ρ) + finrank k (alternatingInvariantForms ρ)
      ≤ finrank k (invariantForms ρ) :=
  finrank_add_finrank_le_of_inf_eq_bot (K := k) (W := BilinForm k V) (symmetricInvariantForms_le ρ)
    (alternatingInvariantForms_le ρ)
    (symmetricInvariantForms_inf_alternatingInvariantForms (by norm_num) ρ)

/-- **The invariant symmetric forms are as many as the invariants of the symmetric square.** -/
theorem finrank_symmetricInvariantForms (ρ : Representation k G V) :
    finrank k (symmetricInvariantForms ρ) = finrank k (ρ.symmetricPower 2).invariants := by
  have h₁ := finrank_invariants_symmetricPower_le ρ
  have h₂ := finrank_invariants_exteriorPower_le ρ
  have h₃ := finrank_symmetricInvariantForms_add_le ρ
  have h₄ := finrank_invariantForms ρ
  omega

/-- **The invariant alternating forms are as many as the invariants of the exterior square.** -/
theorem finrank_alternatingInvariantForms (ρ : Representation k G V) :
    finrank k (alternatingInvariantForms ρ) = finrank k (ρ.exteriorPower 2).invariants := by
  have h₁ := finrank_invariants_symmetricPower_le ρ
  have h₂ := finrank_invariants_exteriorPower_le ρ
  have h₃ := finrank_symmetricInvariantForms_add_le ρ
  have h₄ := finrank_invariantForms ρ
  omega

/-- **The two invariant form counts add to the number of invariant forms.** -/
theorem finrank_symmetricInvariantForms_add_finrank_alternatingInvariantForms
    (ρ : Representation k G V) :
    finrank k (symmetricInvariantForms ρ) + finrank k (alternatingInvariantForms ρ) =
      finrank k (invariantForms ρ) := by
  rw [finrank_symmetricInvariantForms, finrank_alternatingInvariantForms, finrank_invariantForms]

end Counting

/-! ### The indicator as a signed count of invariant forms -/

section Indicator

variable [Field k] [CharZero k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- **The Frobenius-Schur indicator is the signed count of invariant bilinear forms**,
`ν₂(ρ) = dim {invariant symmetric forms} - dim {invariant alternating forms}`. -/
theorem frobeniusSchurIndicator_eq_sub_finrank_invariantForms (ρ : Representation k G V) :
    frobeniusSchurIndicator ρ = (finrank k (symmetricInvariantForms ρ) : k) -
      (finrank k (alternatingInvariantForms ρ) : k) := by
  have : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariants, finrank_symmetricInvariantForms,
    finrank_alternatingInvariantForms]

end Indicator

/-! ### The trichotomy -/

section Trichotomy

variable [Field k] [CharZero k] [IsAlgClosed k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible] {B : BilinForm k V}

omit [IsAlgClosed k] [ρ.IsIrreducible] in
/-- **The complex case.** A representation with no nonzero invariant form has Frobenius-Schur
indicator `0`. -/
theorem frobeniusSchurIndicator_eq_zero_of_invariantForms_eq_bot (h : invariantForms ρ = ⊥) :
    frobeniusSchurIndicator ρ = 0 := by
  have hs : symmetricInvariantForms ρ = ⊥ :=
    le_bot_iff.mp (le_of_le_of_eq (symmetricInvariantForms_le ρ) h)
  have ha : alternatingInvariantForms ρ = ⊥ :=
    le_bot_iff.mp (le_of_le_of_eq (alternatingInvariantForms_le ρ) h)
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariantForms, hs, ha]
  simp

/-- **The orthogonal case.** An irreducible representation carrying a nonzero invariant symmetric
form has Frobenius-Schur indicator `1`.  Such a form is automatically nondegenerate, by
`TauCeti.Representation.IsInvariantForm.nondegenerate`. -/
theorem frobeniusSchurIndicator_eq_one_of_isSymm (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0)
    (hsymm : B.IsSymm) : frobeniusSchurIndicator ρ = 1 := by
  have hone : finrank k (invariantForms ρ) = 1 := by
    rw [hB.invariantForms_eq_span hB0]
    exact finrank_span_singleton_eq_one (K := k) (W := BilinForm k V) hB0
  have hle : 1 ≤ finrank k (symmetricInvariantForms ρ) :=
    one_le_finrank_of_mem (K := k) (W := BilinForm k V) hB0 ⟨hB, hsymm⟩
  have hadd := finrank_symmetricInvariantForms_add_finrank_alternatingInvariantForms ρ
  have hs : finrank k (symmetricInvariantForms ρ) = 1 := by omega
  have ha : finrank k (alternatingInvariantForms ρ) = 0 := by omega
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariantForms, hs, ha]
  simp

/-- **The symplectic case.** An irreducible representation carrying a nonzero invariant alternating
form has Frobenius-Schur indicator `-1`.  Such a form is automatically nondegenerate, by
`TauCeti.Representation.IsInvariantForm.nondegenerate`. -/
theorem frobeniusSchurIndicator_eq_neg_one_of_isAlt (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0)
    (halt : B.IsAlt) : frobeniusSchurIndicator ρ = -1 := by
  have hone : finrank k (invariantForms ρ) = 1 := by
    rw [hB.invariantForms_eq_span hB0]
    exact finrank_span_singleton_eq_one (K := k) (W := BilinForm k V) hB0
  have hle : 1 ≤ finrank k (alternatingInvariantForms ρ) :=
    one_le_finrank_of_mem (K := k) (W := BilinForm k V) hB0 ⟨hB, halt⟩
  have hadd := finrank_symmetricInvariantForms_add_finrank_alternatingInvariantForms ρ
  have hs : finrank k (symmetricInvariantForms ρ) = 0 := by omega
  have ha : finrank k (alternatingInvariantForms ρ) = 1 := by omega
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariantForms, hs, ha]
  simp

/-- **The Frobenius-Schur trichotomy.** The indicator of an irreducible representation over an
algebraically closed field of characteristic zero takes only the values `1`, `0` and `-1`. -/
theorem frobeniusSchurIndicator_eq_one_or_eq_zero_or_eq_neg_one :
    frobeniusSchurIndicator ρ = 1 ∨ frobeniusSchurIndicator ρ = 0 ∨
      frobeniusSchurIndicator ρ = -1 := by
  by_cases hbot : invariantForms ρ = ⊥
  · exact Or.inr (Or.inl (frobeniusSchurIndicator_eq_zero_of_invariantForms_eq_bot ρ hbot))
  · obtain ⟨C, hCmem, hC0⟩ := (Submodule.ne_bot_iff _).mp hbot
    have hC : IsInvariantForm ρ C := mem_invariantForms.mp hCmem
    rcases hC.isSymm_or_isAlt (by norm_num) hC0 with hsymm | halt
    · exact Or.inl (frobeniusSchurIndicator_eq_one_of_isSymm ρ hC hC0 hsymm)
    · exact Or.inr (Or.inr (frobeniusSchurIndicator_eq_neg_one_of_isAlt ρ hC hC0 halt))

/-- **The indicator is `1` exactly in the orthogonal case.** -/
theorem frobeniusSchurIndicator_eq_one_iff :
    frobeniusSchurIndicator ρ = 1 ↔
      ∃ B : BilinForm k V, IsInvariantForm ρ B ∧ B ≠ 0 ∧ B.IsSymm := by
  refine ⟨fun h => ?_, fun ⟨_, hB, hB0, hsymm⟩ =>
    frobeniusSchurIndicator_eq_one_of_isSymm ρ hB hB0 hsymm⟩
  by_cases hbot : invariantForms ρ = ⊥
  · rw [frobeniusSchurIndicator_eq_zero_of_invariantForms_eq_bot ρ hbot] at h
    exact absurd h.symm one_ne_zero
  · obtain ⟨C, hCmem, hC0⟩ := (Submodule.ne_bot_iff _).mp hbot
    have hC : IsInvariantForm ρ C := mem_invariantForms.mp hCmem
    rcases hC.isSymm_or_isAlt (by norm_num) hC0 with hsymm | halt
    · exact ⟨C, hC, hC0, hsymm⟩
    · rw [frobeniusSchurIndicator_eq_neg_one_of_isAlt ρ hC hC0 halt] at h
      exact absurd h (by norm_num)

/-- **The indicator is `-1` exactly in the symplectic case.** -/
theorem frobeniusSchurIndicator_eq_neg_one_iff :
    frobeniusSchurIndicator ρ = -1 ↔
      ∃ B : BilinForm k V, IsInvariantForm ρ B ∧ B ≠ 0 ∧ B.IsAlt := by
  refine ⟨fun h => ?_, fun ⟨_, hB, hB0, halt⟩ =>
    frobeniusSchurIndicator_eq_neg_one_of_isAlt ρ hB hB0 halt⟩
  by_cases hbot : invariantForms ρ = ⊥
  · rw [frobeniusSchurIndicator_eq_zero_of_invariantForms_eq_bot ρ hbot] at h
    exact absurd h (by norm_num)
  · obtain ⟨C, hCmem, hC0⟩ := (Submodule.ne_bot_iff _).mp hbot
    have hC : IsInvariantForm ρ C := mem_invariantForms.mp hCmem
    rcases hC.isSymm_or_isAlt (by norm_num) hC0 with hsymm | halt
    · rw [frobeniusSchurIndicator_eq_one_of_isSymm ρ hC hC0 hsymm] at h
      exact absurd h (by norm_num)
    · exact ⟨C, hC, hC0, halt⟩

/-- **The indicator is `0` exactly in the complex case**, that is, exactly when the representation
carries no nonzero invariant bilinear form at all. -/
theorem frobeniusSchurIndicator_eq_zero_iff :
    frobeniusSchurIndicator ρ = 0 ↔ invariantForms ρ = ⊥ := by
  refine ⟨fun h => ?_, frobeniusSchurIndicator_eq_zero_of_invariantForms_eq_bot ρ⟩
  by_contra hbot
  obtain ⟨C, hCmem, hC0⟩ := (Submodule.ne_bot_iff _).mp hbot
  have hC : IsInvariantForm ρ C := mem_invariantForms.mp hCmem
  rcases hC.isSymm_or_isAlt (by norm_num) hC0 with hsymm | halt
  · rw [frobeniusSchurIndicator_eq_one_of_isSymm ρ hC hC0 hsymm] at h
    exact absurd h one_ne_zero
  · rw [frobeniusSchurIndicator_eq_neg_one_of_isAlt ρ hC hC0 halt] at h
    exact absurd h (by norm_num)

end Trichotomy

end Representation

end TauCeti
