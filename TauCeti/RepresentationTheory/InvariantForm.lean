/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Invariant bilinear forms on a representation

A bilinear form `B` on the space of a representation `ρ` of `G` is **invariant** when every `ρ g`
preserves it, `B (ρ g x) (ρ g y) = B x y`.  The invariant forms are a submodule of all bilinear
forms, and read as maps `V → V*` they are exactly the intertwiners from `ρ` to its dual
representation -- the concrete form of the statement that they are the `G`-invariants of a space
of bilinear forms.

On an **irreducible** representation the invariant forms are tightly constrained, and the three
constraints proved here are the ones the Frobenius-Schur trichotomy is read off from.  First, the
left radical of an invariant form is a subrepresentation, so a nonzero invariant form on an
irreducible representation is nondegenerate.  Second, over an algebraically closed field and in
finite dimensions, Schur's lemma makes a nonzero invariant form unique up to a scalar: the
invariant forms are the line it spans.  Third -- and this is the point -- the flip of an invariant
form is invariant, so a nonzero invariant form is a scalar multiple of its own flip; flipping twice
squares the scalar to `1`, and the form is therefore either symmetric or the negative of its flip.
Away from characteristic two the second alternative is exactly alternation, which gives the
orthogonal/symplectic dichotomy: an irreducible representation carries at most a line of invariant
forms, and any nonzero one on it is either symmetric or alternating.

Nothing here needs a finite group, and the first two sections need neither a field nor finite
dimensions: invariance is defined for a representation of a monoid on a module over a commutative
semiring, and only the results that invoke Schur's lemma ask for an algebraically closed field and
a finite-dimensional space.  The `g⁻¹` in `TauCeti.Representation.IsInvariantForm.apply_left`, and
with it everything downstream of it, is what makes `G` a group from that point on.

## Main definitions

* `TauCeti.Representation.IsInvariantForm`: `B (ρ g x) (ρ g y) = B x y` for all `g`, `x`, `y`.
* `TauCeti.Representation.invariantForms`: the invariant forms, as a submodule of `BilinForm k V`.

## Main results

* `TauCeti.Representation.isInvariantForm_iff_isIntertwiningMap`: a form is invariant exactly when
  it intertwines `ρ` with `ρ.dual`.
* `TauCeti.Representation.IsInvariantForm.nondegenerate`: a nonzero invariant form on an
  irreducible representation is nondegenerate.
* `TauCeti.Representation.exists_eq_smul_id_of_comm`: **Schur's lemma, scalar form**, for an
  abstract representation.
* `TauCeti.Representation.IsInvariantForm.invariantForms_eq_span`: over an algebraically closed
  field and in finite dimensions, a nonzero invariant form on an irreducible representation spans
  all of them.
* `TauCeti.Representation.IsInvariantForm.flip_eq_or_flip_eq_neg` and
  `TauCeti.Representation.IsInvariantForm.isSymm_or_isAlt`: such a form is symmetric or
  alternating.

## Implementation notes

`TauCeti.Representation.IsInvariantForm` is `@[expose]`d, because it is a plain `∀`-statement with
no useful content of its own: the intended way to prove it is `intro g x y`, and the intended way
to use it is to apply it, both of which need the unfolding.  What the file adds around it is the
two rewritings that are *not* immediate -- moving a single `ρ g` across the form at the cost of an
inverse (`TauCeti.Representation.IsInvariantForm.apply_left`), and the identification with
intertwiners into the dual.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 7, `IsInvariantForm` and the invariant symmetric and alternating forms that the values
  `+1` and `-1` of the Frobenius-Schur indicator are characterized by.  The indicator itself is
  `TauCeti.Representation.frobeniusSchurIndicator`; this file supplies the forms, not the count.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 4.
-/

public section

namespace TauCeti

open LinearMap (BilinForm)

namespace Representation

/-! ### The invariant forms of a representation -/

section Monoid

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- A bilinear form `B` is **invariant** for a representation `ρ` when every `ρ g` preserves it:
`B (ρ g x) (ρ g y) = B x y`. -/
@[expose]
def IsInvariantForm (ρ : Representation k G V) (B : BilinForm k V) : Prop :=
  ∀ (g : G) (x y : V), B (ρ g x) (ρ g y) = B x y

variable {ρ : Representation k G V} {B C : BilinForm k V}

/-- The invariant bilinear forms of `ρ`, as a submodule of all bilinear forms on `V`. -/
def invariantForms (ρ : Representation k G V) : Submodule k (BilinForm k V) where
  carrier := {B | IsInvariantForm ρ B}
  add_mem' hB hC g x y := by simp only [LinearMap.add_apply, hB g x y, hC g x y]
  zero_mem' _ _ _ := rfl
  smul_mem' c _ hB g x y := by simp only [LinearMap.smul_apply, hB g x y]

/-- Membership in `TauCeti.Representation.invariantForms` is invariance. -/
@[simp]
theorem mem_invariantForms : B ∈ invariantForms ρ ↔ IsInvariantForm ρ B := Iff.rfl

/-- The zero form is invariant. -/
@[simp]
theorem isInvariantForm_zero : IsInvariantForm ρ (0 : BilinForm k V) := fun _ _ _ => rfl

/-- A sum of invariant forms is invariant. -/
theorem IsInvariantForm.add (hB : IsInvariantForm ρ B) (hC : IsInvariantForm ρ C) :
    IsInvariantForm ρ (B + C) :=
  (invariantForms ρ).add_mem hB hC

/-- A scalar multiple of an invariant form is invariant. -/
theorem IsInvariantForm.smul (c : k) (hB : IsInvariantForm ρ B) : IsInvariantForm ρ (c • B) :=
  (invariantForms ρ).smul_mem c hB

/-- Exchanging the two arguments of an invariant form leaves it invariant. -/
theorem IsInvariantForm.flip (hB : IsInvariantForm ρ B) : IsInvariantForm ρ B.flip :=
  fun g x y => hB g y x

/-- Every bilinear form is invariant for the trivial representation, which acts by the identity. -/
theorem isInvariantForm_trivial (B : BilinForm k V) :
    IsInvariantForm (Representation.trivial k G V) B :=
  fun _ _ _ => rfl

end Monoid

/-! ### Invariance as intertwining with the dual representation -/

section Group

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
variable {ρ : Representation k G V} {B : BilinForm k V}

/-- Moving a single `ρ g` across an invariant form replaces it by its inverse on the other side.
This is the shape invariance is used in whenever only one of the two arguments carries the action,
as in the radical of the form or in a comparison with the dual representation. -/
theorem IsInvariantForm.apply_left (hB : IsInvariantForm ρ B) (g : G) (x y : V) :
    B (ρ g x) y = B x (ρ g⁻¹ y) := by
  conv_lhs => rw [← Representation.self_inv_apply ρ g y]
  exact hB g x (ρ g⁻¹ y)

/-- **A bilinear form is invariant exactly when it intertwines `ρ` with its dual.** Read as a
linear map `V → V*`, an invariant form is a map of representations from `ρ` to `ρ.dual`, and
conversely.  This is what makes the invariant forms a `Hom` space rather than just a submodule,
and it is how Schur's lemma reaches them. -/
theorem isInvariantForm_iff_isIntertwiningMap (ρ : Representation k G V) (B : BilinForm k V) :
    IsInvariantForm ρ B ↔ Representation.IsIntertwiningMap ρ ρ.dual B := by
  constructor
  · refine fun hB => ⟨fun g v => ?_⟩
    ext w
    simpa [Module.Dual.transpose_apply] using hB.apply_left g v w
  · intro hB g x y
    have h := DFunLike.congr_fun (hB.isIntertwining g x) (ρ g y)
    simpa [Module.Dual.transpose_apply] using h

end Group

/-! ### Invariant forms on an irreducible representation -/

section Irreducible

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable {ρ : Representation k G V} {B C : BilinForm k V}

/-- The left radical of an invariant form is a subrepresentation: if `B v` vanishes then so does
`B (ρ g v)`, because `B (ρ g v) w = B v (ρ g⁻¹ w)`. -/
def IsInvariantForm.radical (hB : IsInvariantForm ρ B) : Subrepresentation ρ where
  toSubmodule := LinearMap.ker B
  apply_mem_toSubmodule g v hv := by
    rw [LinearMap.mem_ker] at hv ⊢
    ext w
    rw [hB.apply_left g v w, hv]
    simp

/-- The radical of an invariant form carries the kernel of the form. -/
@[simp]
theorem IsInvariantForm.toSubmodule_radical (hB : IsInvariantForm ρ B) :
    hB.radical.toSubmodule = LinearMap.ker B :=
  (rfl)

/-- On an irreducible representation the radical of an invariant form is trivial unless the form
is: the radical is a subrepresentation, hence zero or everything, and it is everything exactly for
the zero form. -/
theorem IsInvariantForm.ker_eq_bot [ρ.IsIrreducible] (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0) :
    LinearMap.ker B = ⊥ := by
  rcases IsSimpleOrder.eq_bot_or_eq_top hB.radical with h | h
  · rw [← hB.toSubmodule_radical, h, Subrepresentation.toSubmodule_bot]
  · exact absurd (LinearMap.ker_eq_top.mp
      (by rw [← hB.toSubmodule_radical, h, Subrepresentation.toSubmodule_top])) hB0

/-- **A nonzero invariant form on an irreducible representation is nondegenerate.** Both radicals
are handled at once, the right one by applying the left statement to the flipped form. -/
theorem IsInvariantForm.nondegenerate [ρ.IsIrreducible] (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0) :
    B.Nondegenerate := by
  refine ⟨LinearMap.separatingLeft_iff_ker_eq_bot.mpr (hB.ker_eq_bot hB0),
    LinearMap.flip_separatingLeft.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mpr ?_)⟩
  exact hB.flip.ker_eq_bot fun h => hB0 (LinearMap.BilinForm.flipHom.map_eq_zero_iff.mp h)

/-- **Schur's lemma, scalar form.** An endomorphism of a finite-dimensional irreducible
representation over an algebraically closed field that commutes with the action is a scalar
multiple of the identity.

This is the statement for an abstract representation; the counterpart for a continuous
representation of a topological group is
`TauCeti.ContRepresentation.exists_eq_smul_one_of_irreducible`, and both rest on Mathlib's
`Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`. -/
theorem exists_eq_smul_id_of_comm [FiniteDimensional k V] [IsAlgClosed k]
    {ρ : Representation k G V} [ρ.IsIrreducible] {φ : V →ₗ[k] V}
    (hφ : ∀ (g : G) (v : V), φ (ρ g v) = ρ g (φ v)) :
    ∃ c : k, φ = c • LinearMap.id := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 (φ.intertwiningMap_of_isIntertwiningMap ρ ρ hφ)
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  simpa using (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hc).symm

variable [FiniteDimensional k V] [IsAlgClosed k] [ρ.IsIrreducible]

/-- **An invariant form on an irreducible representation is unique up to a scalar.** Comparing `C`
with a nonzero `B` through the isomorphism `V ≃ V*` that the nondegenerate `B` provides produces an
endomorphism commuting with the action, hence a scalar. -/
theorem IsInvariantForm.exists_eq_smul (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0)
    (hC : IsInvariantForm ρ C) : ∃ c : k, C = c • B := by
  have hBnd : B.Nondegenerate := hB.nondegenerate hB0
  -- `φ` reads `C` through the isomorphism `V ≃ V*` that the nondegenerate `B` provides.
  set φ : V →ₗ[k] V := (B.toDual hBnd).symm.toLinearMap ∘ₗ C with hφdef
  have hφB : ∀ v w : V, B (φ v) w = C v w := by
    intro v w
    rw [hφdef]
    simp
  have hφ : ∀ (g : G) (v : V), φ (ρ g v) = ρ g (φ v) := by
    intro g v
    refine sub_eq_zero.mp (hBnd.1 _ fun w => ?_)
    rw [map_sub, LinearMap.sub_apply, hφB, hB.apply_left, hφB, hC.apply_left, sub_self]
  obtain ⟨c, hc⟩ := exists_eq_smul_id_of_comm (ρ := ρ) hφ
  refine ⟨c, LinearMap.ext fun v => LinearMap.ext fun w => ?_⟩
  have h := hφB v w
  rw [hc] at h
  simpa using h.symm

/-- **A nonzero invariant form on an irreducible representation spans all of them**: the invariant
forms are a line. -/
theorem IsInvariantForm.invariantForms_eq_span (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0) :
    invariantForms ρ = Submodule.span k {B} := by
  refine le_antisymm (fun C hC => ?_) (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hB))
  obtain ⟨c, rfl⟩ := hB.exists_eq_smul hB0 hC
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self B)

/-- **A nonzero invariant form on an irreducible representation is its own flip up to sign.** The
flip is invariant too, so it is a scalar multiple `c • B` of the form; reading that off twice
multiplies each value of `B` by `c * c`, which is therefore `1`. -/
theorem IsInvariantForm.flip_eq_or_flip_eq_neg (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0) :
    B.flip = B ∨ B.flip = -B := by
  obtain ⟨c, hc⟩ := hB.exists_eq_smul hB0 hB.flip
  have hpt : ∀ x y : V, B y x = c * B x y := by
    intro x y
    simpa using DFunLike.congr_fun (DFunLike.congr_fun hc x) y
  have hsq : c * c = 1 := by
    by_contra hne
    refine hB0 (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    have h1 : B x y = c * c * B x y := by
      conv_lhs => rw [hpt y x, hpt x y]
      ring
    have h2 : (1 - c * c) * B x y = 0 := by linear_combination h1
    simpa using (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  rcases mul_self_eq_one_iff.mp hsq with rfl | rfl
  · exact Or.inl (by rw [hc, one_smul])
  · exact Or.inr (by rw [hc]; module)

/-- **The orthogonal/symplectic dichotomy.** Away from characteristic two, a nonzero invariant form
on a finite-dimensional irreducible representation over an algebraically closed field is either
symmetric or alternating. -/
theorem IsInvariantForm.isSymm_or_isAlt (h2 : (2 : k) ≠ 0) (hB : IsInvariantForm ρ B)
    (hB0 : B ≠ 0) : B.IsSymm ∨ B.IsAlt := by
  rcases hB.flip_eq_or_flip_eq_neg hB0 with h | h
  · exact Or.inl (LinearMap.BilinForm.isSymm_iff_flip.mpr h)
  · refine Or.inr fun x => ?_
    have hx : B x x = -B x x := by
      have := DFunLike.congr_fun (DFunLike.congr_fun h x) x
      simpa using this
    have : (2 : k) * B x x = 0 := by linear_combination hx
    exact (mul_eq_zero.mp this).resolve_left h2

end Irreducible

end Representation

end TauCeti
