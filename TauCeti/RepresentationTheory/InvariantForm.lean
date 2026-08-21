/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible
public import TauCeti.LinearAlgebra.BilinearForm.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic

/-!
# Invariant bilinear forms on a representation

A bilinear form `B` on the space of a representation `ρ` of `G` is **invariant** when every `ρ g`
preserves it, `B (ρ g x) (ρ g y) = B x y`.  The invariant forms are a submodule of all bilinear
forms, and read as maps `V → V*` they are exactly the intertwiners from `ρ` to its dual
representation -- the concrete form of the statement that they are the `G`-invariants of a space
of bilinear forms.  Cutting the invariant forms down by symmetry, respectively by alternation,
gives two further submodules, and away from characteristic two they meet only in `0`.

On an **irreducible** representation the invariant forms are tightly constrained, and the three
constraints proved here are the ones the Frobenius-Schur trichotomy is read off from.  First, the
left radical of an invariant form is the kernel of an intertwiner out of an irreducible
representation, so a nonzero invariant form on one is nondegenerate.  Second, over an
algebraically closed field and in finite dimensions, Schur's lemma makes a nonzero invariant form
unique up to a scalar: the invariant forms are the line it spans.  Third -- and this is the
point -- the flip of an invariant form is invariant, so a nonzero invariant form is a scalar
multiple of its own flip; flipping twice squares the scalar to `1`, and the form is therefore
either symmetric or the negative of its flip.
Away from characteristic two the second alternative is exactly alternation, which gives the
orthogonal/symplectic dichotomy: an irreducible representation carries at most a line of invariant
forms, and -- in characteristic other than two -- any nonzero one on it is either symmetric or
alternating.

Nothing here needs a finite group, and almost nothing needs finite dimensions: invariance, and the
symmetric and alternating invariant forms with it, are defined for a representation of a monoid on
a module over a commutative semiring, and only the results that invoke Schur's lemma ask for an
algebraically closed field and a finite-dimensional space.  The `g⁻¹` in
`TauCeti.Representation.IsInvariantForm.apply_left`, and with it the comparison with the dual
representation, is what makes `G` a group.

## Main definitions

* `TauCeti.Representation.IsInvariantForm`: `B (ρ g x) (ρ g y) = B x y` for all `g`, `x`, `y`.
* `TauCeti.Representation.invariantForms`: the invariant forms, as a submodule of `BilinForm k V`.
* `TauCeti.Representation.symmetricInvariantForms` and
  `TauCeti.Representation.alternatingInvariantForms`: the invariant forms that are symmetric,
  respectively alternating.
* `TauCeti.Representation.invariantFormsEquivIntertwiningMapDual`: the invariant forms of `ρ` as
  the intertwiners from `ρ` to its dual.

## Main results

* `TauCeti.Representation.isInvariantForm_iff_isIntertwiningMap`: a form is invariant exactly when
  it intertwines `ρ` with `ρ.dual`.
* `TauCeti.Representation.invariantForms_eq_invariants_linHom_dual`: the invariant forms are the
  invariants of `linHom ρ ρ.dual`.
* `TauCeti.Representation.symmetricInvariantForms_inf_alternatingInvariantForms`: away from
  characteristic two the symmetric and the alternating invariant forms meet only in `0`.
* `TauCeti.Representation.IsInvariantForm.nondegenerate` and
  `TauCeti.Representation.IsInvariantForm.nondegenerate_iff_ne_zero`: an invariant form on an
  irreducible representation is nondegenerate exactly when it is nonzero.
* `TauCeti.Representation.IsInvariantForm.exists_eq_smul`: over an algebraically closed field and
  in finite dimensions, an invariant form on an irreducible representation is a scalar multiple of
  any nonzero one.
* `TauCeti.Representation.IsInvariantForm.invariantForms_eq_span`: over an algebraically closed
  field and in finite dimensions, a nonzero invariant form on an irreducible representation spans
  all of them.
* `TauCeti.Representation.IsInvariantForm.flip_eq_or_flip_eq_neg`: in every characteristic, the
  flip of such a form is the form itself or its negative.
* `TauCeti.Representation.IsInvariantForm.isSymm_or_isAlt`: away from characteristic two -- the
  hypothesis `(2 : k) ≠ 0` -- such a form is symmetric or alternating.

## Implementation notes

`TauCeti.Representation.IsInvariantForm` is the statement that every `ρ g` is an isometry of the
form, `TauCeti.BilinForm.IsIsometry B (ρ g)`, so that the invariant forms of a representation and
the isometry group of a form are the same notion read two ways.  Its body is not exposed:
`TauCeti.Representation.isInvariantForm_iff_isIsometry` and
`TauCeti.Representation.isInvariantForm_iff` introduce its isometry and pointwise forms, while
`TauCeti.Representation.IsInvariantForm.isIsometry` and
`TauCeti.Representation.IsInvariantForm.apply` eliminate them, so nothing outside this file has to
unfold the definition.  The pointwise `iff` is deliberately not a `simp` lemma: unfolding
invariance into its quantified equation would take
`TauCeti.Representation.isInvariantForm_zero` and
`TauCeti.Representation.mem_invariantForms` out of simp-normal form, which the `simpNF` linter
rejects.  What the file adds around that pair is the two rewritings that are *not*
immediate -- moving a single `ρ g` across the form at the cost of an inverse
(`TauCeti.Representation.IsInvariantForm.apply_left`), and the identification with intertwiners
into the dual.  That identification is recorded twice: once unbundled as
`TauCeti.Representation.isInvariantForm_iff_isIntertwiningMap`, which is the shape the proofs
below use, and once as the linear equivalence
`TauCeti.Representation.invariantFormsEquivIntertwiningMapDual`, which is the shape a dimension
count of the invariant forms needs.  The equivalence is not built by hand: the invariant forms are
literally the invariants of `linHom ρ ρ.dual`
(`TauCeti.Representation.invariantForms_eq_invariants_linHom_dual`), so it is Mathlib's
`Representation.invariantsEquivIntertwiningMap` transported along that equality.  Mathlib's
`Representation.invariants` asks for a commutative ring and an additive group, which is why the two
declarations sit in a narrower section than the rest of the file; the additive group on the space
of maps `V → V*` is supplied explicitly, because a representation records only the additive monoid
and the elaborator does not solve for a group structure inducing a given one.  The equivalence is
not exposed,
so a downstream module uses it opaquely -- a dimension count goes through `LinearEquiv.finrank_eq`
and never looks at a value.  When a value is needed, the two `simp` lemmas
`TauCeti.Representation.invariantFormsEquivIntertwiningMapDual_apply_toLinearMap` and
`TauCeti.Representation.invariantFormsEquivIntertwiningMapDual_symm_apply_coe` are what identify
it: they say the equivalence moves a form and an intertwiner to each other unchanged.

That identification is also what controls the left radical: the form is an intertwiner out of an
irreducible representation, so `TauCeti.Representation.IsInvariantForm.ker_eq_bot` is Mathlib's
`Representation.IsIrreducible.injective_or_eq_zero` rather than a hand-built subrepresentation
argument.  Schur's lemma enters through Mathlib's
`Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`, the same
theorem that `TauCeti.ContRepresentation.exists_eq_smul_one_of_irreducible` rests on for a
continuous representation.

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
`B (ρ g x) (ρ g y) = B x y`; that is, when every `ρ g` is an isometry of `B`. -/
def IsInvariantForm (ρ : Representation k G V) (B : BilinForm k V) : Prop :=
  ∀ g : G, BilinForm.IsIsometry B (ρ g)

variable {ρ : Representation k G V} {B C : BilinForm k V}

/-- A form is invariant for `ρ` exactly when every `ρ g` is an isometry of the form. -/
theorem isInvariantForm_iff_isIsometry :
    IsInvariantForm ρ B ↔ ∀ g : G, BilinForm.IsIsometry B (ρ g) := Iff.rfl

/-- Every element of a representation is an isometry of an invariant form. -/
theorem IsInvariantForm.isIsometry (hB : IsInvariantForm ρ B) (g : G) :
    BilinForm.IsIsometry B (ρ g) :=
  isInvariantForm_iff_isIsometry.mp hB g

/-- A form is invariant for `ρ` exactly when it satisfies the pointwise equation
`B (ρ g x) (ρ g y) = B x y`. -/
theorem isInvariantForm_iff :
    IsInvariantForm ρ B ↔ ∀ (g : G) (x y : V), B (ρ g x) (ρ g y) = B x y :=
  ⟨fun h g => BilinForm.isIsometry_iff.mp (h g),
    fun h g => BilinForm.isIsometry_iff.mpr (h g)⟩

/-- An invariant form takes the same value on `ρ g x` and `ρ g y` as it does on `x` and `y`. -/
@[grind =]
theorem IsInvariantForm.apply (hB : IsInvariantForm ρ B) (g : G) (x y : V) :
    B (ρ g x) (ρ g y) = B x y := (hB g).apply x y

/-- The invariant bilinear forms of `ρ`, as a submodule of all bilinear forms on `V`. -/
def invariantForms (ρ : Representation k G V) : Submodule k (BilinForm k V) where
  carrier := {B | IsInvariantForm ρ B}
  add_mem' hB hC g := BilinForm.isIsometry_iff.mpr fun x y => by
    simp only [LinearMap.add_apply, hB.apply g x y, hC.apply g x y]
  zero_mem' _ := BilinForm.isIsometry_iff.mpr fun _ _ => rfl
  smul_mem' c _ hB g := BilinForm.isIsometry_iff.mpr fun x y => by
    simp only [LinearMap.smul_apply, hB.apply g x y]

/-- Membership in `TauCeti.Representation.invariantForms` is invariance. -/
@[simp]
theorem mem_invariantForms : B ∈ invariantForms ρ ↔ IsInvariantForm ρ B := Iff.rfl

/-- The zero form is invariant. -/
@[simp]
theorem isInvariantForm_zero : IsInvariantForm ρ (0 : BilinForm k V) :=
  fun _ => BilinForm.isIsometry_iff.mpr fun _ _ => rfl

/-- A sum of invariant forms is invariant. -/
theorem IsInvariantForm.add (hB : IsInvariantForm ρ B) (hC : IsInvariantForm ρ C) :
    IsInvariantForm ρ (B + C) :=
  (invariantForms ρ).add_mem hB hC

/-- A scalar multiple of an invariant form is invariant. -/
theorem IsInvariantForm.smul (c : k) (hB : IsInvariantForm ρ B) : IsInvariantForm ρ (c • B) :=
  (invariantForms ρ).smul_mem c hB

/-- Exchanging the two arguments of an invariant form leaves it invariant. -/
theorem IsInvariantForm.flip (hB : IsInvariantForm ρ B) : IsInvariantForm ρ B.flip :=
  fun g => BilinForm.isIsometry_iff.mpr fun x y => hB.apply g y x

/-- Every bilinear form is invariant for the trivial representation, which acts by the identity. -/
@[simp]
theorem isInvariantForm_trivial (B : BilinForm k V) :
    IsInvariantForm (Representation.trivial k G V) B :=
  fun _ => BilinForm.isIsometry_iff.mpr fun _ _ => rfl

end Monoid

/-! ### The symmetric and the alternating invariant forms -/

section SymmetricAlternating

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
variable {ρ : Representation k G V} {B : BilinForm k V}

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

/-- Membership in `TauCeti.Representation.symmetricInvariantForms` is invariance together with
symmetry. -/
@[simp]
theorem mem_symmetricInvariantForms :
    B ∈ symmetricInvariantForms ρ ↔ IsInvariantForm ρ B ∧ B.IsSymm := Iff.rfl

/-- Membership in `TauCeti.Representation.alternatingInvariantForms` is invariance together with
alternation. -/
@[simp]
theorem mem_alternatingInvariantForms :
    B ∈ alternatingInvariantForms ρ ↔ IsInvariantForm ρ B ∧ B.IsAlt := Iff.rfl

/-- An invariant symmetric form is in particular invariant. -/
theorem symmetricInvariantForms_le (ρ : Representation k G V) :
    symmetricInvariantForms ρ ≤ invariantForms ρ :=
  fun _ hB => mem_invariantForms.mpr hB.1

/-- An invariant alternating form is in particular invariant. -/
theorem alternatingInvariantForms_le (ρ : Representation k G V) :
    alternatingInvariantForms ρ ≤ invariantForms ρ :=
  fun _ hB => mem_invariantForms.mpr hB.1

end SymmetricAlternating

section SymmetricAlternatingRing

variable {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]

/-- Away from characteristic two, a form cannot be both symmetric and alternating, so the two
invariant subspaces meet only in `0`.  All that is asked of `k` is that `2` be regular, which over
a field is `IsRegular.of_ne_zero`. -/
theorem symmetricInvariantForms_inf_alternatingInvariantForms (h2 : IsLeftRegular (2 : k))
    (ρ : Representation k G V) :
    symmetricInvariantForms ρ ⊓ alternatingInvariantForms ρ = ⊥ :=
  le_antisymm (fun _ hB => Submodule.mem_bot k |>.mpr
    (BilinForm.eq_zero_of_isSymm_of_isAlt h2 hB.1.2 hB.2.2)) bot_le

end SymmetricAlternatingRing

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
  exact hB.apply g x (ρ g⁻¹ y)

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
  · intro hB g
    refine BilinForm.isIsometry_iff.mpr fun x y => ?_
    have h := DFunLike.congr_fun (hB.isIntertwining g x) (ρ g y)
    simpa [Module.Dual.transpose_apply] using h

end Group

section GroupRing

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

/-- **The invariant forms of `ρ` are the invariants of `linHom ρ ρ.dual`.**  Invariance of a form
is intertwining of the map `V → V*` it is, which is Mathlib's membership criterion for the
invariants of a `Hom` representation. -/
theorem invariantForms_eq_invariants_linHom_dual (ρ : Representation k G V) :
    invariantForms ρ =
      @Representation.invariants k G (V →ₗ[k] Module.Dual k V) _ _ LinearMap.addCommGroup _
        (Representation.linHom ρ ρ.dual) := by
  ext B
  rw [mem_invariantForms, isInvariantForm_iff_isIntertwiningMap,
    ← Representation.mem_linHom_invariants_iff_isIntertwining]
  exact Iff.rfl

/-- **The invariant forms of `ρ` are the intertwiners from `ρ` to its dual.**  This is the bundled
form of `TauCeti.Representation.isInvariantForm_iff_isIntertwiningMap`, and it is what puts the
invariant forms in reach of machinery that counts intertwiners: it is Mathlib's
`Representation.invariantsEquivIntertwiningMap`, transported along
`TauCeti.Representation.invariantForms_eq_invariants_linHom_dual`. -/
noncomputable def invariantFormsEquivIntertwiningMapDual (ρ : Representation k G V) :
    invariantForms ρ ≃ₗ[k] Representation.IntertwiningMap ρ ρ.dual :=
  (LinearEquiv.ofEq _ _ (invariantForms_eq_invariants_linHom_dual ρ)).trans
    (Representation.invariantsEquivIntertwiningMap ρ ρ.dual)

/-- The intertwiner attached to an invariant form is that form, read as a map `V → V*`. -/
@[simp]
theorem invariantFormsEquivIntertwiningMapDual_apply_toLinearMap (ρ : Representation k G V)
    (B : invariantForms ρ) :
    (invariantFormsEquivIntertwiningMapDual ρ B).toLinearMap = (B : BilinForm k V) := (rfl)

/-- The invariant form attached to an intertwiner `ρ → ρ.dual` is that intertwiner, read as a
bilinear form. -/
@[simp]
theorem invariantFormsEquivIntertwiningMapDual_symm_apply_coe (ρ : Representation k G V)
    (f : Representation.IntertwiningMap ρ ρ.dual) :
    (((invariantFormsEquivIntertwiningMapDual ρ).symm f : invariantForms ρ) : BilinForm k V) =
      f.toLinearMap := (rfl)

end GroupRing

/-! ### Invariant forms on an irreducible representation -/

section Irreducible

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable {ρ : Representation k G V} {B C : BilinForm k V}

/-- **A nonzero invariant form on an irreducible representation has trivial left radical.** -/
theorem IsInvariantForm.ker_eq_bot [ρ.IsIrreducible] (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0) :
    LinearMap.ker B = ⊥ := by
  -- Read as a map `V → V*`, `B` intertwines `ρ` with `ρ.dual`; an intertwiner out of an
  -- irreducible representation is injective or zero, and `B` is not zero.
  set f : Representation.IntertwiningMap ρ ρ.dual :=
    B.intertwiningMap_of_isIntertwiningMap ρ ρ.dual
      ((isInvariantForm_iff_isIntertwiningMap ρ B).mp hB).isIntertwining
  have hf0 : f ≠ 0 := fun h => hB0 (congrArg Representation.IntertwiningMap.toLinearMap h)
  exact LinearMap.ker_eq_bot.mpr
    ((Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf0)

/-- **A nonzero invariant form on an irreducible representation is nondegenerate.** -/
theorem IsInvariantForm.nondegenerate [ρ.IsIrreducible] (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0) :
    B.Nondegenerate := by
  -- Both radicals are handled by `ker_eq_bot`, the right one via the flipped form.
  refine ⟨LinearMap.separatingLeft_iff_ker_eq_bot.mpr (hB.ker_eq_bot hB0),
    LinearMap.flip_separatingLeft.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mpr ?_)⟩
  exact hB.flip.ker_eq_bot fun h => hB0 (LinearMap.BilinForm.flipHom.map_eq_zero_iff.mp h)

/-- **On an irreducible representation, an invariant form is nondegenerate exactly when it is
nonzero.** The interesting direction is `TauCeti.Representation.IsInvariantForm.nondegenerate`; the
other is Mathlib's `LinearMap.BilinForm.Nondegenerate.ne_zero`, once the space an irreducible
representation acts on is known to be nonzero. -/
theorem IsInvariantForm.nondegenerate_iff_ne_zero [ρ.IsIrreducible] (hB : IsInvariantForm ρ B) :
    B.Nondegenerate ↔ B ≠ 0 := by
  -- Irreducibility makes `ρ.asModule` a simple, hence nonzero, module over the group algebra.
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra k G) _
  have : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  exact ⟨fun h => h.ne_zero, hB.nondegenerate⟩

variable [FiniteDimensional k V] [IsAlgClosed k] [ρ.IsIrreducible]

/-- **An invariant form on an irreducible representation is unique up to a scalar**: over an
algebraically closed field and in finite dimensions, every invariant form `C` is a scalar multiple
of a nonzero invariant form `B`. -/
theorem IsInvariantForm.exists_eq_smul (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0)
    (hC : IsInvariantForm ρ C) : ∃ c : k, C = c • B := by
  -- Comparing `C` with `B` produces an endomorphism `φ` commuting with the action, hence a scalar
  -- by Schur's lemma in the form of Mathlib's
  -- `Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`.
  have hBnd : B.Nondegenerate := hB.nondegenerate hB0
  -- `φ` reads `C` through the isomorphism `V ≃ V*` that the nondegenerate `B` provides.
  set φ : V →ₗ[k] V := C.symmCompOfNondegenerate B hBnd
  have hφB : ∀ v w : V, B (φ v) w = C v w := fun v w =>
    C.symmCompOfNondegenerate_left_apply hBnd w v
  have hφ : ∀ (g : G) (v : V), φ (ρ g v) = ρ g (φ v) := by
    intro g v
    refine sub_eq_zero.mp (hBnd.1 _ fun w => ?_)
    rw [map_sub, LinearMap.sub_apply, hφB, hB.apply_left, hφB, hC.apply_left, sub_self]
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 (φ.intertwiningMap_of_isIntertwiningMap ρ ρ hφ)
  have hcφ : φ = c • LinearMap.id := LinearMap.ext fun v => by
    simpa using (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hc).symm
  refine ⟨c, LinearMap.ext fun v => LinearMap.ext fun w => ?_⟩
  have h := hφB v w
  rw [hcφ] at h
  simpa using h.symm

/-- **A nonzero invariant form on an irreducible representation spans all of them**: the invariant
forms are a line. -/
theorem IsInvariantForm.invariantForms_eq_span (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0) :
    invariantForms ρ = Submodule.span k {B} := by
  refine le_antisymm (fun C hC => ?_) (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hB))
  obtain ⟨c, rfl⟩ := hB.exists_eq_smul hB0 hC
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self B)

/-- **A nonzero invariant form on an irreducible representation is its own flip up to sign**: its
flip is either the form itself or its negative.  This holds in every characteristic. -/
theorem IsInvariantForm.flip_eq_or_flip_eq_neg (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0) :
    B.flip = B ∨ B.flip = -B := by
  -- The flip is invariant too, so it is a scalar multiple `c • B` of the form; reading that off
  -- twice multiplies each value of `B` by `c * c`, which is therefore `1`.
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
