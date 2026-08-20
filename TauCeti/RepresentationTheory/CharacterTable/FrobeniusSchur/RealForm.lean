/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Mathlib.Analysis.Complex.Polynomial.Basic` supplies the `IsAlgClosed ℂ` instance the
-- Frobenius-Schur trichotomy asks for.
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Trichotomy
public import TauCeti.RepresentationTheory.Irreducible
-- Private: `LinearMap.trace_baseChange` and `LinearMap.trace_conj'` are used only inside proofs.
import Mathlib.LinearAlgebra.Trace

/-!
# Real forms of a complex representation, and the orthogonal case

A **real form** of a representation `ρ` of `G` on a complex vector space `V` is a real
representation `σ` on a real vector space `W` whose complexification is `ρ`: a `ℂ`-linear
isomorphism `ℂ ⊗[ℝ] W ≃ₗ[ℂ] V` intertwining `1 ⊗ σ g` with `ρ g`.  Only the values on the pure
tensors `1 ⊗ₜ w` are asked for, which is enough because those generate `ℂ ⊗[ℝ] W` over `ℂ`
(`Representation.IsRealForm.map_baseChange` upgrades the condition to the statement that
`ρ g` is conjugate to the base change of `σ g`).  A representation is **realizable over `ℝ`** when
it admits a real form.  `Representation.IsRealForm` allows any carrier for the real form,
while `Representation.IsRealizableOverReal` pins it to `Fin (finrank ℂ V) → ℝ`, so that the
predicate needs no type existential; transporting a real form on an arbitrary carrier to the pinned
one along a basis is not built here.  Pinning the carrier by the dimension is only faithful in
finite dimension -- `finrank ℂ V = 0` for an infinite-dimensional `V`, which would make the pinned
carrier the zero space -- so `Representation.IsRealizableOverReal` carries
`FiniteDimensional ℂ V` as a conjunct of its statement, and
`Representation.isRealizableOverReal_iff` drops it again once it is available as an instance.  The
infinite-dimensional case is outside the scope of the pinned predicate; `Representation.IsRealForm`
is the notion to use there.

This file builds those two notions and proves the direction of the Frobenius-Schur criterion that
goes from a real form to the indicator: **an irreducible representation with a real form is
orthogonal**, `ν₂(ρ) = 1`.  The route is the one the trichotomy already asks for, an invariant
symmetric form.  A real representation of a finite group carries a nonzero invariant symmetric
form, obtained by averaging the coordinate dot product of a basis over the group
(`Representation.averageForm`); the base change of that form to `ℂ ⊗[ℝ] W`
(`LinearMap.BilinForm.baseChange`) stays symmetric, stays invariant for the base-changed
representation (`TauCeti.Representation.IsInvariantForm.baseChange`), and stays nonzero because
`ℝ → ℂ` is injective; transported along the isomorphism it is a nonzero invariant symmetric form on
`V`, and `TauCeti.Representation.frobeniusSchurIndicator_eq_one_of_isSymm` reads off the indicator.

The averaging step is where finiteness of `G` enters, and it is the only place: everything about
real forms below is stated for an arbitrary group.  Positivity is what makes the averaged form
nonzero -- the average of a sum of squares over the group is at least its value at the identity --
so it is the ordering of `ℝ`, not a division by `|G|`, that does the work, and no invertibility of
`|G|` is needed to produce the form.

The **converse** -- that an irreducible representation with `ν₂(ρ) = 1` is realizable over `ℝ` --
is not proved here.  It is a strictly stronger statement than the existence of an invariant
symmetric form supplied by
`TauCeti.Representation.frobeniusSchurIndicator_eq_one_iff`: passing from the form to a real
structure needs an invariant Hermitian inner product as well, and the antilinear involution built
from the two of them, whose fixed points are the real form.  That construction is separate work.

## Main definitions

* `Representation.averageForm`: the average of a bilinear form over a finite group.
* `Representation.IsRealForm`: `σ` is a real form of `ρ`.
* `Representation.IsRealizableOverReal`: `ρ` admits a real form on a carrier pinned by the
  dimension of `V`.

## Main results

* `Representation.isInvariantForm_averageForm`: the average of a bilinear form is
  invariant.
* `Representation.exists_isInvariantForm_isSymm_ne_zero`: **a real representation of a
  finite group on a nontrivial finite-dimensional space carries a nonzero invariant symmetric
  form.**
* `TauCeti.Representation.IsInvariantForm.baseChange`: the base change of an invariant form is
  invariant.
* `Representation.IsRealForm.map_baseChange`: a real form conjugates `ρ g` into the base
  change of `σ g`.
* `Representation.IsRealForm.character_eq`: the character of a representation with a real
  form is the character of that real form, in particular real-valued
  (`Representation.IsRealForm.conj_character`).
* `Representation.IsRealForm.exists_isInvariantForm`: a real form transports a nonzero
  invariant symmetric real form to a nonzero invariant symmetric complex form.
* `Representation.IsRealForm.frobeniusSchurIndicator_eq_one` and
  `Representation.frobeniusSchurIndicator_eq_one_of_isRealizableOverReal`: **an
  irreducible representation realizable over `ℝ` has Frobenius-Schur indicator `1`.**

## References

This builds the `IsRealForm` and `IsRealizableOverReal` targets of Layer 7 of
`TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md`, and the "realizable" direction of
the milestone `frobeniusSchurIndicatorRep_eq_one_realizable` pinned in the accompanying
`Suggested.lean`.

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 4.
-/

public section

open Module (finrank)

open scoped TensorProduct

open LinearMap (BilinForm)

namespace TauCeti

namespace Representation

/-! ### Base change of an invariant form -/

section BaseChangeForm

variable {R A G W : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [Monoid G]
  [AddCommMonoid W] [Module R W]

/-- **The base change of an invariant form is invariant** for the base-changed representation.  The
two base changes are matched on pure tensors, where both are the original form and the original
action, and extended by bilinearity. -/
theorem IsInvariantForm.baseChange {σ : Representation R G W} {B : BilinForm R W}
    (hB : IsInvariantForm σ B) :
    IsInvariantForm (Representation.baseChange A σ) (B.baseChange A) := by
  rw [isInvariantForm_iff]
  intro g u v
  simp only [Representation.baseChange_apply]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul a w =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v₁ v₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul a' w' =>
      simp only [LinearMap.baseChange_tmul, BilinForm.baseChange_tmul, hB.apply g w w']

end BaseChangeForm

end Representation

end TauCeti

open TauCeti

namespace Representation

open TauCeti.Representation

/-! ### Averaging a bilinear form over a finite group -/

section Average

variable {k G W : Type*} [CommSemiring k] [Group G] [Fintype G] [AddCommMonoid W] [Module k W]

/-- The **average** of a bilinear form over a finite group: `∑_g B (σ g ·) (σ g ·)`.  No division
by `|G|` is performed, so no invertibility of the group order is needed; the sum is already
invariant. -/
def averageForm (σ : Representation k G W) (B : BilinForm k W) : BilinForm k W :=
  ∑ g : G, B.comp (σ g) (σ g)

@[simp]
theorem averageForm_apply (σ : Representation k G W) (B : BilinForm k W) (x y : W) :
    averageForm σ B x y = ∑ g : G, B (σ g x) (σ g y) := by
  simp [averageForm, BilinForm.comp_apply]

/-- The average of a bilinear form over a finite group is invariant: reindexing the sum by right
translation absorbs the group element. -/
theorem isInvariantForm_averageForm (σ : Representation k G W) (B : BilinForm k W) :
    IsInvariantForm σ (averageForm σ B) := by
  rw [isInvariantForm_iff]
  intro h x y
  simp only [averageForm_apply]
  refine Eq.trans ?_ (Fintype.sum_equiv (Equiv.mulRight h)
    (fun g : G => B (σ (g * h) x) (σ (g * h) y)) (fun g : G => B (σ g x) (σ g y))
    fun g => rfl)
  exact Finset.sum_congr rfl fun g _ => by
    simp only [map_mul, Module.End.mul_apply]

/-- The average of a symmetric bilinear form is symmetric. -/
theorem averageForm_isSymm {σ : Representation k G W} {B : BilinForm k W} (hB : B.IsSymm) :
    (averageForm σ B).IsSymm :=
  ⟨fun x y => by
    simpa only [averageForm_apply] using
      Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => hB.eq (σ g x) (σ g y)⟩

end Average

/-! ### A nonzero invariant symmetric form on a real representation -/

section RealAverage

variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module ℝ W]

/-- **A real representation of a finite group carries a nonzero invariant symmetric form.**  Take
the dot product read in a basis and average it over the group; averaging preserves symmetry, and
the average of a positive semidefinite form is at least its value at the identity, hence still
positive definite.  This is the real input to the orthogonality of a representation with a real
form. -/
theorem exists_isInvariantForm_isSymm_ne_zero (σ : Representation ℝ G W)
    [FiniteDimensional ℝ W] [Nontrivial W] :
    ∃ B : BilinForm ℝ W, IsInvariantForm σ B ∧ B.IsSymm ∧ B ≠ 0 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set b := Module.finBasis ℝ W with hb
  set B₀ : BilinForm ℝ W := Matrix.toBilin b 1 with hB₀
  have hB₀apply : ∀ x y : W, B₀ x y = ∑ i, b.repr x i * b.repr y i := by
    intro x y
    simp [hB₀, Matrix.toBilin_apply, Matrix.one_apply, Finset.sum_ite_eq]
  have hB₀symm : B₀.IsSymm :=
    ⟨fun x y => by
      simpa only [hB₀apply] using
        Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => mul_comm _ _⟩
  have hB₀nonneg : ∀ x : W, 0 ≤ B₀ x x := fun x => by
    rw [hB₀apply]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  refine ⟨averageForm σ B₀, isInvariantForm_averageForm σ B₀, averageForm_isSymm hB₀symm, ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  have hpos : 0 < B₀ x x := by
    rw [hB₀apply]
    obtain ⟨i, hi⟩ : ∃ i, b.repr x i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hx (b.repr.injective ?_)
      rw [map_zero]
      ext j
      simp [hcon j]
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
      ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
  have hle : B₀ (σ 1 x) (σ 1 x) ≤ averageForm σ B₀ x x := by
    rw [averageForm_apply]
    exact Finset.single_le_sum (f := fun g : G => B₀ (σ g x) (σ g x))
      (fun g _ => hB₀nonneg _) (Finset.mem_univ 1)
  intro hzero
  rw [map_one] at hle
  simp only [Module.End.one_apply] at hle
  rw [hzero] at hle
  simp only [LinearMap.zero_apply] at hle
  exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl 0)

end RealAverage

/-! ### Real forms -/

section RealForm

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {W : Type*} [AddCommGroup W] [Module ℝ W]
variable {ρ : Representation ℂ G V} {σ : Representation ℝ G W}

/-- `σ` is a **real form** of `ρ` when the complexification `ℂ ⊗[ℝ] W` of the space of `σ` is
`ℂ`-linearly isomorphic to the space of `ρ` by an isomorphism intertwining the two actions.  The
condition is stated on the pure tensors `1 ⊗ₜ w`, which generate `ℂ ⊗[ℝ] W` over `ℂ`. -/
def IsRealForm (ρ : Representation ℂ G V) (σ : Representation ℝ G W) : Prop :=
  ∃ e : (ℂ ⊗[ℝ] W) ≃ₗ[ℂ] V, ∀ (g : G) (w : W), e (1 ⊗ₜ[ℝ] σ g w) = ρ g (e (1 ⊗ₜ[ℝ] w))

/-- `Representation.IsRealForm` unfolded: an intertwining `ℂ`-linear isomorphism from the
complexification. -/
theorem isRealForm_iff :
    IsRealForm ρ σ ↔
      ∃ e : (ℂ ⊗[ℝ] W) ≃ₗ[ℂ] V, ∀ (g : G) (w : W),
        e (1 ⊗ₜ[ℝ] σ g w) = ρ g (e (1 ⊗ₜ[ℝ] w)) :=
  (Iff.rfl)

/-- The intertwining condition on pure tensors upgrades to the whole complexification: the
isomorphism carries the base change of `σ g` to `ρ g`.  Both sides are `ℂ`-linear, so it is enough
to check it on the generators `a ⊗ₜ w`. -/
theorem IsRealForm.map_baseChange {e : (ℂ ⊗[ℝ] W) ≃ₗ[ℂ] V}
    (he : ∀ (g : G) (w : W), e (1 ⊗ₜ[ℝ] σ g w) = ρ g (e (1 ⊗ₜ[ℝ] w))) (g : G)
    (u : ℂ ⊗[ℝ] W) : e (Representation.baseChange ℂ σ g u) = ρ g (e u) := by
  simp only [Representation.baseChange_apply]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul a w =>
    have hsmul : ∀ v : W, (a ⊗ₜ[ℝ] v : ℂ ⊗[ℝ] W) = a • (1 ⊗ₜ[ℝ] v) := by
      intro v
      rw [TensorProduct.smul_tmul' a (1 : ℂ) v, smul_eq_mul, mul_one]
    rw [LinearMap.baseChange_tmul, hsmul (σ g w), hsmul w, map_smul, map_smul, map_smul, he g w]

/-- The character of a representation with a real form is the character of that real form.  In
particular it takes real values (`Representation.IsRealForm.conj_character`). -/
theorem IsRealForm.character_eq [FiniteDimensional ℝ W] (h : IsRealForm ρ σ) (g : G) :
    ρ.character g = (σ.character g : ℂ) := by
  obtain ⟨e, he⟩ := h
  have hconj : ρ g = e.conj (Representation.baseChange ℂ σ g) := by
    refine LinearMap.ext fun x => ?_
    have := IsRealForm.map_baseChange he g (e.symm x)
    simpa using this.symm
  rw [Representation.character, hconj, LinearMap.trace_conj', Representation.baseChange_apply,
    LinearMap.trace_baseChange]
  rfl

/-- The character of a representation with a real form is fixed by complex conjugation. -/
theorem IsRealForm.conj_character [FiniteDimensional ℝ W] (h : IsRealForm ρ σ) (g : G) :
    (starRingEnd ℂ) (ρ.character g) = ρ.character g := by
  rw [h.character_eq g, Complex.conj_ofReal]

/-- **A real form transports invariant symmetric forms.**  The base change to `ℂ` of a nonzero
invariant symmetric form on the real side, read through the isomorphism, is a nonzero invariant
symmetric form on the complex side. -/
theorem IsRealForm.exists_isInvariantForm (h : IsRealForm ρ σ) {B : BilinForm ℝ W}
    (hB : IsInvariantForm σ B) (hsymm : B.IsSymm) (hB0 : B ≠ 0) :
    ∃ C : BilinForm ℂ V, IsInvariantForm ρ C ∧ C.IsSymm ∧ C ≠ 0 := by
  obtain ⟨e, he⟩ := h
  refine ⟨(B.baseChange ℂ).comp e.symm.toLinearMap e.symm.toLinearMap, ?_, ?_, ?_⟩
  · rw [isInvariantForm_iff]
    intro g x y
    simp only [BilinForm.comp_apply, LinearEquiv.coe_coe]
    have hx : e.symm (ρ g x) = Representation.baseChange ℂ σ g (e.symm x) := by
      refine e.injective ?_
      rw [LinearEquiv.apply_symm_apply, IsRealForm.map_baseChange he g (e.symm x),
        LinearEquiv.apply_symm_apply]
    have hy : e.symm (ρ g y) = Representation.baseChange ℂ σ g (e.symm y) := by
      refine e.injective ?_
      rw [LinearEquiv.apply_symm_apply, IsRealForm.map_baseChange he g (e.symm y),
        LinearEquiv.apply_symm_apply]
    rw [hx, hy, (hB.baseChange (A := ℂ)).apply g]
  · have hDsymm : (B.baseChange ℂ).IsSymm :=
      BilinForm.isSymm_iff.mpr (BilinForm.IsSymm.baseChange ℂ (BilinForm.isSymm_iff.mp hsymm))
    exact ⟨fun x y => by
      simpa only [BilinForm.comp_apply, LinearEquiv.coe_coe] using
        hDsymm.eq (e.symm x) (e.symm y)⟩
  · intro hzero
    refine hB0 (LinearMap.ext fun w => LinearMap.ext fun w' => ?_)
    have hval := LinearMap.congr_fun₂ hzero (e (1 ⊗ₜ[ℝ] w)) (e (1 ⊗ₜ[ℝ] w'))
    simp only [BilinForm.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      BilinForm.baseChange_tmul, LinearMap.zero_apply, mul_one] at hval
    rcases smul_eq_zero.mp hval with hzero' | hone
    · simpa using hzero'
    · exact absurd hone one_ne_zero

variable (ρ) in
/-- **Realizability over `ℝ`**: `ρ` admits a real form on the carrier `Fin (finrank ℂ V) → ℝ`.
Pinning the carrier avoids a type existential; a real form on an arbitrary carrier is
`Representation.IsRealForm`, and every result below about the indicator is proved from that
more general notion.

Finite-dimensionality of `V` is part of the statement, not an ambient hypothesis: `finrank ℂ V`
is `0` for an infinite-dimensional `V`, so without it the pinned carrier would degenerate to the
zero space and the predicate would say nothing about real forms.  The infinite-dimensional case is
outside the scope of this notion; use `Representation.IsRealForm` there. -/
def IsRealizableOverReal : Prop :=
  FiniteDimensional ℂ V ∧ ∃ σ : Representation ℝ G (Fin (finrank ℂ V) → ℝ), IsRealForm ρ σ

/-- `Representation.IsRealizableOverReal` unfolded, with the finite-dimensionality it carries
already available as an instance. -/
theorem isRealizableOverReal_iff [FiniteDimensional ℂ V] :
    IsRealizableOverReal ρ ↔
      ∃ σ : Representation ℝ G (Fin (finrank ℂ V) → ℝ), IsRealForm ρ σ :=
  and_iff_right ‹FiniteDimensional ℂ V›

end RealForm

/-! ### The orthogonal case -/

section Orthogonal

variable {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] {W : Type*} [AddCommGroup W] [Module ℝ W]
variable {ρ : Representation ℂ G V} {σ : Representation ℝ G W}

/-- **An irreducible representation with a real form is orthogonal.**  Averaging produces a nonzero
invariant symmetric form on the real side, and transporting it along the real form makes the
complex representation carry one too, which is exactly the orthogonal case of the Frobenius-Schur
trichotomy. -/
theorem IsRealForm.frobeniusSchurIndicator_eq_one [FiniteDimensional ℝ W] [Nontrivial W]
    [ρ.IsIrreducible] (h : IsRealForm ρ σ) : frobeniusSchurIndicator ρ = 1 := by
  obtain ⟨B, hB, hsymm, hB0⟩ := exists_isInvariantForm_isSymm_ne_zero σ
  obtain ⟨C, hC, hCsymm, hC0⟩ := h.exists_isInvariantForm hB hsymm hB0
  exact frobeniusSchurIndicator_eq_one_of_isSymm ρ hC hC0 hCsymm

/-- **An irreducible representation realizable over `ℝ` has Frobenius-Schur indicator `1`.**  This
is the "realizable" half of the orthogonality criterion; the converse, that indicator `1` produces
a real form, is not proved here. -/
theorem frobeniusSchurIndicator_eq_one_of_isRealizableOverReal [ρ.IsIrreducible]
    (h : IsRealizableOverReal ρ) : frobeniusSchurIndicator ρ = 1 := by
  obtain ⟨σ, hσ⟩ := isRealizableOverReal_iff.mp h
  have : Nontrivial V :=
    TauCeti.Representation.IsIrreducible.nontrivial (inferInstance : ρ.IsIrreducible)
  have hpos : 0 < finrank ℂ V := Module.finrank_pos
  have : Nonempty (Fin (finrank ℂ V)) := ⟨⟨0, hpos⟩⟩
  exact hσ.frobeniusSchurIndicator_eq_one

end Orthogonal

end Representation
