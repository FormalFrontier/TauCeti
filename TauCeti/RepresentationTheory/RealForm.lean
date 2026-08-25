/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.Finiteness.Descent
public import TauCeti.RepresentationTheory.InvariantForm.BaseChange

/-!
# Real forms of a complex representation

A **real form** of a representation `ρ` of `G` on a complex vector space `V` is a real
representation `σ` on a real vector space `W` whose complexification is `ρ`: a `ℂ`-linear
isomorphism `ℂ ⊗[ℝ] W ≃ₗ[ℂ] V` intertwining `1 ⊗ σ g` with `ρ g`.  Only the values on the pure
tensors `1 ⊗ₜ w` are asked for, which is enough because those generate `ℂ ⊗[ℝ] W` over `ℂ`:
`Representation.isRealForm_iff_nonempty_equiv` upgrades the condition to an equivalence of
representations `(Representation.baseChange ℂ σ).Equiv ρ`, which is the statement that `ρ` *is* the
complexification of `σ`.  A representation is **realizable over `ℝ`** when it admits a real form.

`Representation.IsRealForm` allows any carrier for the real form, while
`Representation.IsRealizableOverReal` pins it to `Fin (finrank ℂ V) → ℝ`, so that the predicate
needs no type existential; nothing is lost by pinning it, because
`Representation.IsRealForm.isRealizableOverReal` transports a real form of a finite-dimensional
representation to the pinned carrier along a real basis (the carrier of the real form is then
finite-dimensional too, by `Representation.IsRealForm.finiteDimensional_iff`).  The pinned
predicate needs no finite-dimensionality hypothesis either: the pinned carrier is
finite-dimensional, so it already implies `FiniteDimensional ℂ V`
(`Representation.IsRealizableOverReal.finiteDimensional`).  For an infinite-dimensional `V` it is
therefore simply false, and `Representation.IsRealForm` is the notion to use there.

Everything here is for a representation of an arbitrary monoid: the real-form vocabulary and its
transports never invert a group element, and the passage to the Frobenius-Schur indicator that
consumes them -- `Representation.frobeniusSchurIndicator_eq_one_of_isRealizableOverReal`, in
`TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.RealForm` -- asks for a finite group
only where it sums over the group.

## Main definitions

* `Representation.IsRealForm`: `σ` is a real form of `ρ`.
* `Representation.IsRealizableOverReal`: `ρ` admits a real form on a carrier pinned by the
  dimension of `V`.

## Main results

* `Representation.isRealForm_iff_nonempty_equiv`: a real form is exactly an equivalence of
  representations from the complexification of `σ` to `ρ`.
* `Representation.IsRealForm.char_eq`: the character of a representation with a real
  form is the character of that real form, in particular real-valued
  (`Representation.IsRealForm.conj_char`).
* `Representation.IsRealForm.exists_isInvariantForm_isSymm_ne_zero`: a real form transports a
  nonzero invariant symmetric real form to a nonzero invariant symmetric complex form.
* `Representation.IsRealForm.finiteDimensional_iff`: a real form is finite-dimensional exactly when
  the representation it is a form of is.
* `Representation.IsRealForm.isRealizableOverReal`: a real form of a finite-dimensional
  representation makes `ρ` realizable over `ℝ` in the pinned sense.
* `Representation.IsRealizableOverReal.finiteDimensional`: a representation realizable over `ℝ` is
  finite-dimensional.

## References

This builds the `IsRealForm` and `IsRealizableOverReal` targets of Layer 7 of
`TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md`.

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 4.
-/

public section

open Module (finrank)

open scoped TensorProduct

open LinearMap (BilinForm)

open TauCeti

namespace Representation

open TauCeti.Representation

variable {G : Type*} [Monoid G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {W : Type*} [AddCommGroup W] [Module ℝ W]
variable {ρ : Representation ℂ G V} {σ : Representation ℝ G W}

/-! ### Real forms -/

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

/-- The intertwining condition on pure tensors upgrades to the whole complexification: an
isomorphism intertwining on `1 ⊗ₜ w` carries the base change of `σ g` to `ρ g`.  Both sides are
`ℂ`-linear, so it is enough to check them on the generators `a ⊗ₜ w`.  This is the content of
`Representation.isRealForm_iff_nonempty_equiv`, which is the public form of the statement. -/
private theorem map_baseChange_of_map_one_tmul {e : (ℂ ⊗[ℝ] W) ≃ₗ[ℂ] V}
    (he : ∀ (g : G) (w : W), e (1 ⊗ₜ[ℝ] σ g w) = ρ g (e (1 ⊗ₜ[ℝ] w))) (g : G)
    (u : ℂ ⊗[ℝ] W) : e (Representation.baseChange ℂ σ g u) = ρ g (e u) := by
  simp only [Representation.baseChange_apply]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul a w =>
    rw [LinearMap.baseChange_tmul, TensorProduct.tmul_eq_smul_one_tmul a (σ g w),
      TensorProduct.tmul_eq_smul_one_tmul a w, map_smul, map_smul, map_smul, he g w]

/-- **A real form is an equivalence of representations from the complexification.**  This is the
characterization of `Representation.IsRealForm` against `Representation.baseChange`: checking the
intertwining condition on the pure tensors `1 ⊗ₜ w` is the same as producing a
`Representation.Equiv` out of the whole complexification. -/
theorem isRealForm_iff_nonempty_equiv :
    IsRealForm ρ σ ↔ Nonempty ((Representation.baseChange ℂ σ).Equiv ρ) := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨Equiv.mk e fun g => LinearMap.ext (map_baseChange_of_map_one_tmul he g)⟩
  · rintro ⟨φ⟩
    refine ⟨φ.toLinearEquiv, fun g w => ?_⟩
    simpa [Equiv.toLinearEquiv_apply] using φ.isIntertwining (g := g) (v := 1 ⊗ₜ[ℝ] w)

/-- The character of a representation with a real form is the character of that real form.  In
particular it takes real values (`Representation.IsRealForm.conj_char`). -/
theorem IsRealForm.char_eq [FiniteDimensional ℝ W] (h : IsRealForm ρ σ) (g : G) :
    ρ.character g = (σ.character g : ℂ) := by
  obtain ⟨φ⟩ := isRealForm_iff_nonempty_equiv.mp h
  rw [← congrFun (char_iso φ) g]
  simp only [Representation.character, Representation.baseChange_apply,
    LinearMap.trace_baseChange, Complex.coe_algebraMap]

/-- The character of a representation with a real form is fixed by complex conjugation. -/
theorem IsRealForm.conj_char [FiniteDimensional ℝ W] (h : IsRealForm ρ σ) (g : G) :
    (starRingEnd ℂ) (ρ.character g) = ρ.character g := by
  rw [h.char_eq g, Complex.conj_ofReal]

/-- The complex dimension of a representation is the real dimension of any of its real forms:
complexification does not change the dimension. -/
theorem IsRealForm.finrank_eq (h : IsRealForm ρ σ) :
    finrank ℝ W = finrank ℂ V := by
  obtain ⟨e, -⟩ := h
  rw [← e.finrank_eq, Module.finrank_baseChange]

/-- **A real form is finite-dimensional exactly when the representation it is a form of is.**
Finiteness passes from `W` to `V` because `V` is the complexification `ℂ ⊗[ℝ] W` up to isomorphism,
and back down because `ℂ` is faithfully flat over `ℝ`
(`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`).  Both directions are available with no
finiteness in the ambient context, so a consumer holding finiteness on either side gets it on the
other; comparing dimensions instead (`Representation.IsRealForm.finrank_eq`) would say nothing when
the common dimension is `0`. -/
theorem IsRealForm.finiteDimensional_iff (h : IsRealForm ρ σ) :
    FiniteDimensional ℝ W ↔ FiniteDimensional ℂ V := by
  obtain ⟨e, -⟩ := h
  constructor
  · intro _
    exact Module.Finite.equiv e
  · intro _
    have : Module.Finite ℂ (ℂ ⊗[ℝ] W) := Module.Finite.equiv e.symm
    exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat ℂ

/-- **A real form transports invariant symmetric forms.**  The base change to `ℂ` of a nonzero
invariant symmetric form on the real side, read through the isomorphism, is a nonzero invariant
symmetric form on the complex side. -/
theorem IsRealForm.exists_isInvariantForm_isSymm_ne_zero (h : IsRealForm ρ σ) {B : BilinForm ℝ W}
    (hB : IsInvariantForm σ B) (hsymm : B.IsSymm) (hB0 : B ≠ 0) :
    ∃ C : BilinForm ℂ V, IsInvariantForm ρ C ∧ C.IsSymm ∧ C ≠ 0 := by
  obtain ⟨φ⟩ := isRealForm_iff_nonempty_equiv.mp h
  have hsymm' : ∀ (g : G) (v : V), φ.toLinearEquiv.symm (ρ g v) =
      Representation.baseChange ℂ σ g (φ.toLinearEquiv.symm v) :=
    fun g v => φ.symm.isIntertwining (g := g) (v := v)
  refine ⟨BilinForm.congr φ.toLinearEquiv (B.baseChange ℂ), ?_, ?_, ?_⟩
  · rw [isInvariantForm_iff]
    intro g x y
    simp only [BilinForm.congr_apply, hsymm']
    exact (hB.baseChange (A := ℂ)).apply g _ _
  · have hDsymm : (B.baseChange ℂ).IsSymm :=
      BilinForm.isSymm_iff.mpr (BilinForm.IsSymm.baseChange ℂ (BilinForm.isSymm_iff.mp hsymm))
    exact ⟨fun x y => by
      simpa only [BilinForm.congr_apply] using
        hDsymm.eq (φ.toLinearEquiv.symm x) (φ.toLinearEquiv.symm y)⟩
  · exact (BilinForm.congr φ.toLinearEquiv).map_ne_zero_iff.mpr
      ((BilinForm.baseChange_eq_zero_iff (A := ℂ) B).not.mpr hB0)

/-! ### Realizability over the reals -/

variable (ρ) in
/-- **Realizability over `ℝ`**: `ρ` admits a real form on the carrier `Fin (finrank ℂ V) → ℝ`.
Pinning the carrier avoids a type existential; a real form on an arbitrary carrier is
`Representation.IsRealForm`, and every result about the indicator is proved from that more general
notion.

Pinning the carrier by the dimension costs nothing: the pinned carrier is finite-dimensional, so a
real form on it already forces `V` to be finite-dimensional
(`Representation.IsRealizableOverReal.finiteDimensional`), and conversely every real form on a
finite-dimensional carrier transports to the pinned one
(`Representation.IsRealForm.isRealizableOverReal`).  For an infinite-dimensional `V` the predicate
is therefore simply false -- `finrank ℂ V` is then `0` and the pinned carrier is the zero space --
and `Representation.IsRealForm` is the notion to use there. -/
def IsRealizableOverReal : Prop :=
  ∃ σ : Representation ℝ G (Fin (finrank ℂ V) → ℝ), IsRealForm ρ σ

/-- `Representation.IsRealizableOverReal` unfolded: it is the existence of a real form on the
pinned carrier, and this is the elimination principle for it. -/
theorem isRealizableOverReal_iff :
    IsRealizableOverReal ρ ↔
      ∃ σ : Representation ℝ G (Fin (finrank ℂ V) → ℝ), IsRealForm ρ σ :=
  (Iff.rfl)

/-- **A representation realizable over `ℝ` is finite-dimensional.**  The pinned carrier
`Fin (finrank ℂ V) → ℝ` is finite-dimensional, so `V`, being the complexification of it, is too.
This is what makes pinning the carrier by the dimension faithful. -/
theorem IsRealizableOverReal.finiteDimensional (h : IsRealizableOverReal ρ) :
    FiniteDimensional ℂ V := by
  obtain ⟨_, hσ⟩ := h
  exact hσ.finiteDimensional_iff.mp inferInstance

/-- **A real form on an arbitrary carrier realizes `ρ` over `ℝ`.**  Reading `σ` in a real basis of
`W` moves it to the pinned carrier: complexification does not change the dimension
(`Representation.IsRealForm.finrank_eq`), so a basis of `W` is indexed by `Fin (finrank ℂ V)`, and
conjugating `σ` by the resulting coordinate isomorphism turns the real form into one on
`Fin (finrank ℂ V) → ℝ`.  This is what makes `Representation.IsRealizableOverReal` usable from a
real form carried by whatever space it naturally lives on.

Finiteness is asked of `V`, the representation the conclusion speaks about; the carrier `W` of the
real form inherits it through `Representation.IsRealForm.finiteDimensional_iff`, which also takes a
consumer who has finiteness on the real side the other way. -/
theorem IsRealForm.isRealizableOverReal [FiniteDimensional ℂ V] (h : IsRealForm ρ σ) :
    IsRealizableOverReal ρ := by
  have : FiniteDimensional ℝ W := h.finiteDimensional_iff.mpr inferInstance
  have hrank := h.finrank_eq
  obtain ⟨e, he⟩ := h
  let f : W ≃ₗ[ℝ] (Fin (finrank ℂ V) → ℝ) :=
    ((Module.finBasis ℝ W).reindex (finCongr hrank)).equivFun
  refine ⟨{ toFun := fun g => f.conj (σ g)
            map_one' := by simp [Module.End.one_eq_id]
            map_mul' := fun g g' => by
              rw [map_mul, Module.End.mul_eq_comp, LinearEquiv.conj_comp,
                Module.End.mul_eq_comp] }, ?_⟩
  refine ⟨(f.symm.baseChange ℝ ℂ _ _).trans e, fun g x => ?_⟩
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  exact he g (f.symm x)

end Representation
