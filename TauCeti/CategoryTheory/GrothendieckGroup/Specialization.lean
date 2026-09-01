/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Laurent

/-!
# Specialization of Laurent modules

This file supplies the algebraic specializations of a Laurent module at `q = 1` and `q = -1`.
For a Laurent-module `M` and a ring homomorphism `ev : ℤ[q,q⁻¹] →+* ℤ`, the specialization is
presented as the quotient of `M` by the relations
`q • x = ev q • x`.  This is the standard presentation of
`ℤ ⊗[ℤ[q,q⁻¹]] M`, with the first tensor factor viewed through `ev`, but the quotient presentation
makes the canonical map and its universal property available without choosing an additional
module structure on the tensor product.

The two distinguished evaluations are `laurentEvalOne` and `laurentEvalNegOne`.  The resulting
maps record that a Laurent shift becomes the identity at `q = 1` and multiplication by
`(-1)^n` at `q = -1`.  No comparison with an ungraded category is built in: such a comparison
needs the extra forgetful and Ext data described in the Grothendieck-groups roadmap.

## Main definitions

* `TauCeti.LaurentSpecialization`: specialization of a Laurent module along a ring homomorphism.
* `TauCeti.specializeOf` and `TauCeti.specializeLift`: its canonical map and universal factor.
* `TauCeti.SpecializeAtOne` and `TauCeti.SpecializeAtNegOne`: the two algebraic specializations.

## Main results

* `TauCeti.specializeOf_smul`: the defining scalar relation in the specialization.
* `TauCeti.specializeAtOne_T_smul` and `TauCeti.specializeAtNegOne_T_smul`: the shift laws at
  `q = 1` and `q = -1`.

The quotient presentation is the elementary base-change construction from Weibel, *The K-book*,
Chapter II, §1.  The evaluation convention and the warning that specialization may change
nondegeneracy follow Dancso--Licata, "Koszul algebras and flow lattices", §3.1.
-/

public section

namespace TauCeti

open LaurentPolynomial

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- The Laurent-scalar relations used to specialize a Laurent module along `ev`.

The quotient identifies the action of a Laurent polynomial with the integer action obtained by
evaluating that polynomial at `ev`. -/
def LaurentScalarRelations (ev : LaurentPolynomial ℤ →+* ℤ) (M : Type*)
    [AddCommGroup M] [Module (LaurentPolynomial ℤ) M] : AddSubgroup M :=
  AddSubgroup.closure {x | ∃ r m, x = r • m - ev r • m}

/-- The algebraic base change of a Laurent module along `ev`, presented by scalar relations. -/
abbrev LaurentSpecialization (ev : LaurentPolynomial ℤ →+* ℤ) (M : Type*)
    [AddCommGroup M] [Module (LaurentPolynomial ℤ) M] :=
  M ⧸ LaurentScalarRelations ev M

/-- The canonical map from a Laurent module to its specialization. -/
noncomputable def specializeOf (ev : LaurentPolynomial ℤ →+* ℤ) (M : Type*)
    [AddCommGroup M] [Module (LaurentPolynomial ℤ) M] : M →+ LaurentSpecialization ev M :=
  QuotientAddGroup.mk' (LaurentScalarRelations ev M)

/-- A map is compatible with specialization along `ev` when it intertwines Laurent scalars with
the integer action obtained by evaluating them. -/
def IsLaurentLinearAt (ev : LaurentPolynomial ℤ →+* ℤ) (f : M →+ N)
    [Module (LaurentPolynomial ℤ) M] : Prop :=
  ∀ r x, f (r • x) = ev r • f x

private theorem scalarRelations_le_ker (ev : LaurentPolynomial ℤ →+* ℤ) (f : M →+ N)
    [Module (LaurentPolynomial ℤ) M] (hf : IsLaurentLinearAt ev f) :
    LaurentScalarRelations ev M ≤ f.ker := by
  refine (AddSubgroup.closure_le (f.ker)).2 ?_
  rintro x ⟨r, m, rfl⟩
  -- View kernel membership as an equality so the compatibility hypothesis can rewrite it.
  change f (r • m - ev r • m) = 0
  rw [map_sub, hf]
  simp

/-- The unique additive map out of a specialization whose composite with `specializeOf` is `f`.

The compatibility hypothesis is precisely the relation imposed by the quotient; no bijectivity or
comparison with another category is inferred. -/
noncomputable def specializeLift (ev : LaurentPolynomial ℤ →+* ℤ) (f : M →+ N)
    [Module (LaurentPolynomial ℤ) M] (hf : IsLaurentLinearAt ev f) :
    LaurentSpecialization ev M →+ N :=
  QuotientAddGroup.lift (LaurentScalarRelations ev M) f (scalarRelations_le_ker ev f hf)

/-- The lift agrees with the original map on the canonical representatives. -/
@[simp]
theorem specializeLift_of (ev : LaurentPolynomial ℤ →+* ℤ) (f : M →+ N)
    [Module (LaurentPolynomial ℤ) M] (hf : IsLaurentLinearAt ev f) (x : M) :
    specializeLift ev f hf (specializeOf ev M x) = f x :=
  by
    -- Unfold both quotient maps to put the lift in the form of `lift_mk'`.
    change
      (QuotientAddGroup.lift (LaurentScalarRelations ev M) f
        (scalarRelations_le_ker ev f hf)) (↑x : M ⧸ LaurentScalarRelations ev M) = f x
    exact QuotientAddGroup.lift_mk' _ _ _

/-- Any additive map with the same values on canonical representatives is this lift. -/
theorem specializeLift_unique (ev : LaurentPolynomial ℤ →+* ℤ) (f : M →+ N)
    [Module (LaurentPolynomial ℤ) M] (hf : IsLaurentLinearAt ev f)
    (g : LaurentSpecialization ev M →+ N)
    (hg : ∀ x, g (specializeOf ev M x) = f x) :
    g = specializeLift ev f hf := by
  apply AddMonoidHom.ext
  intro y
  induction y using QuotientAddGroup.induction_on' with
  | _ x =>
    -- Quotient induction presents this class by the canonical representative of `x`.
    change g (specializeOf ev M x) = specializeLift ev f hf (specializeOf ev M x)
    rw [hg, specializeLift_of]

/-- The scalar relation defining Laurent specialization. -/
@[simp]
theorem specializeOf_smul (ev : LaurentPolynomial ℤ →+* ℤ) (r : LaurentPolynomial ℤ) (x : M)
    [Module (LaurentPolynomial ℤ) M] :
    specializeOf ev M (r • x) = ev r • specializeOf ev M x := by
  -- Rewrite the additive quotient representatives before applying its equality criterion.
  change (↑(r • x) : M ⧸ LaurentScalarRelations ev M) = ↑(ev r • x)
  exact (QuotientAddGroup.eq_iff_sub_mem).2 <| by
    exact AddSubgroup.subset_closure ⟨r, x, rfl⟩

/-- Evaluation of a Laurent monomial at `q = 1`. -/
noncomputable def laurentEvalOne : LaurentPolynomial ℤ →+* ℤ :=
  LaurentPolynomial.eval₂ (RingHom.id ℤ) (1 : ℤˣ)

/-- At `q = 1`, every Laurent monomial evaluates to `1`. -/
@[simp]
theorem laurentEvalOne_T (n : ℤ) : laurentEvalOne (T n) = 1 := by
  rw [laurentEvalOne, LaurentPolynomial.eval₂_T]
  simp

/-- Evaluation of a Laurent monomial at `q = -1`. -/
noncomputable def laurentEvalNegOne : LaurentPolynomial ℤ →+* ℤ :=
  LaurentPolynomial.eval₂ (RingHom.id ℤ) (-1 : ℤˣ)

/-- The `q = -1` evaluation of a Laurent monomial is its sign `(-1)^n`. -/
@[simp]
theorem laurentEvalNegOne_T (n : ℤ) : laurentEvalNegOne (T n) = (n.negOnePow : ℤ) := by
  rw [laurentEvalNegOne, LaurentPolynomial.eval₂_T]
  rfl

/-- The specialization of a Laurent module at `q = 1`. -/
abbrev SpecializeAtOne (M : Type*) [AddCommGroup M] [Module (LaurentPolynomial ℤ) M] :=
  LaurentSpecialization laurentEvalOne M

/-- The specialization of a Laurent module at `q = -1`. -/
abbrev SpecializeAtNegOne (M : Type*) [AddCommGroup M] [Module (LaurentPolynomial ℤ) M] :=
  LaurentSpecialization laurentEvalNegOne M

/-- At `q = 1`, every Laurent shift has the same specialized class. -/
theorem specializeAtOne_T_smul (n : ℤ) (x : M) [Module (LaurentPolynomial ℤ) M] :
    specializeOf laurentEvalOne M ((T n : LaurentPolynomial ℤ) • x) =
      specializeOf laurentEvalOne M x := by
  rw [specializeOf_smul (M := M), laurentEvalOne_T]
  simp

/-- At `q = -1`, a Laurent shift acts by its sign on the specialized class. -/
theorem specializeAtNegOne_T_smul (n : ℤ) (x : M) [Module (LaurentPolynomial ℤ) M] :
    specializeOf laurentEvalNegOne M ((T n : LaurentPolynomial ℤ) • x) =
      (n.negOnePow : ℤ) • specializeOf laurentEvalNegOne M x := by
  rw [specializeOf_smul (M := M), laurentEvalNegOne_T]

end TauCeti
