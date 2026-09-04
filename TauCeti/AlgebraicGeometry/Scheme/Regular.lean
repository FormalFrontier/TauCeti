/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Rational functions without poles are regular

On a locally Noetherian integral scheme a regular function has nonnegative order at every point
where it is defined (`TauCeti.AlgebraicGeometry.Scheme.ord_germToFunctionField_nonneg`). This file
proves the converse for a scheme of dimension at most one whose codimension-one local rings on an
open subset `U` are discrete valuation rings: a rational function with no poles on `U` is the germ
of a regular function on `U`.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.exists_algebraMap_stalk_eq_of_ord_nonneg`: at a
  codimension-one point whose local ring is a discrete valuation ring, a rational function of
  nonnegative order lies in that local ring;
* `TauCeti.AlgebraicGeometry.Scheme.exists_algebraMap_stalk_eq_of_coheight_eq_zero`: at a point
  with no proper generization the local ring is already the whole function field;
* `TauCeti.AlgebraicGeometry.Scheme.exists_germToFunctionField_eq_of_ord_nonneg`: a rational
  function with nonnegative order at every codimension-one point of `U` is the germ at the generic
  point of a section of `𝒪_X` over `U`.

The last statement is the one-dimensional case of algebraic Hartogs' principle, and it is the
input that identifies the sheaf `𝒪_X(0)` of the zero divisor with the structure sheaf.

The argument follows Hartshorne, *Algebraic Geometry*, II.6.3A and Proposition II.6.11, in the
dimension-one case where the intersection of the local rings can be taken over the points of `U`
themselves. The local step is Mathlib's `IsDiscreteValuationRing.exists_lift_of_le_one` together
with `Ring.ordFrac_eq_valuation_inv`, and the global step is Mathlib's unique gluing for sheaves
on a topological space.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace
open scoped WithZero

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

noncomputable section

namespace Scheme

/-- At a codimension-one point whose local ring is a discrete valuation ring, a rational function
of nonnegative order is a section of that local ring. This is the local half of the statement that
a rational function without poles is regular. -/
theorem exists_algebraMap_stalk_eq_of_ord_nonneg {x : X}
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (hx : coheight x = 1)
    {f : X.functionField} (hf : 0 ≤ X.ord f x) :
    ∃ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g = f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, map_zero _⟩
  refine IsDiscreteValuationRing.exists_lift_of_le_one ?_
  have h1 : (1 : ℤᵐ⁰) ≤ X.ordHom x hx f := by
    simpa using (X.le_ord_iff hx hf0 (n := 0)).mp (by simpa using hf)
  simp only [_root_.AlgebraicGeometry.Scheme.ordHom, Ring.ordFrac_eq_valuation_inv] at h1
  exact (one_le_inv_iff₀.mp h1).2

omit [IsLocallyNoetherian X] in
/-- At a point with no proper generization the local ring is the whole function field: it is a
zero-dimensional local domain, hence a field, and it has the function field as its field of
fractions. -/
theorem exists_algebraMap_stalk_eq_of_coheight_eq_zero {x : X} (hx : coheight x = 0)
    (f : X.functionField) :
    ∃ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g = f := by
  have hdim : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hfield : IsField (X.presheaf.stalk x) :=
    Ring.isField_iff_maximal_bot.mpr (Ring.krullDimLE_zero_iff.mp hdim ⊥ Ideal.isPrime_bot)
  exact IsFractionRing.surjective_iff_isField.mpr hfield f

/-- **A rational function without poles is regular.** On a locally Noetherian integral scheme, let
`U` be a nonempty open subset of dimension at most one whose codimension-one local rings are
discrete valuation rings. A rational function whose order is nonnegative at every codimension-one
point of `U` is the image of a section of `𝒪_X` over `U`.

This is the one-dimensional case of algebraic Hartogs' principle. The hypothesis on the dimension
enters only through the points of `U`: at a codimension-one point the discrete valuation gives the
bound, and at a point with no proper generization the local ring is already the function field. -/
theorem exists_germToFunctionField_eq_of_ord_nonneg
    {U : X.Opens} [Nonempty U]
    (hDVR : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      IsDiscreteValuationRing (X.presheaf.stalk (y : X)))
    (hU : ∀ y ∈ U, coheight y ≤ 1) {f : X.functionField}
    (hf : ∀ (y : CodimensionOnePoint X), (y : X) ∈ U → 0 ≤ X.ord f y) :
    ∃ a : Γ(X, U), X.germToFunctionField U a = f := by
  -- The generic point lies in every nonempty open subset, so germs there see every overlap.
  have hgen : ∀ V : X.Opens, Nonempty V → genericPoint X ∈ V := fun V hV ↦
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  -- Every point of `U` has a neighbourhood inside `U` on which `f` is regular.
  have key : ∀ y : U, ∃ V : X.Opens, ∃ _ : (y : X) ∈ V, ∃ hV : V ≤ U,
      ∃ s : Γ(X, V), X.presheaf.germ V (genericPoint X) (hgen V ⟨⟨(y : X), ‹_›⟩⟩) s = f := by
    intro y
    have hg : ∃ g : X.presheaf.stalk (y : X),
        algebraMap (X.presheaf.stalk (y : X)) X.functionField g = f := by
      rcases eq_or_lt_of_le (hU y y.2) with hy | hy
      · have : IsDiscreteValuationRing (X.presheaf.stalk (y : X)) :=
          hDVR ⟨(y : X), hy⟩ y.2
        exact exists_algebraMap_stalk_eq_of_ord_nonneg hy (hf ⟨(y : X), hy⟩ y.2)
      · exact exists_algebraMap_stalk_eq_of_coheight_eq_zero (Order.lt_one_iff.mp hy) f
    obtain ⟨g, hgf⟩ := hg
    obtain ⟨W, hyW, s, hs⟩ := X.presheaf.exists_germ_eq g
    have hmem : (y : X) ∈ (W ⊓ U : X.Opens) := ⟨hyW, y.2⟩
    have hWU : Nonempty (W ⊓ U : X.Opens) := ⟨⟨(y : X), hmem⟩⟩
    -- Only needed as an instance, so that `algebraMap_germ_eq_germToFunctionField` applies at `W`.
    have : Nonempty W := ⟨⟨(y : X), hyW⟩⟩
    refine ⟨W ⊓ U, hmem, inf_le_right, X.presheaf.map (homOfLE inf_le_left).op s, ?_⟩
    rw [X.presheaf.germ_res_apply (homOfLE (inf_le_left : W ⊓ U ≤ W)) (genericPoint X)
      (hgen _ hWU) s, ← hgf, ← hs]
    exact (_root_.AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField X hyW s).symm
  choose V hyV hVU s hs using key
  -- The chosen local regular functions agree on overlaps, since they all have germ `f`.
  have hne : ∀ y : U, Nonempty (V y) := fun y ↦ ⟨⟨(y : X), hyV y⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V s := by
    intro y z
    have hyz : Nonempty (V y ⊓ V z : X.Opens) :=
      ⟨⟨genericPoint X, hgen _ (hne y), hgen _ (hne z)⟩⟩
    refine X.germToFunctionField_injective (V y ⊓ V z) ?_
    rw [X.presheaf.germ_res_apply (Opens.infLELeft (V y) (V z)) (genericPoint X)
        (hgen _ hyz) (s y),
      X.presheaf.germ_res_apply (Opens.infLERight (V y) (V z)) (genericPoint X)
        (hgen _ hyz) (s z)]
    exact (hs y).trans (hs z).symm
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' V U (fun y ↦ homOfLE (hVU y))
    (fun y hy ↦ Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩) s hcompat
  obtain ⟨y⟩ := ‹Nonempty U›
  refine ⟨a, ?_⟩
  -- `ha` is phrased through `X.sheaf`, whose underlying presheaf is `X.presheaf`; naming the
  -- restriction identity with its `X.presheaf` type keeps the rewrites below type-correct.
  have hres : X.presheaf.map (homOfLE (hVU y)).op a = s y := ha y
  rw [← hs y, ← hres,
    X.presheaf.germ_res_apply (homOfLE (hVU y)) (genericPoint X) (hgen _ (hne y)) a]

end Scheme

end

end AlgebraicGeometry

end TauCeti
