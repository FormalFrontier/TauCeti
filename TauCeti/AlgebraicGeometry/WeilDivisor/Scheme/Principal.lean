/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Principal divisors on Noetherian integral schemes

For a Noetherian integral scheme `X`, this file combines Mathlib's local orders of vanishing into
the global order system on the codimension-one points of `X`. The only global issue is finite
support. A nonzero rational function is a unit on some nonempty affine open `U`; its order
therefore vanishes on `U`. The codimension-one points outside `U` are finite: each is the generic
point of one of the finitely many irreducible pieces of the closed complement.

The main results are:

* `SchemeWeilDivisor.finite_setOfPred_not_mem`: a nonempty open misses only finitely many
  codimension-one points;
* `SchemeWeilDivisor.finite_support_orderAt`: the orders of a nonzero rational function have
  finite support;
* `WeilDivisor.OrderSystem.ofScheme`: the resulting order system, whose generic
  `OrderSystem.principalDivisor` is the scheme-theoretic principal divisor.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "principal divisors" in
"Divisors on a curve". It completes the global step explicitly left open by
`TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Order.lean`. The proof reuses Mathlib's
`exists_isUnit_germ_eq`, `Scheme.ord_of_isUnit`, and the decomposition of a closed subset
of a Noetherian space into finitely many irreducible closed subsets. No formalization is vendored.
-/

public section

open AlgebraicGeometry Order TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}}

noncomputable section

/-- A nonempty open subset of an irreducible scheme with Noetherian underlying space contains all
but finitely many codimension-one points. -/
lemma finite_setOfPred_not_mem [IrreducibleSpace X] [NoetherianSpace X]
    (U : X.Opens) [Nonempty U] :
    {x : CodimensionOnePoint X | (x : X) ∉ U}.Finite := by
  obtain ⟨S, hSfinite, hSclosed, hSirreducible, hSunion⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  let g : S → X := fun T ↦ (hSirreducible T T.property).genericPoint
  have hfiniteRange : (Set.range g).Finite := by
    letI : Finite S := hSfinite.to_subtype
    exact Set.finite_range g
  apply Set.Finite.of_finite_image
  · refine hfiniteRange.subset ?_
    rintro _ ⟨x, hxU, rfl⟩
    have hxUnion : (x : X) ∈ ⋃₀ S := by
      rw [← hSunion]
      exact hxU
    obtain ⟨T, hTS, hxT⟩ := Set.mem_sUnion.mp hxUnion
    let T' : S := ⟨T, hTS⟩
    let y : X := g T'
    have hyGeneric : IsGenericPoint y T := by
      dsimp only [y, g, T']
      exact (hSirreducible T hTS).isGenericPoint_genericPoint (hSclosed T hTS)
    have hxy : (x : X) = y := by
      by_contra hne
      have hxylt : (x : X) < y := by
        refine ⟨hyGeneric.specializes hxT, ?_⟩
        intro hyx
        exact hne (Inseparable.eq <| inseparable_iff_specializes_and.mpr
          ⟨hyx, hyGeneric.specializes hxT⟩)
      have hyCoheight : coheight y = 0 :=
        Order.lt_one_iff.mp <| (Order.coheight_eq_coe_iff.mp x.property).2.2 y hxylt
      have hyMax : IsMax y := Order.coheight_eq_zero.mp hyCoheight
      have hyη : y ≤ genericPoint X := genericPoint_specializes y
      have hηy : genericPoint X ≤ y := hyMax hyη
      have hyEqη : y = genericPoint X :=
        Inseparable.eq <| inseparable_iff_specializes_and.mpr ⟨hηy, hyη⟩
      have hηU : genericPoint X ∈ U :=
        (genericPoint_spec X).mem_open_set_iff U.isOpen |>.mpr <| by
          obtain ⟨u⟩ := (inferInstance : Nonempty U)
          exact ⟨u.1, Set.mem_univ _, u.property⟩
      have hTcompl : T ⊆ (U : Set X)ᶜ := by
        rw [hSunion]
        exact Set.subset_sUnion_of_mem hTS
      exact hTcompl hyGeneric.mem (hyEqη.symm ▸ hηU)
    exact ⟨T', hxy.symm⟩
  · exact Set.injOn_of_injective Subtype.val_injective

variable [IsIntegral X] [IsNoetherian X]

/-- The orders of a nonzero rational function on a Noetherian integral scheme are nonzero at only
finitely many codimension-one points. -/
lemma finite_support_orderAt (f : Additive X.functionFieldˣ) :
    (Function.support fun x : CodimensionOnePoint X ↦ orderAt x f).Finite := by
  obtain ⟨U, _, a, hU, ha, haUnit⟩ :=
    exists_isUnit_germ_eq X ((Additive.toMul f : X.functionFieldˣ) : X.functionField)
      (Units.ne_zero _)
  letI : Nonempty U := hU
  refine (finite_setOfPred_not_mem U).subset ?_
  intro x hx
  simp only [Set.mem_ofPred_eq]
  intro hxU
  exact hx <| by
    simpa only [orderAt_apply, ← ha] using X.ord_of_isUnit haUnit hxU

end

end SchemeWeilDivisor

namespace WeilDivisor.OrderSystem

/-- The orders of vanishing of nonzero rational functions at codimension-one points, assembled
into the order system whose principal divisors are scheme-theoretic Weil divisors. -/
noncomputable def ofScheme (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X] :
    OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ) where
  ord := SchemeWeilDivisor.orderAt
  finite_support := SchemeWeilDivisor.finite_support_orderAt

/-- The order map in the scheme-theoretic order system is the locally defined order map. -/
@[simp]
lemma ofScheme_ord {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (x : CodimensionOnePoint X) :
    (ofScheme X).ord x = SchemeWeilDivisor.orderAt x :=
  (rfl)

end WeilDivisor.OrderSystem

end AlgebraicGeometry

end TauCeti
