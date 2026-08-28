/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PrimitiveElement
public import TauCeti.FieldTheory.AlgebraicClosure

/-!
# The geometric degree of an extension of function fields

Let `F' / k'` be a finite extension of an algebraic function field `F / k`, so that `k'` is the
constant field upstairs and `k` the constant field downstairs.  The two degrees `[F' : F]` and
`[k' : k]` are related through the **compositum** `F · k'`, formed inside `F'`: the tower
`F ⊆ F·k' ⊆ F'` splits `[F' : F]` as `[F·k' : F] · [F' : F·k']`, and the second factor is the
**geometric degree** `n(F'/F)`, the degree of the extension after the constants have been
absorbed.

When `F` and `k'` are linearly disjoint over `k` — equivalently `[F·k' : F] = [k' : k]`, the form
in which the hypothesis is carried here — this reads `[F' : F] = n(F'/F) · [k' : k]`.  In
particular `[k' : k]` divides `[F' : F]`, which is what turns the cross-multiplied degree identity
`[k' : k] · deg (Con D) = [F' : F] · deg D` for the conorm into `deg (Con D) = n(F'/F) · deg D`.

Linear disjointness is not automatic; it is what an inseparable constant field extension can
destroy.  It does hold whenever `k' / k` is finite separable and `k` is the exact constant field
of `F`, and that is proved here from `TauCeti.finrank_adjoin_eq_finrank_adjoin`.

## Main definitions

* `TauCeti.constantCompositum`: the compositum `F · k'` inside `F'`.
* `TauCeti.geometricDegree`: the geometric degree `n(F'/F) = [F' : F·k']`.

## Main results

* `TauCeti.finrank_constantCompositum_mul_geometricDegree`: the tower law
  `[F·k' : F] · n(F'/F) = [F' : F]`.
* `TauCeti.finrank_eq_geometricDegree_mul`: `[F' : F] = n(F'/F) · [k' : k]` for linearly disjoint
  `F` and `k'`, and `TauCeti.finrank_dvd_finrank` for the divisibility it contains.
* `TauCeti.finrank_constantCompositum_eq_finrank`: linear disjointness holds for a finite
  separable constant field extension over an exact constant field.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.1.
-/

public section

namespace TauCeti

open IntermediateField

universe u u' v v'

variable {k : Type u} {F : Type v} {k' : Type u'} {F' : Type v'}
variable [Field k] [Field F] [Field k'] [Field F']

section Compositum

variable [Algebra k' F'] [Algebra F F'] (F k' F')

/-- The **compositum** `F · k'` of the lower function field `F` with the constant field `k'` of
the upper function field, formed inside `F'`: the smallest intermediate field of `F' / F`
containing the constants. -/
def constantCompositum : IntermediateField F F' :=
  IntermediateField.adjoin F (Set.range (algebraMap k' F'))

/-- Every constant of `F'` lies in the compositum `F · k'`. -/
@[simp]
theorem algebraMap_mem_constantCompositum (c : k') :
    algebraMap k' F' c ∈ constantCompositum F k' F' :=
  IntermediateField.subset_adjoin _ _ ⟨c, rfl⟩

/-- The universal property of the compositum `F · k'`: it is the least intermediate field of
`F' / F` containing every constant. -/
theorem constantCompositum_le_iff {K : IntermediateField F F'} :
    constantCompositum F k' F' ≤ K ↔ ∀ c : k', algebraMap k' F' c ∈ K := by
  simp [constantCompositum, IntermediateField.adjoin_le_iff, Set.range_subset_iff]

/-- The **geometric degree** `n(F'/F)` of a finite extension `F' / k'` of the function field
`F / k`: the degree of `F'` over the compositum `F · k'`, that is, the degree of the extension
once the constants of `F'` have been adjoined to `F`.

Under linear disjointness of `F` and `k'` over `k` it is the quotient `[F' : F] / [k' : k]`; see
`TauCeti.finrank_eq_geometricDegree_mul`. -/
noncomputable def geometricDegree : ℕ :=
  Module.finrank (constantCompositum F k' F') F'

/-- The tower law for the compositum: `[F·k' : F] · n(F'/F) = [F' : F]`. -/
theorem finrank_constantCompositum_mul_geometricDegree :
    Module.finrank F (constantCompositum F k' F') * geometricDegree F k' F' = Module.finrank F F' :=
  Module.finrank_mul_finrank ..

/-- The geometric degree of a finite extension is positive. -/
theorem geometricDegree_pos [FiniteDimensional F F'] : 0 < geometricDegree F k' F' := by
  have : FiniteDimensional (constantCompositum F k' F') F' :=
    FiniteDimensional.right F (constantCompositum F k' F') F'
  exact Module.finrank_pos

end Compositum

/-! ### Linear disjointness from the constant field -/

section LinearDisjoint

variable [Algebra k k'] [Algebra k' F'] [Algebra F F'] (F k' F')

/-- **The degree of a function field extension in terms of its geometric degree**: if `F` and the
constant field `k'` are linearly disjoint over `k`, so that the constants cost `[k' : k]` to
adjoin, then `[F' : F] = n(F'/F) · [k' : k]`.

The hypothesis is stated as the degree of the compositum, the form in which linear disjointness is
used; it can fail when `k' / k` is inseparable. -/
theorem finrank_eq_geometricDegree_mul
    (h : Module.finrank F (constantCompositum F k' F') = Module.finrank k k') :
    Module.finrank F F' = geometricDegree F k' F' * Module.finrank k k' := by
  rw [← finrank_constantCompositum_mul_geometricDegree F k' F', h, mul_comm]

/-- **The degree of the constant field extension divides the degree of the function field
extension**, for linearly disjoint `F` and `k'`; the quotient is the geometric degree. -/
theorem finrank_dvd_finrank
    (h : Module.finrank F (constantCompositum F k' F') = Module.finrank k k') :
    Module.finrank k k' ∣ Module.finrank F F' :=
  ⟨geometricDegree F k' F', by rw [finrank_eq_geometricDegree_mul F k' F' h, mul_comm]⟩

variable [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- **A finite separable constant field extension is linearly disjoint from the lower function
field**, provided the constant field downstairs is exact: adjoining the constants of `F'` to `F`
costs exactly `[k' : k]`.

Both hypotheses are used: exactness of `k` in `F` keeps the minimal polynomial of a constant
irreducible over `F` (`TauCeti.map_minpoly_eq_minpoly`), and separability makes `k' / k` simple,
so that a single such minimal polynomial computes the whole degree. -/
theorem finrank_constantCompositum_eq_finrank (hex : IsIntegrallyClosedIn k F)
    [FiniteDimensional k k'] [Algebra.IsSeparable k k'] :
    Module.finrank F (constantCompositum F k' F') = Module.finrank k k' := by
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element k k'
  set α := algebraMap k' F' β with hα
  have hβint : IsIntegral k β := Algebra.IsIntegral.isIntegral β
  have hαint : IsIntegral k α := hβint.map (IsScalarTower.toAlgHom k k' F')
  -- the compositum is generated by a primitive element of the constant field extension
  have hcomp : constantCompositum F k' F' = F⟮α⟯ := by
    have hrange : Set.range (algebraMap k' F') = (k⟮α⟯ : IntermediateField k F') := by
      rw [← IsScalarTower.toAlgHom_fieldRange k k' F', AlgHom.fieldRange_eq_map, ← hβ,
        IntermediateField.adjoin_map]
      simp [hα]
    refine le_antisymm ?_ (adjoin_simple_le_iff.2 (algebraMap_mem_constantCompositum F k' F' β))
    rw [constantCompositum, IntermediateField.adjoin_le_iff, hrange]
    have hle : k⟮α⟯ ≤ (F⟮α⟯).restrictScalars k :=
      adjoin_simple_le_iff.2 (mem_adjoin_simple_self F α)
    exact fun y hy ↦ hle hy
  rw [hcomp, finrank_adjoin_eq_finrank_adjoin hex hαint, adjoin.finrank hαint, hα,
    minpoly.algebraMap_eq (algebraMap k' F').injective β, ← adjoin.finrank hβint, hβ,
    IntermediateField.finrank_top']

end LinearDisjoint

end TauCeti
