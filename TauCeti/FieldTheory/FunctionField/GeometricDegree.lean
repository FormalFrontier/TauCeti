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

## Implementation notes

Only `TauCeti.finrank_constantCompositum_eq_finrank`, where linear disjointness is *established*,
is stated over the compatible tower `k → F → F'`, `k → k' → F'`; so is its consumer
`TauCeti.Divisor.degree_conorm`.  The two lemmas that *use* the hypothesis
`[F·k' : F] = [k' : k]` are arithmetic in the tower `F ⊆ F·k' ⊆ F'` and assume no relation
between `k` and `F`, because Lean's `unusedSectionVars` linter — which this repository enforces
and does not disable — rejects a statement carrying instances that appear neither in it nor in
its proof.
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

/-- **The degree of a function field extension in terms of its geometric degree**: if adjoining
the constants of `F'` to `F` costs exactly `[k' : k]`, then `[F' : F] = n(F'/F) · [k' : k]`.

The hypothesis `h` is the degree form of linear disjointness of `F` and `k'` over `k`; it is that
condition in the situation where `k` sits in both `F` and `k'` compatibly with the two routes into
`F'`, which is the situation of `TauCeti.finrank_constantCompositum_eq_finrank`, where `h` is
proved, and of `TauCeti.Divisor.degree_conorm`, where it is consumed.  Establishing `h` is where
that compatibility does the work, and where the condition can fail — an inseparable `k' / k` can
destroy it.  Deducing the degree identity from `h` is arithmetic in the tower `F ⊆ F·k' ⊆ F'`
alone, so no scalar tower relating `k` to `F` is assumed here: assuming one would leave it unused
in the proof and in the statement. -/
theorem finrank_eq_geometricDegree_mul
    (h : Module.finrank F (constantCompositum F k' F') = Module.finrank k k') :
    Module.finrank F F' = geometricDegree F k' F' * Module.finrank k k' := by
  rw [← finrank_constantCompositum_mul_geometricDegree F k' F', h, mul_comm]

/-- **The degree of the constant field extension divides the degree of the function field
extension**, under the same hypothesis as `TauCeti.finrank_eq_geometricDegree_mul` — the degree
form of linear disjointness of `F` and `k'` over `k`; the quotient is the geometric degree. -/
theorem finrank_dvd_finrank
    (h : Module.finrank F (constantCompositum F k' F') = Module.finrank k k') :
    Module.finrank k k' ∣ Module.finrank F F' :=
  ⟨geometricDegree F k' F', by rw [finrank_eq_geometricDegree_mul F k' F' h, mul_comm]⟩

variable [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- **A finite separable constant field extension is linearly disjoint from the lower function
field**, provided the constant field downstairs is exact: adjoining the constants of `F'` to `F`
costs exactly `[k' : k]`.

This is the statement in which linear disjointness has content, and it is stated over the full
compatible tower: `k` embeds in `F` and in `k'`, and the two routes `k → F → F'` and `k → k' → F'`
agree.  Both hypotheses are used: exactness of `k` in `F` keeps the minimal polynomial of a
constant irreducible over `F` (`TauCeti.map_minpoly_eq_minpoly`), and separability makes `k' / k`
simple, so that a single such minimal polynomial computes the whole degree. -/
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
