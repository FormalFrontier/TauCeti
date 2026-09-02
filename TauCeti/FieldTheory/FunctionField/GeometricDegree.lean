/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.PrimitiveElement
public import TauCeti.FieldTheory.Minpoly.IsIntegrallyClosedIn

/-!
# The geometric degree of an extension of function fields

Let `F' / k'` be a finite extension of an algebraic function field `F / k`, so that `k'` is the
constant field upstairs and `k` the constant field downstairs.  The two degrees `[F' : F]` and
`[k' : k]` are related through the **compositum** `F · k'`, formed inside `F'`: the tower
`F ⊆ F·k' ⊆ F'` splits `[F' : F]` as `[F·k' : F] · [F' : F·k']`, and the second factor is the
**geometric degree** `n(F'/F)`, the degree of the extension after the constants have been
absorbed.

When `F` and `k'` are linearly disjoint over `k` this reads `[F' : F] = n(F'/F) · [k' : k]`.  The
hypothesis is carried here in the degree form `[F·k' : F] = [k' : k]`; that equality is equivalent
to linear disjointness when `k' / k` is finite and `k` sits in both `F` and `k'` compatibly with
the two routes into `F'`, and without those provisos it can hold for want of content, both sides
being `0`.  In particular `[k' : k]` divides `[F' : F]`, which is what turns the cross-multiplied
degree identity `[k' : k] · deg (Con D) = [F' : F] · deg D` for the conorm into
`deg (Con D) = n(F'/F) · deg D`.

Linear disjointness is not automatic; it is what an inseparable constant field extension can
destroy.  It does hold whenever `k' / k` is finite separable and `k` is the exact constant field
of `F`, and that is proved here from
`TauCeti.IntermediateField.finrank_adjoin_simple_eq_finrank_adjoin_simple_of_isIntegrallyClosedIn`.
Mathlib's predicate `IntermediateField.LinearDisjoint` also supplies the degree equality, through
`TauCeti.finrank_constantCompositum_eq_finrank_of_linearDisjoint`.

## Main definitions

* `TauCeti.constantCompositum`: the compositum `F · k'` inside `F'`.
* `TauCeti.geometricDegree`: the geometric degree `n(F'/F) = [F' : F·k']`.

## Main results

* `TauCeti.finrank_constantCompositum_mul_geometricDegree`: the tower law
  `[F·k' : F] · n(F'/F) = [F' : F]`.
* `TauCeti.finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq`:
  `[F' : F] = n(F'/F) · [k' : k]` when adjoining the constants to `F` costs `[k' : k]`, and
  `TauCeti.finrank_dvd_finrank_of_finrank_constantCompositum_eq` for the divisibility it contains.
* `TauCeti.finrank_constantCompositum_eq_finrank_of_isSeparable`: that degree equality holds for a
  finite separable constant field extension over an exact constant field.
* `TauCeti.finrank_constantCompositum_eq_finrank_of_linearDisjoint`: it also follows from
  `IntermediateField.LinearDisjoint`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6: the degree form `[F·k' : F] = [k' : k]` extracted from Proposition 3.6.1(b) (whose
  own statement, the persistence over `k'` of linear independence over `k`, is not formalized here)
  is `TauCeti.finrank_constantCompositum_eq_finrank_of_isSeparable`, the geometric degree
  `[F' : F·k']` is the factor appearing in Corollary 3.6.4, and the splitting
  `[F' : F] = n(F'/F) · [k' : k]` is the companion of Proposition 3.6.6.  Section III.1
  (Corollary 3.1.14) is the cross-multiplied conorm identity this feeds, in
  `TauCeti.FieldTheory.FunctionField.Divisor.Conorm`.

## Implementation notes

The two lemmas that *use* the hypothesis `[F·k' : F] = [k' : k]`,
`TauCeti.finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq` and
`TauCeti.finrank_dvd_finrank_of_finrank_constantCompositum_eq`, are arithmetic in the tower
`F ⊆ F·k' ⊆ F'` and assume no relation between `k` and `F`, because Lean's `unusedSectionVars`
linter — which this repository enforces and does not disable — rejects a statement carrying
instances that appear neither in it nor in its proof.  The remaining three declarations of that
section — `TauCeti.constantCompositum_eq_adjoin_simple`,
`TauCeti.finrank_constantCompositum_eq_finrank_of_linearDisjoint` and
`TauCeti.finrank_constantCompositum_eq_finrank_of_isSeparable`, where linear disjointness is
*established* — are stated over the compatible tower `k → F → F'`, `k → k' → F'`, as is the
consumer `TauCeti.Divisor.degree_conorm`.
-/

public section

open IntermediateField TauCeti.IntermediateField

namespace TauCeti

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

/-
Proved by `(rfl)`, not `rfl`: the body of `constantCompositum` is not `@[expose]`d, so the equation
is definitional only inside this module, and downstream consumers need this lemma to connect the
compositum to `IntermediateField.adjoin`.
-/
/-- The defining equation of the compositum `F · k'`: it is `F` with the constants of `F'`
adjoined. -/
theorem constantCompositum_def :
    constantCompositum F k' F' = IntermediateField.adjoin F (Set.range (algebraMap k' F')) :=
  (rfl)

/-- The universal property of the compositum `F · k'`: it is the least intermediate field of
`F' / F` containing every constant. -/
@[simp]
theorem constantCompositum_le_iff {K : IntermediateField F F'} :
    constantCompositum F k' F' ≤ K ↔ ∀ c : k', algebraMap k' F' c ∈ K := by
  simp [constantCompositum_def, IntermediateField.adjoin_le_iff, Set.range_subset_iff]

/-- The **geometric degree** `n(F'/F)` of a finite extension `F' / k'` of the function field
`F / k`: the degree of `F'` over the compositum `F · k'`, that is, the degree of the extension
once the constants of `F'` have been adjoined to `F`.

Under linear disjointness of `F` and `k'` over `k` it is the quotient `[F' : F] / [k' : k]`; see
`TauCeti.finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq`.  It is the
factor `[F' : F·k']` by which the conorm multiplies degrees in Stichtenoth's Corollary 3.6.4. -/
noncomputable def geometricDegree : ℕ :=
  Module.finrank (constantCompositum F k' F') F'

/-
Proved by `(rfl)`, not `rfl`: the body of `geometricDegree` is not `@[expose]`d, so the equation is
definitional only inside this module, and downstream consumers need this lemma to pin the value.
-/
/-- The defining equation of the geometric degree: `n(F'/F)` is the degree of `F'` over the
compositum `F · k'`. -/
theorem geometricDegree_def :
    geometricDegree F k' F' = Module.finrank (constantCompositum F k' F') F' :=
  (rfl)

/-- The tower law for the compositum: `[F·k' : F] · n(F'/F) = [F' : F]`. -/
theorem finrank_constantCompositum_mul_geometricDegree :
    Module.finrank F (constantCompositum F k' F') * geometricDegree F k' F' =
      Module.finrank F F' := by
  rw [geometricDegree_def]
  exact Module.finrank_mul_finrank ..

/-- The geometric degree of a finite extension is positive. -/
theorem geometricDegree_pos [FiniteDimensional F F'] : 0 < geometricDegree F k' F' := by
  have : FiniteDimensional (constantCompositum F k' F') F' :=
    FiniteDimensional.right F (constantCompositum F k' F') F'
  rw [geometricDegree_def]
  exact Module.finrank_pos

end Compositum

/-! ### Linear disjointness from the constant field -/

section LinearDisjoint

variable [Algebra k k'] [Algebra k' F'] [Algebra F F'] (F k' F')

/-- **The degree of a function field extension in terms of its geometric degree**: if adjoining
the constants of `F'` to `F` costs exactly `[k' : k]`, then `[F' : F] = n(F'/F) · [k' : k]`.

The hypothesis `h` is the degree form of the linear-disjointness condition on `F` and `k'` over
`k`; it is that condition in the situation where `k` sits in both `F` and `k'` compatibly with the
two routes into `F'`, where `TauCeti.finrank_constantCompositum_eq_finrank_of_linearDisjoint`
derives it from `IntermediateField.LinearDisjoint`.  That is the situation of
`TauCeti.finrank_constantCompositum_eq_finrank_of_isSeparable`, where `h` is proved, and of
`TauCeti.Divisor.degree_conorm`, where it is consumed.  Establishing `h` is where that
compatibility does the work, and where the condition can fail — an inseparable `k' / k` can
destroy it.  Deducing the degree identity from `h` is arithmetic in the tower `F ⊆ F·k' ⊆ F'`
alone, so no scalar tower relating `k` to `F` is assumed here: assuming one would leave it unused
in the proof and in the statement.

This is the companion of Stichtenoth's Proposition 3.6.6, which splits `[F' : F]` the same way. -/
theorem finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq
    (h : Module.finrank F (constantCompositum F k' F') = Module.finrank k k') :
    Module.finrank F F' = geometricDegree F k' F' * Module.finrank k k' := by
  rw [← finrank_constantCompositum_mul_geometricDegree F k' F', h, mul_comm]

/-- **The degree of the constant field extension divides the degree of the function field
extension**, under the same hypothesis as
`TauCeti.finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq` — the degree form
of the linear-disjointness condition on `F` and `k'` over `k`; the quotient is the geometric
degree. -/
theorem finrank_dvd_finrank_of_finrank_constantCompositum_eq
    (h : Module.finrank F (constantCompositum F k' F') = Module.finrank k k') :
    Module.finrank k k' ∣ Module.finrank F F' :=
  ⟨geometricDegree F k' F', by
    rw [finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq F k' F' h,
      mul_comm]⟩

variable [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- **The compositum is generated by a primitive element of the constant field extension**: if `β`
generates `k' / k`, then `F · k'` is `F` with the image of `β` adjoined. -/
theorem constantCompositum_eq_adjoin_simple {β : k'} (hβ : k⟮β⟯ = ⊤) :
    constantCompositum F k' F' = F⟮algebraMap k' F' β⟯ := by
  set α := algebraMap k' F' β with hα
  have hrange : Set.range (algebraMap k' F') = (k⟮α⟯ : IntermediateField k F') := by
    rw [← IsScalarTower.toAlgHom_fieldRange k k' F', AlgHom.fieldRange_eq_map, ← hβ,
      IntermediateField.adjoin_map]
    simp [hα]
  have hle : k⟮α⟯ ≤ (F⟮α⟯).restrictScalars k :=
    adjoin_simple_le_iff.2 ((mem_restrictScalars k).2 (mem_adjoin_simple_self F α))
  refine le_antisymm ((constantCompositum_le_iff F k' F').2 fun c ↦ ?_)
    (adjoin_simple_le_iff.2 (algebraMap_mem_constantCompositum F k' F' β))
  have hc : algebraMap k' F' c ∈ k⟮α⟯ := hrange.le (Set.mem_range_self c)
  exact (mem_restrictScalars k).1 (hle hc)

/-- **Mathlib's linear disjointness implies the degree hypothesis**: if the constants of `F'` and
the lower function field `F` are linearly disjoint over `k` in the sense of
`IntermediateField.LinearDisjoint`, and `k' / k` is algebraic, then adjoining the constants to `F`
costs exactly `[k' : k]`.

This is the bridge from Mathlib's predicate to the degree form `[F·k' : F] = [k' : k]` in which the
hypothesis is carried by
`TauCeti.finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq`,
`TauCeti.finrank_dvd_finrank_of_finrank_constantCompositum_eq` and
`TauCeti.Divisor.degree_conorm`. -/
theorem finrank_constantCompositum_eq_finrank_of_linearDisjoint [Algebra.IsAlgebraic k k']
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F) :
    Module.finrank F (constantCompositum F k' F') = Module.finrank k k' := by
  have e := (IsScalarTower.toAlgHom k k' F').equivFieldRange
  have halg : Algebra.IsAlgebraic k (IsScalarTower.toAlgHom k k' F').fieldRange := e.isAlgebraic
  have hrank := H.adjoin_rank_eq_rank_left_of_isAlgebraic (.inl halg)
  rw [constantCompositum_def, ← IsScalarTower.toAlgHom_fieldRange k k' F',
    e.toLinearEquiv.finrank_eq]
  exact congrArg Cardinal.toNat hrank

/-- **Adjoining a finite separable constant field extension to the lower function field costs
exactly its degree**, provided the constant field downstairs is exact: `[F·k' : F] = [k' : k]`,
which is the degree form of linear disjointness of `F` and `k'` over `k`.

This is the degree consequence of Stichtenoth's Proposition 3.6.1(b); that proposition's own
statement — the persistence over `k'` of linear independence over `k` — is stronger and is not
formalized here.

This is the statement in which that condition has content, and it is stated over the full
compatible tower: `k` embeds in `F` and in `k'`, and the two routes `k → F → F'` and `k → k' → F'`
agree.  Both hypotheses are used: exactness of `k` in `F` keeps the minimal polynomial of a
constant irreducible over `F` (`TauCeti.minpoly.map_algebraMap_of_isIntegrallyClosedIn`), and
separability makes `k' / k` simple, so that a single such minimal polynomial computes the whole
degree. -/
theorem finrank_constantCompositum_eq_finrank_of_isSeparable (hex : IsIntegrallyClosedIn k F)
    [FiniteDimensional k k'] [Algebra.IsSeparable k k'] :
    Module.finrank F (constantCompositum F k' F') = Module.finrank k k' := by
  -- separability makes `k' / k` simple: let `β` generate it, and work with its image in `F'`
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element k k'
  have hβint : IsIntegral k β := Algebra.IsIntegral.isIntegral β
  have hαint : IsIntegral k (algebraMap k' F' β) := hβint.map (IsScalarTower.toAlgHom k k' F')
  have hminpoly : minpoly k (algebraMap k' F' β) = minpoly k β :=
    minpoly.algebraMap_eq (algebraMap k' F').injective β
  calc Module.finrank F (constantCompositum F k' F')
      -- the compositum is `F` with the image of the generator adjoined
      = Module.finrank F F⟮algebraMap k' F' β⟯ := by
        rw [constantCompositum_eq_adjoin_simple F k' F' hβ]
      -- exactness of `k` in `F`: adjoining a constant costs the same over `F` as over `k`
    _ = Module.finrank k k⟮algebraMap k' F' β⟯ :=
        finrank_adjoin_simple_eq_finrank_adjoin_simple_of_isIntegrallyClosedIn hex hαint
      -- both degrees are the degree of the minimal polynomial of the generator, which the
      -- embedding `k' → F'` does not change
    _ = (minpoly k β).natDegree := by rw [adjoin.finrank hαint, hminpoly]
    _ = Module.finrank k k⟮β⟯ := (adjoin.finrank hβint).symm
      -- and `β` generates `k'`
    _ = Module.finrank k k' := by rw [hβ, IntermediateField.finrank_top']

end LinearDisjoint

end TauCeti
