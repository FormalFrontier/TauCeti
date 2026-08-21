/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Restriction
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.Symmetric.Dominance
public import TauCeti.RepresentationTheory.Symmetric.Factorization
public import TauCeti.RepresentationTheory.Symmetric.Specht.Module

/-!
# James's submodule theorem, and the irreducibility of the Specht module

Every subrepresentation `U` of the Young permutation module `M^μ` is comparable with the Specht
module `S^μ` in a very strong sense: either `S^μ ≤ U`, or `U` is orthogonal to `S^μ` for the
tabloid form.  This dichotomy is **James's submodule theorem**, and it is proved here
(`TauCeti.spechtSubrepresentation_le_or_le_orthogonal`).  Since the tabloid form is positive
definite, the two alternatives overlap only on the zero subrepresentation, so the theorem
immediately makes `S^μ` an atom of the lattice of subrepresentations of `M^μ`, hence irreducible.

The engine is the behaviour of the column antisymmetrizer `b_t` on a single tabloid, which is
James's Lemma 4.6: `b_t · {s}` is either `0` or `± e_t`
(`TauCeti.YoungTableau.exists_eq_smul_polytabloid_single`).  Writing `{s} = σ · {t}`, the two cases
are exactly the two cases of the row/column criterion of
`TauCeti.RepresentationTheory.Symmetric.Vanishing`, read with the roles of the two tableaux
exchanged.

* If a row of `relabel σ t` meets a column of `t` in two distinct labels `x ≠ y`, then the
  transposition of `x` and `y` lies in the column group of `t` while fixing the tabloid `{s}`, so
  pushing it across turns `b_t · {s}` into its own negative and kills it.
* Otherwise the row-column factorization of
  `TauCeti.RepresentationTheory.Symmetric.Factorization` writes `σ⁻¹ = p q` with `p` in the row
  group and `q` in the column group of `t`.  The row group is the stabilizer of `{t}`, so
  `{s} = q⁻¹ · {t}`, and `b_t` absorbs `q⁻¹` through its sign: `b_t · {s} = sign q • e_t`.

By linearity the same holds for an arbitrary vector of `M^μ`
(`TauCeti.YoungTableau.exists_eq_smul_polytabloid`), and that is the dichotomy.  Given a
subrepresentation `U`, either some `b_t` fails to annihilate some vector of `U` -- and then `e_t`
itself lies in `U`, and with it the span of its orbit, which is all of `S^μ` -- or every `b_t`
annihilates every vector of `U`, and then `U` is orthogonal to every polytabloid, because `b_t` is
self-adjoint for the tabloid form
(`TauCeti.YoungTableau.tabloidForm_asAlgebraHom_columnAntisymmetrizer`) and `e_t = b_t · {t}`.

The dimension of `S^μ`, the standard basis of polytabloids indexing it, and the statement that
the `S^μ` exhaust the irreducibles of `Sₙ` and are pairwise non-isomorphic are separate targets and
are not proved here.  Neither is the comparison of `S^μ` with the left ideal `ℚ[Sₙ] c_t`, which is
irreducible by
`TauCeti.YoungTableau.isIrreducible_spechtIdealRep` through an argument that shares the row-column
factorization but not the tabloid form.

## Main results

* `TauCeti.YoungTableau.exists_eq_smul_polytabloid_single`: the column antisymmetrizer sends a
  tabloid to a multiple of the polytabloid (James's Lemma 4.6), and
  `TauCeti.YoungTableau.exists_eq_smul_polytabloid` extends this to all of `M^μ`.
* `TauCeti.YoungTableau.tabloidForm_asAlgebraHom_columnAntisymmetrizer`: the column
  antisymmetrizer is self-adjoint for the tabloid form.
* `TauCeti.spechtSubrepresentation_le_or_le_orthogonal`: **James's submodule theorem**.
* `TauCeti.isAtom_spechtSubrepresentation` and `TauCeti.isIrreducible_spechtSubrepresentation`:
  the Specht module is a minimal subrepresentation of `M^μ`, hence irreducible, with
  `TauCeti.isIrreducible_spechtModule` the partition-indexed form.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 4:
  Lemma 4.6, the submodule theorem 4.8, and Corollary 4.9.
* B. E. Sagan, *The Symmetric Group*, 2nd ed. (2001), Section 2.4.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 3, "The submodule theorem (James)", and Layer 4, "Irreducibility".
-/

public section

namespace TauCeti

open scoped BigOperators

namespace YoungTableau

variable {μ : YoungDiagram}

/-- Classical decidability of membership in the column group, used to form its finite sum, as in
`TauCeti/RepresentationTheory/Symmetric/Symmetrizer.lean`. -/
noncomputable local instance (t : YoungTableau μ) : DecidablePred (· ∈ colSubgroup t) :=
  Classical.decPred _

/-! ### James's lemma: the column antisymmetrizer of a tabloid -/

/-- When no row of `s` meets a column of `t` twice, the column antisymmetrizer of `t` sends the
tabloid of `s` to a signed multiple of the polytabloid `e_t`, the sign being that of some
permutation. -/
private theorem exists_asAlgebraHom_columnAntisymmetrizer_single_eq_sign_smul
    (s t : YoungTableau μ) (h : ¬ RowMeetsColumnTwice s t) :
    ∃ q : Equiv.Perm (Fin μ.card),
      (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t)
        (MonoidAlgebra.single (tabloid s) 1)
          = ((Equiv.Perm.sign q : ℤ) : ℚ) • polytabloid t := by
  -- Writing `s = relabel σ t`, the permutation `σ⁻¹` factors as a row permutation times a
  -- column permutation; the row part fixes `{t}`, and `b_t` absorbs the column part `q⁻¹` by
  -- its sign.
  obtain ⟨σ, rfl⟩ := exists_relabel_eq t s
  rw [rowMeetsColumnTwice_relabel_left_iff] at h
  obtain ⟨p, hp, q, hq, hpq⟩ := Set.mem_mul.mp (mem_mul_of_not_rowMeetsColumnTwice h)
  have hσ : σ = q⁻¹ * p⁻¹ := by rw [← mul_inv_rev, hpq, inv_inv]
  refine ⟨q, ?_⟩
  have htab : MonoidAlgebra.single (tabloid (relabel σ t)) (1 : ℚ) =
      (permutationModule (shapePartition μ)).ρ q⁻¹
        (MonoidAlgebra.single (tabloid t) 1) := by
    rw [Representation.ofMulAction_single, tabloid_relabel, hσ, mul_smul,
      smul_tabloid_eq_self_iff.mpr (inv_mem (SetLike.mem_coe.mp hp))]
  rw [htab, ← Representation.asAlgebraHom_single_one (permutationModule (shapePartition μ)).ρ,
    ← Module.End.mul_apply, ← map_mul,
    mul_columnAntisymmetrizer_right t ⟨q⁻¹, inv_mem (SetLike.mem_coe.mp hq)⟩,
    Equiv.Perm.sign_inv, map_smul, LinearMap.smul_apply, ← polytabloid_def]

/-- **James's Lemma 4.6.**  The column antisymmetrizer of `t` sends a `μ`-tabloid to a rational
multiple of the polytabloid `e_t`; the multiple is `0` or a sign.

The tabloid is `σ · {t}` for some `σ`, and the two cases are the two cases of the row/column
criterion: if a row of `relabel σ t` meets a column of `t` twice the transposition of the two
shared labels fixes the tabloid while `b_t` sees its sign, and otherwise `σ⁻¹` factors through the
row and column groups of `t`, of which the row part fixes `{t}`. -/
theorem exists_eq_smul_polytabloid_single (t : YoungTableau μ)
    (T : Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ)) :
    ∃ κ : ℚ, (κ = 0 ∨ κ = 1 ∨ κ = -1) ∧
      (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t)
          (MonoidAlgebra.single T 1) = κ • polytabloid t := by
  obtain ⟨s, rfl⟩ := tabloid_surjective T
  by_cases h : RowMeetsColumnTwice s t
  · -- The transposition of the two shared labels is an odd element of the column group of `t`
    -- fixing the tabloid of `s`, which is exactly the hypothesis of the general vanishing lemma.
    obtain ⟨x, y, hxy, hrow, hcol⟩ := (rowMeetsColumnTwice_def _ _).mp h
    exact ⟨0, Or.inl rfl, by
      rw [zero_smul]
      exact asAlgebraHom_columnAntisymmetrizer_single_eq_zero t (shapePartition μ) (tabloid s)
        (swap_mem_colSubgroup hcol) (Equiv.Perm.sign_swap hxy)
        (smul_tabloid_eq_self_iff.mpr (swap_mem_rowSubgroup hrow))⟩
  · obtain ⟨q, hq⟩ := exists_asAlgebraHom_columnAntisymmetrizer_single_eq_sign_smul s t h
    exact ⟨_, Or.inr (by rcases Int.units_eq_one_or (Equiv.Perm.sign q) with h | h <;> simp [h]),
      hq⟩

/-- **The column antisymmetrizer collapses `M^μ` onto the line spanned by the polytabloid.**  This
is the linear extension of `TauCeti.YoungTableau.exists_eq_smul_polytabloid_single` from the
tabloid basis to the whole Young permutation module. -/
theorem exists_eq_smul_polytabloid (t : YoungTableau μ)
    (v : (permutationModule (shapePartition μ)).V) :
    ∃ κ : ℚ,
      (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t) v =
        κ • polytabloid t := by
  have hv : v ∈ Submodule.span ℚ (Set.range (permutationModuleBasis (shapePartition μ))) := by
    rw [Module.Basis.span_eq]
    exact Submodule.mem_top
  have hspan : (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t) v ∈
      Submodule.span ℚ {polytabloid t} := by
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨T, rfl⟩ := hw
      obtain ⟨κ, -, hκ⟩ := exists_eq_smul_polytabloid_single t T
      rw [MonoidAlgebra.basis_apply, hκ]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  obtain ⟨κ, hκ⟩ := Submodule.mem_span_singleton.mp hspan
  exact ⟨κ, hκ.symm⟩

/-! ### Self-adjointness of the column antisymmetrizer -/

/-- **The column antisymmetrizer is self-adjoint for the tabloid form.**  The symmetric group acts
on `M^μ` by isometries, so moving a permutation across the form inverts it, and inversion is a
sign-preserving involution of the column group. -/
theorem tabloidForm_asAlgebraHom_columnAntisymmetrizer (t : YoungTableau μ)
    (v w : (permutationModule (shapePartition μ)).V) :
    tabloidForm (shapePartition μ)
        ((permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t) v) w =
      tabloidForm (shapePartition μ) v
        ((permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t) w) := by
  rw [asAlgebraHom_columnAntisymmetrizer_apply, asAlgebraHom_columnAntisymmetrizer_apply,
    map_sum, LinearMap.sum_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.inv (colSubgroup t)) _ _ fun q => ?_
  rw [map_smul, LinearMap.smul_apply, map_smul]
  simp only [Equiv.inv_apply, InvMemClass.coe_inv, Equiv.Perm.sign_inv, smul_eq_mul]
  rw [permutationForm_ofMulAction_left]

end YoungTableau

/-! ### The submodule theorem -/

open YoungTableau

/-- **James's submodule theorem.**  A subrepresentation `U` of the Young permutation module `M^μ`
either contains the Specht module `S^μ` or is orthogonal to it for the tabloid form.

The dichotomy is whether some column antisymmetrizer `b_t` fails to annihilate some vector of `U`.
If it does fail, the value is a nonzero multiple of the polytabloid `e_t` and lies in `U`, so `U`
contains the orbit of `e_t`, which spans `S^μ`.  If every `b_t` annihilates every vector of `U`,
then self-adjointness of `b_t` moves it off each polytabloid `e_t = b_t · {t}` and onto the vector
of `U`, where it vanishes. -/
theorem spechtSubrepresentation_le_or_le_orthogonal (μ : YoungDiagram)
    (U : Subrepresentation (permutationModule (shapePartition μ)).ρ) :
    spechtSubrepresentation μ ≤ U ∨
      U ≤ orthogonalSubrepresentation (spechtSubrepresentation μ) := by
  by_cases hex : ∃ (t : YoungTableau μ) (v : (permutationModule (shapePartition μ)).V),
      v ∈ U.toSubmodule ∧
      (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t) v ≠ 0
  · obtain ⟨t, v, hvU, hne⟩ := hex
    refine Or.inl ?_
    obtain ⟨κ, hκ⟩ := exists_eq_smul_polytabloid t v
    have hκ0 : κ ≠ 0 := by
      rintro rfl
      exact hne (by rw [hκ, zero_smul])
    -- the polytabloid itself lies in `U`, after rescaling
    have hmem : polytabloid t ∈ U.toSubmodule := by
      have hsmul : κ • polytabloid t ∈ U.toSubmodule :=
        hκ ▸ Representation.asAlgebraHom_mem_of_forall_mem _ U.toSubmodule
          (fun g _ hv => U.apply_mem_toSubmodule g hv) v hvU (columnAntisymmetrizer t)
      have := U.toSubmodule.smul_mem κ⁻¹ hsmul
      rwa [smul_smul, inv_mul_cancel₀ hκ0, one_smul] at this
    -- and `U` then contains the whole orbit of the polytabloid, which spans `S^μ`
    rw [← Subrepresentation.toSubmodule_le_toSubmodule, spechtSubrepresentation_eq_span_orbit t]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨σ, rfl⟩
    exact U.apply_mem_toSubmodule σ hmem
  · push Not at hex
    refine Or.inr ?_
    rw [← Subrepresentation.toSubmodule_le_toSubmodule,
      toSubmodule_orthogonalSubrepresentation]
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [spechtSubrepresentation_toSubmodule] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      rw [polytabloid_def, tabloidForm_asAlgebraHom_columnAntisymmetrizer, hex t v hv,
        map_zero]
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul r x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

/-! ### Irreducibility -/

/-- **The Specht module is a minimal subrepresentation of `M^μ`.**  A nonzero subrepresentation
strictly inside `S^μ` would, by the submodule theorem, be orthogonal to `S^μ` while lying in it,
and the tabloid form is positive definite. -/
theorem isAtom_spechtSubrepresentation (μ : YoungDiagram) :
    IsAtom (spechtSubrepresentation μ) := by
  refine ⟨spechtSubrepresentation_ne_bot μ, fun U hU => ?_⟩
  rcases spechtSubrepresentation_le_or_le_orthogonal μ U with hle | hle
  · exact absurd (le_antisymm hU.le hle) hU.ne
  · exact le_bot_iff.mp
      ((isCompl_orthogonalSubrepresentation_permutationModule (shapePartition μ)
        (spechtSubrepresentation μ)).disjoint hU.le hle)

/-- **The Specht module is irreducible.**  This is James's Corollary 4.9 over a field of
characteristic zero, in the concrete presentation of `S^μ` as the span of the polytabloids inside
the Young permutation module. -/
theorem isIrreducible_spechtSubrepresentation (μ : YoungDiagram) :
    (spechtSubrepresentation μ).toRepresentation.IsIrreducible :=
  Representation.isIrreducible_toRepresentation_of_isAtom (isAtom_spechtSubrepresentation μ)

/-- **The Specht module of a partition is irreducible**, in the partition-indexed packaging
`TauCeti.spechtModule`.  Transporting along the relabelling `Fin n ≃ Fin (diagramOf μ).card` is an
isomorphism of groups, and restriction along an isomorphism preserves irreducibility. -/
instance isIrreducible_spechtModule {n : ℕ} (μ : n.Partition) :
    _root_.Representation.IsIrreducible (spechtModule μ).ρ :=
  (isIrreducible_comp_equiv_iff (finCongr (card_diagramOf μ).symm).permCongrHom
    (spechtSubrepresentation (diagramOf μ)).toRepresentation).mpr
    (isIrreducible_spechtSubrepresentation (diagramOf μ))

end TauCeti
