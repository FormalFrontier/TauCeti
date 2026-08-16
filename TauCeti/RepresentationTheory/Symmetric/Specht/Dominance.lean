/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Specht.SubmoduleTheorem

/-!
# Dominance triangularity for maps out of a Specht module

A nonzero map of representations from the Specht module `S^{lam}` to the Young permutation module
`M^μ` forces the shape of `lam` to dominate `μ`
(`TauCeti.dominates_of_intertwiningMap_ne_zero`).  Equivalently, `Hom(S^{lam}, M^μ)` vanishes
unless `lam` dominates `μ`: the matrix of multiplicities of the Specht modules in the permutation
modules is triangular for the dominance order.  This is the shape-comparison half of the
classification of the Specht modules, and it is what turns James's dominance lemma of
`TauCeti/RepresentationTheory/Symmetric/Dominance.lean` into a statement about maps.

The proof has two steps beyond that lemma.

* **Off the tabloid basis.** James's dominance lemma sees the column antisymmetrizer `b_t` only on
  a single tabloid.  When `lam` fails to dominate `μ` the lemma says `b_t` kills every tabloid, so
  by linearity it kills all of `M^μ`; that extension lives beside the lemma itself, as
  `TauCeti.YoungTableau.dominates_of_asAlgebraHom_columnAntisymmetrizer_apply_ne_zero`.
* **Producing a preimage of the polytabloid inside `S^{lam}`.** The polytabloid is `e_t = b_t·{t}`,
  but the tabloid `{t}` is not in the Specht module, so `b_t` cannot be moved across a map defined
  only on `S^{lam}`.  The tabloid form supplies an invariant complement `M^{lam} = S^{lam} ⊕ W`
  (`TauCeti.isCompl_orthogonalSubrepresentation_permutationModule`); splitting `{t}` along it and
  applying `b_t` to both summands, the `W`-part lands in `S^{lam} ⊓ W = ⊥`, so the `S^{lam}`-part
  `e` already satisfies `b_t·e = e_t`
  (`TauCeti.YoungTableau.exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid`).

With those, a nonzero `f : S^{lam} → M^μ` is injective, because `S^{lam}` is irreducible, so
`f e ≠ 0` and `b_t · f e = f (b_t · e) = f e_t ≠ 0`, and the first step applies.

Combining the theorem with itself in both directions is what shows the Specht modules of distinct
shapes to be non-isomorphic; that combination needs the Specht module of a partition of `n`
presented inside the permutation module of the *same* index type `Fin n`, and is not carried out
here.

## Main results

* `TauCeti.YoungTableau.exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid`: the
  polytabloid is `b_t` applied to a vector already inside the Specht module.
* `TauCeti.dominates_of_intertwiningMap_ne_zero`: a nonzero map `S^{lam} → M^μ` forces dominance.
* `TauCeti.intertwiningMap_eq_zero_of_not_dominates`: the contrapositive, as the vanishing of the
  whole `Hom` space.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 4.
* B. E. Sagan, *The Symmetric Group*, 2nd ed. (2001), Section 2.4.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "Distinctness and completeness".
-/

public section

namespace TauCeti

open scoped BigOperators

variable {lam : YoungDiagram}

namespace YoungTableau

/-! ### A preimage of the polytabloid inside the Specht module -/

/-- **The polytabloid is already in the image of the column antisymmetrizer on `S^{lam}`.**
Splitting the tabloid `{t}` as `e + w` along the invariant orthogonal decomposition
`M^{lam} = S^{lam} ⊕ (S^{lam})ᗮ` and applying `b_t`, the two images stay in their summands while
their sum is the polytabloid `e_t`, which lies in `S^{lam}`; so the second image lies in the
intersection of the two summands and vanishes.

This is what lets `b_t` be moved across a map that is defined only on the Specht module: the
tabloid `{t}` itself is not available there, but `e` is. -/
theorem exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid (t : YoungTableau lam) :
    ∃ e ∈ (spechtSubrepresentation lam).toSubmodule,
      (permutationModule (shapePartition lam)).ρ.asAlgebraHom (columnAntisymmetrizer t) e =
        polytabloid t := by
  have hc : IsCompl (spechtSubrepresentation lam)
      (orthogonalSubrepresentation (spechtSubrepresentation lam)) :=
    isCompl_orthogonalSubrepresentation_permutationModule (shapePartition lam) _
  have hstable : ∀ (σ : Subrepresentation (permutationModule (shapePartition lam)).ρ)
      (g : Equiv.Perm (Fin lam.card)), ∀ v ∈ σ.toSubmodule,
      (permutationModule (shapePartition lam)).ρ g v ∈ σ.toSubmodule :=
    fun σ g _ hv => σ.apply_mem_toSubmodule g hv
  -- split the tabloid along the invariant decomposition
  have hsup : MonoidAlgebra.single (tabloid t) (1 : ℚ) ∈
      (spechtSubrepresentation lam).toSubmodule ⊔
        (orthogonalSubrepresentation (spechtSubrepresentation lam)).toSubmodule := by
    have h := congrArg Subrepresentation.toSubmodule hc.sup_eq_top
    rw [Subrepresentation.toSubmodule_sup, Subrepresentation.toSubmodule_top] at h
    rw [h]
    exact Submodule.mem_top
  obtain ⟨e, he, w, hw, hsum⟩ := Submodule.mem_sup.mp hsup
  refine ⟨e, he, ?_⟩
  -- the two images stay in their summands
  have hmemS : (permutationModule (shapePartition lam)).ρ.asAlgebraHom (columnAntisymmetrizer t) e ∈
      (spechtSubrepresentation lam).toSubmodule :=
    Representation.asAlgebraHom_mem_of_forall_mem _ _ (hstable _) e he _
  have hmemW : (permutationModule (shapePartition lam)).ρ.asAlgebraHom (columnAntisymmetrizer t) w ∈
      (orthogonalSubrepresentation (spechtSubrepresentation lam)).toSubmodule :=
    Representation.asAlgebraHom_mem_of_forall_mem _ _ (hstable _) w hw _
  -- their sum is the polytabloid, so the second image lies in both summands
  have hadd : (permutationModule (shapePartition lam)).ρ.asAlgebraHom (columnAntisymmetrizer t) e +
      (permutationModule (shapePartition lam)).ρ.asAlgebraHom (columnAntisymmetrizer t) w =
      polytabloid t := by
    rw [← map_add, hsum, polytabloid_def]
  have hmemW' : (permutationModule (shapePartition lam)).ρ.asAlgebraHom
      (columnAntisymmetrizer t) w ∈ (spechtSubrepresentation lam).toSubmodule := by
    have : (permutationModule (shapePartition lam)).ρ.asAlgebraHom (columnAntisymmetrizer t) w =
        polytabloid t -
          (permutationModule (shapePartition lam)).ρ.asAlgebraHom (columnAntisymmetrizer t) e := by
      rw [← hadd]
      exact (add_sub_cancel_left _ _).symm
    rw [this]
    exact Submodule.sub_mem _ (polytabloid_mem_spechtSubrepresentation t) hmemS
  have hdisj : Disjoint (spechtSubrepresentation lam).toSubmodule
      (orthogonalSubrepresentation (spechtSubrepresentation lam)).toSubmodule :=
    disjoint_iff.mpr (by
      rw [← Subrepresentation.toSubmodule_inf, hc.inf_eq_bot, Subrepresentation.toSubmodule_bot])
  rw [← hadd, Submodule.disjoint_def.mp hdisj _ hmemW' hmemW, add_zero]

end YoungTableau

/-! ### Dominance from a nonzero map out of the Specht module -/

open YoungTableau

/-- Classical decidability of membership in the column group, used to form its finite sum, as in
`TauCeti/RepresentationTheory/Symmetric/Symmetrizer.lean`. -/
noncomputable local instance (t : YoungTableau lam) : DecidablePred (· ∈ colSubgroup t) :=
  Classical.decPred _

/-- **The dominance triangularity of maps out of a Specht module.**  A nonzero map of
representations from the Specht module of `lam` to the Young permutation module `M^μ` forces the
shape of `lam` to dominate `μ`.

The Specht module is irreducible, so `f` is injective.  Pick a `lam`-tableau `t` and a vector `e`
of `S^{lam}` with `b_t · e = e_t`; then `f e_t ≠ 0` and, because `f` intertwines the actions,
`b_t · f e = f (b_t · e) = f e_t`, so `b_t` does not annihilate `M^μ` and James's dominance lemma
applies. -/
theorem dominates_of_intertwiningMap_ne_zero (μ : lam.card.Partition)
    {f : Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
      (permutationModule μ).ρ} (hf : f ≠ 0) :
    Dominates (shapePartition lam) μ := by
  obtain ⟨t⟩ := YoungTableau.nonempty lam
  obtain ⟨e, he, hbe⟩ := exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid t
  have : (spechtSubrepresentation lam).toRepresentation.IsIrreducible :=
    isIrreducible_spechtSubrepresentation lam
  have hinj : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  -- the signed sum of the column translates of `e` is the polytabloid, hence nonzero
  set E : (spechtSubrepresentation lam).toSubmodule :=
    ∑ q : colSubgroup t, ((Equiv.Perm.sign (q : Equiv.Perm (Fin lam.card)) : ℤ) : ℚ) •
      (spechtSubrepresentation lam).toRepresentation q ⟨e, he⟩ with hE
  -- the action on the Specht module is the restriction of the ambient action
  have hact : ∀ (g : Equiv.Perm (Fin lam.card)) (v : (spechtSubrepresentation lam).toSubmodule),
      ((spechtSubrepresentation lam).toRepresentation g v :
          (permutationModule (shapePartition lam)).V) =
        (permutationModule (shapePartition lam)).ρ g v :=
    fun g v =>
      LinearMap.coe_restrict_apply ((spechtSubrepresentation lam).apply_mem_toSubmodule g) v
  have hEcoe : (E : (permutationModule (shapePartition lam)).V) = polytabloid t := by
    rw [hE, ← hbe, asAlgebraHom_columnAntisymmetrizer_apply]
    push_cast
    exact Finset.sum_congr rfl fun q _ => by rw [hact]
  have hEne : E ≠ 0 := fun h =>
    polytabloid_ne_zero t (by rw [← hEcoe, h, ZeroMemClass.coe_zero])
  -- and `f` carries it to `b_t` applied to `f ⟨e, he⟩`
  have hfE : (permutationModule μ).ρ.asAlgebraHom (columnAntisymmetrizer t) (f ⟨e, he⟩) = f E := by
    rw [asAlgebraHom_columnAntisymmetrizer_apply, hE, map_sum]
    exact Finset.sum_congr rfl fun q _ => by
      rw [map_smul, f.isIntertwining]
  refine dominates_of_asAlgebraHom_columnAntisymmetrizer_apply_ne_zero t μ
    (x := f ⟨e, he⟩) ?_
  rw [hfE]
  exact fun h => hEne (hinj (h.trans (map_zero f).symm))

/-- **The `Hom` space vanishes off the dominance order.**  If the shape of `lam` does not dominate
`μ`, every map of representations from the Specht module of `lam` to `M^μ` is zero. -/
theorem intertwiningMap_eq_zero_of_not_dominates (μ : lam.card.Partition)
    (h : ¬Dominates (shapePartition lam) μ)
    (f : Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
      (permutationModule μ).ρ) :
    f = 0 := by
  by_contra hf
  exact h (dominates_of_intertwiningMap_ne_zero μ hf)

end TauCeti
