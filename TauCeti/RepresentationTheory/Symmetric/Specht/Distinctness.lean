/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Specht.Dominance

/-!
# Distinctness of Specht modules

The rational Specht modules of two partitions of the same integer are isomorphic only when their
shapes agree.  This is the irredundancy half of the classification of the irreducible
representations of the symmetric group.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 4.
* B. E. Sagan, *The Symmetric Group*, 2nd ed. (2001), Section 2.4.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "Distinctness and completeness".
-/

public section

namespace TauCeti

open CategoryTheory
open YoungTableau
open scoped BigOperators

variable {lam m : YoungDiagram}

/-- The column antisymmetrizer after relabelling its entries along `e`. -/
private noncomputable def transportedColumnAntisymmetrizer
    (e : Fin lam.card ≃ Fin m.card) (t : YoungTableau lam) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin m.card)) :=
  MonoidAlgebra.mapDomainAlgHom ℚ ℚ e.permCongrHom.toMonoidHom (columnAntisymmetrizer t)

private theorem asAlgebraHom_comp_apply (e : Fin lam.card ≃ Fin m.card)
    (a : MonoidAlgebra ℚ (Equiv.Perm (Fin lam.card)))
    (x : (permutationModule (shapePartition m)).V) :
    Representation.asAlgebraHom
        ((permutationModule (shapePartition m)).ρ.comp e.permCongrHom.toMonoidHom) a x =
      (permutationModule (shapePartition m)).ρ.asAlgebraHom
        (MonoidAlgebra.mapDomainAlgHom ℚ ℚ e.permCongrHom.toMonoidHom a) x := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ (fun u v => u + v) ha hb
  | single g r => simp [Representation.asAlgebraHom_single]

private theorem transportedColumnAntisymmetrizer_single_eq_zero
    (e : Fin lam.card ≃ Fin m.card) (t : YoungTableau lam)
    (q : Equiv.Perm (Fin m.card) ⧸ youngSubgroup (shapePartition m))
    {x y : Fin m.card} (hxy : x ≠ y)
    (hcol : colIndex t (e.symm x) = colIndex t (e.symm y))
    (hfix : Equiv.swap x y • q = q) :
    (permutationModule (shapePartition m)).ρ.asAlgebraHom
        (transportedColumnAntisymmetrizer e t) (MonoidAlgebra.single q 1) = 0 := by
  let p₀ : Equiv.Perm (Fin lam.card) := Equiv.swap (e.symm x) (e.symm y)
  let p : Equiv.Perm (Fin m.card) := e.permCongrHom p₀
  have hp₀ : p₀ ∈ colSubgroup t := swap_mem_colSubgroup hcol
  have hp : p = Equiv.swap x y := by
    apply Equiv.ext
    intro z
    -- Unfold conjugation just far enough to apply `Equiv.map_swap`.
    change e (Equiv.swap (e.symm x) (e.symm y) (e.symm z)) = Equiv.swap x y z
    simpa using e.injective.map_swap (e.symm x) (e.symm y) (e.symm z)
  have hfix' : (permutationModule (shapePartition m)).ρ p (MonoidAlgebra.single q (1 : ℚ)) =
      MonoidAlgebra.single q 1 := by
    rw [Representation.ofMulAction_single, hp, hfix]
  have hneg : transportedColumnAntisymmetrizer e t * MonoidAlgebra.single p (1 : ℚ) =
      -transportedColumnAntisymmetrizer e t := by
    have h := congrArg
      (MonoidAlgebra.mapDomainAlgHom ℚ ℚ e.permCongrHom.toMonoidHom)
      (mul_columnAntisymmetrizer_right t ⟨p₀, hp₀⟩)
    rw [map_mul, map_smul] at h
    have hsingle :
        (MonoidAlgebra.mapDomainAlgHom ℚ ℚ e.permCongrHom.toMonoidHom)
            (MonoidAlgebra.single p₀ 1) = MonoidAlgebra.single p 1 := by
      -- Expose the underlying `mapDomain` operation so its basis lemma applies.
      change MonoidAlgebra.mapDomain e.permCongrHom (MonoidAlgebra.single p₀ 1) = _
      rw [MonoidAlgebra.mapDomain_single]
    rw [hsingle] at h
    -- Rewrite the transported definitions while retaining the useful equation `h`.
    change transportedColumnAntisymmetrizer e t * MonoidAlgebra.single p 1 =
      ((Equiv.Perm.sign p₀ : ℤ) : ℚ) • transportedColumnAntisymmetrizer e t at h
    rw [hp] at h
    rw [hp]
    calc
      transportedColumnAntisymmetrizer e t * MonoidAlgebra.single (Equiv.swap x y) 1 =
          ((Equiv.Perm.sign p₀ : ℤ) : ℚ) • transportedColumnAntisymmetrizer e t := by
        exact h
      _ = -transportedColumnAntisymmetrizer e t := by
        rw [Equiv.Perm.sign_swap (e.symm.injective.ne hxy)]
        simp
  have key : (permutationModule (shapePartition m)).ρ.asAlgebraHom
        (transportedColumnAntisymmetrizer e t) (MonoidAlgebra.single q 1) =
      -((permutationModule (shapePartition m)).ρ.asAlgebraHom
        (transportedColumnAntisymmetrizer e t) (MonoidAlgebra.single q 1)) := by
    conv_lhs => rw [← hfix']
    rw [← Representation.asAlgebraHom_single_one (permutationModule (shapePartition m)).ρ,
      ← Module.End.mul_apply, ← map_mul, hneg, map_neg, LinearMap.neg_apply]
  have htwo : (2 : ℚ) • (permutationModule (shapePartition m)).ρ.asAlgebraHom
      (transportedColumnAntisymmetrizer e t) (MonoidAlgebra.single q 1) = 0 := by
    rw [two_smul]
    nth_rewrite 2 [key]
    exact add_neg_cancel _
  exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero

private theorem coe_toRepresentation_apply {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℚ V] {ρ : Representation ℚ G V}
    (S : Subrepresentation ρ) (g : G) (x : S.toSubmodule) :
    ((S.toRepresentation g x : S.toSubmodule) : V) = ρ g (x : V) :=
  rfl

private theorem sum_take_rowLens_le_of_transportedColumnAntisymmetrizer_ne_zero
    (e : Fin lam.card ≃ Fin m.card) (t : YoungTableau lam)
    {v : (permutationModule (shapePartition m)).V}
    (hv : (permutationModule (shapePartition m)).ρ.asAlgebraHom
      (transportedColumnAntisymmetrizer e t) v ≠ 0) (k : ℕ) :
    (m.rowLens.take k).sum ≤ (lam.rowLens.take k).sum := by
  have hex : ∃ q : Equiv.Perm (Fin m.card) ⧸ youngSubgroup (shapePartition m),
      (permutationModule (shapePartition m)).ρ.asAlgebraHom
        (transportedColumnAntisymmetrizer e t) (MonoidAlgebra.single q 1) ≠ 0 := by
    by_contra h
    push Not at h
    have hspan : v ∈ Submodule.span ℚ
        (Set.range (permutationModuleBasis (shapePartition m))) := by
      rw [Module.Basis.span_eq]
      exact Submodule.mem_top
    have hzero : ∀ w ∈ Submodule.span ℚ
        (Set.range (permutationModuleBasis (shapePartition m))),
        (permutationModule (shapePartition m)).ρ.asAlgebraHom
          (transportedColumnAntisymmetrizer e t) w = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
          obtain ⟨q, rfl⟩ := hw
          rw [MonoidAlgebra.basis_apply, h q]
      | zero => rw [map_zero]
      | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
      | smul r a _ ha => rw [map_smul, ha, smul_zero]
    exact hv (hzero v hspan)
  obtain ⟨q, hq⟩ := hex
  obtain ⟨s, rfl⟩ := YoungTableau.tabloid_surjective (μ := m) q
  refine YoungTableau.sum_take_rowLens_le_of_injective t s e.symm (fun x y hrow hcol => ?_) k
  by_contra hxy
  apply hq
  exact transportedColumnAntisymmetrizer_single_eq_zero e t _ hxy hcol
    ((YoungTableau.smul_tabloid_eq_self_iff).mpr (swap_mem_rowSubgroup hrow))

private theorem sum_take_rowLens_le_of_intertwiningMap_ne_zero
    (e : Fin lam.card ≃ Fin m.card)
    {f : Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
      ((permutationModule (shapePartition m)).ρ.comp e.permCongrHom.toMonoidHom)}
    (hf : f ≠ 0) (k : ℕ) :
    (m.rowLens.take k).sum ≤ (lam.rowLens.take k).sum := by
  obtain ⟨t⟩ := YoungTableau.nonempty lam
  obtain ⟨v, hv, hbv⟩ :=
    YoungTableau.exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid t
  let v' : (spechtSubrepresentation lam).toSubmodule := ⟨v, hv⟩
  have : (spechtSubrepresentation lam).toRepresentation.IsIrreducible :=
    isIrreducible_spechtSubrepresentation lam
  have hinj : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  have hmap : f
      ((spechtSubrepresentation lam).toRepresentation.asAlgebraHom
        (columnAntisymmetrizer t) v') =
      (permutationModule (shapePartition m)).ρ.asAlgebraHom
        (transportedColumnAntisymmetrizer e t) (f v') := by
    rw [transportedColumnAntisymmetrizer, ← asAlgebraHom_comp_apply]
    exact (Representation.IntertwiningMap.equivLinearMapAsModule _ _ f).map_smul'
      (columnAntisymmetrizer t) v'
  apply sum_take_rowLens_le_of_transportedColumnAntisymmetrizer_ne_zero e t (k := k)
  rw [← hmap]
  intro h
  have hawne :
      (spechtSubrepresentation lam).toRepresentation.asAlgebraHom
        (columnAntisymmetrizer t) v' ≠ 0 := by
    intro haw
    apply YoungTableau.polytabloid_ne_zero t
    rw [← hbv]
    have haw' := congrArg Subtype.val haw
    rw [Subrepresentation.coe_toRepresentation_asAlgebraHom_apply] at haw'
    exact haw'
  exact hawne (hinj (h.trans (map_zero f).symm))

private noncomputable def spechtIntertwiningMapOfIso {n : ℕ} {μ ν : n.Partition}
    (i : spechtModule μ ≅ spechtModule ν) :
    Representation.IntertwiningMap (spechtSubrepresentation (diagramOf μ)).toRepresentation
      ((spechtSubrepresentation (diagramOf ν)).toRepresentation.comp
        (finCongr
          ((card_diagramOf μ).trans (card_diagramOf ν).symm)).permCongrHom.toMonoidHom) := by
  let f : Representation.Equiv (spechtModule μ).ρ (spechtModule ν).ρ :=
    Representation.equivOfIso
    ((forget₂ (FDRep ℚ (Equiv.Perm (Fin n))) (Rep ℚ (Equiv.Perm (Fin n)))).mapIso i)
  let eμ := (finCongr (card_diagramOf μ).symm).permCongrHom
  let eν := (finCongr (card_diagramOf ν).symm).permCongrHom
  let e := (finCongr ((card_diagramOf μ).trans (card_diagramOf ν).symm)).permCongrHom
  refine ⟨f.toLinearMap, fun g => ?_⟩
  have hf := f.toIntertwiningMap.isIntertwining' (eμ.symm g)
  have he : eν (eμ.symm g) = e g := by
    apply Equiv.Perm.ext
    intro x
    simp [eμ, eν, e, Equiv.permCongrHom_coe, Equiv.permCongr_apply, finCongr]
  simpa only [spechtModule, FDRep.of_ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    eμ, eν, e, MulEquiv.apply_symm_apply, he] using hf

private theorem spechtIntertwiningMapOfIso_injective {n : ℕ} {μ ν : n.Partition}
    (i : spechtModule μ ≅ spechtModule ν) : Function.Injective (spechtIntertwiningMapOfIso i) := by
  let f : Representation.Equiv (spechtModule μ).ρ (spechtModule ν).ρ :=
    Representation.equivOfIso
      ((forget₂ (FDRep ℚ (Equiv.Perm (Fin n))) (Rep ℚ (Equiv.Perm (Fin n)))).mapIso i)
  exact fun _ _ h => f.injective h

private noncomputable def spechtToPermutationIntertwiningMapOfIso {n : ℕ}
    {μ ν : n.Partition} (i : spechtModule μ ≅ spechtModule ν) :
    Representation.IntertwiningMap (spechtSubrepresentation (diagramOf μ)).toRepresentation
      ((permutationModule (shapePartition (diagramOf ν))).ρ.comp
        (finCongr ((card_diagramOf μ).trans (card_diagramOf ν).symm)).permCongrHom.toMonoidHom) :=
  { toLinearMap := (Submodule.subtype _).comp (spechtIntertwiningMapOfIso i).toLinearMap
    isIntertwining' := fun g => by
      apply LinearMap.ext
      intro v
      let f := spechtIntertwiningMapOfIso i
      have h := congrArg Subtype.val (DFunLike.congr_fun (f.isIntertwining' g) v)
      simp only [LinearMap.comp_apply, MonoidHom.comp_apply] at h
      rw [coe_toRepresentation_apply] at h
      simpa only [f, LinearMap.comp_apply, Submodule.coe_subtype, MonoidHom.comp_apply] using h }

private theorem spechtToPermutationIntertwiningMapOfIso_apply {n : ℕ}
    {μ ν : n.Partition} (i : spechtModule μ ≅ spechtModule ν)
    (v : (spechtSubrepresentation (diagramOf μ)).toSubmodule) :
    spechtToPermutationIntertwiningMapOfIso i v =
      ((spechtIntertwiningMapOfIso i v :
        (spechtSubrepresentation (diagramOf ν)).toSubmodule) :
          (permutationModule (shapePartition (diagramOf ν))).V) :=
  rfl

/-- An isomorphism from `S^μ` to `S^ν` forces `μ` to dominate `ν`. -/
private theorem dominates_of_spechtModule_iso {n : ℕ} {μ ν : n.Partition}
    (i : spechtModule μ ≅ spechtModule ν) : Dominates μ ν := by
  refine dominates_iff.mpr fun k => ?_
  simpa only [rowLens_diagramOf] using
    sum_take_rowLens_le_of_intertwiningMap_ne_zero
      (finCongr ((card_diagramOf μ).trans (card_diagramOf ν).symm))
      (f := spechtToPermutationIntertwiningMapOfIso i) (k := k) (by
        intro hzero
        obtain ⟨t⟩ := YoungTableau.nonempty (diagramOf μ)
        let v : (spechtSubrepresentation (diagramOf μ)).toSubmodule :=
          ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩
        have hv : v ≠ 0 := by
          intro h
          apply polytabloid_ne_zero t
          simpa only [v, ZeroMemClass.coe_zero] using congrArg Subtype.val h
        have heval := congrArg (fun f => f v) hzero
        rw [spechtToPermutationIntertwiningMapOfIso_apply] at heval
        have hinner : spechtIntertwiningMapOfIso i v = 0 := by
          apply Subtype.val_injective
          exact heval
        exact hv (spechtIntertwiningMapOfIso_injective i
          (hinner.trans (map_zero (spechtIntertwiningMapOfIso i)).symm)))

/-- **Specht modules have distinct partition labels.** Two rational Specht modules for `Sₙ` are
isomorphic if and only if their indexing partitions are equal. -/
@[simp]
theorem spechtModule_iso_iff {n : ℕ} (μ ν : n.Partition) :
    Nonempty (spechtModule μ ≅ spechtModule ν) ↔ μ = ν := by
  constructor
  · rintro ⟨i⟩
    exact (dominates_of_spechtModule_iso i).antisymm
      (dominates_of_spechtModule_iso i.symm)
  · rintro rfl
    exact ⟨Iso.refl _⟩

end TauCeti
