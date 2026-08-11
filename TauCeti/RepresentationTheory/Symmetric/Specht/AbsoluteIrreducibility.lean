/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Specht.Dominance

/-!
# Absolute irreducibility of rational Specht modules

Every endomorphism of a rational Specht module that commutes with the symmetric-group action is
scalar.  Equivalently, the endomorphism algebra of `S^mu` is `ℚ`.  This is the Schur-index-one
statement needed to pass from the rational Specht classification to irreducible complex
representations.

The proof uses the same column-antisymmetrizer calculation as James's submodule theorem.  For a
tableau `t`, the antisymmetrizer `b_t` maps the whole permutation module onto the line spanned by
the polytabloid `e_t`.  Moreover, `e_t = b_t v` for some `v` already in the Specht module.  An
equivariant endomorphism therefore maps `e_t` to a scalar multiple of itself.  Since the orbit of
`e_t` spans the Specht module, the endomorphism is that scalar everywhere.

## Main results

* `TauCeti.algebraMap_intertwiningMap_spechtSubrepresentation_bijective`: the scalar map onto the
  equivariant endomorphisms of the diagram-indexed Specht representation is bijective.
* `TauCeti.algebraMap_intertwiningMap_spechtModule_bijective`: the partition-indexed version for
  `spechtModule`.
* `TauCeti.spechtModuleEndAlgEquiv`: the `ℚ[S_n]`-linear endomorphism algebra of `S^mu` is
  isomorphic to `ℚ`.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 4.
* B. E. Sagan, *The Symmetric Group*, 2nd ed. (2001), Section 2.4.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "Absolute irreducibility".
-/

public section

namespace TauCeti

open YoungTableau

variable {mu : YoungDiagram}

private theorem intertwiningMap_eq_smul_one_of_apply_polytabloid_eq
    (t : YoungTableau mu)
    (f : Representation.IntertwiningMap
      (spechtSubrepresentation mu).toRepresentation
      (spechtSubrepresentation mu).toRepresentation)
    (kappa : ℚ)
    (h : f ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩ =
      kappa • ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩) :
    f = kappa • 1 := by
  let et : (spechtSubrepresentation mu).toSubmodule :=
    ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩
  let orbit : Set (spechtSubrepresentation mu).toSubmodule :=
    Set.range fun sigma : Equiv.Perm (Fin mu.card) =>
      (spechtSubrepresentation mu).toRepresentation sigma et
  have hspan : Submodule.span ℚ orbit = ⊤ := by
    apply Submodule.map_injective_of_injective
      (spechtSubrepresentation mu).toSubmodule.injective_subtype
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span]
    have himage : (spechtSubrepresentation mu).toSubmodule.subtype '' orbit =
        Set.range (fun sigma : Equiv.Perm (Fin mu.card) =>
          (permutationModule (shapePartition mu)).ρ sigma (polytabloid t)) := by
      ext x
      constructor
      · rintro ⟨y, ⟨sigma, rfl⟩, rfl⟩
        exact ⟨sigma, rfl⟩
      · rintro ⟨sigma, rfl⟩
        exact ⟨_, ⟨sigma, rfl⟩, rfl⟩
    rw [himage]
    exact (spechtSubrepresentation_eq_span_orbit t).symm
  apply Representation.IntertwiningMap.ext
  refine (Submodule.linearMap_eq_iff_of_span_eq_top _ _ hspan).2 ?_
  rintro ⟨_, ⟨sigma, rfl⟩⟩
  have hf := Representation.IntertwiningMap.isIntertwining
    (spechtSubrepresentation mu).toRepresentation
    (spechtSubrepresentation mu).toRepresentation f sigma et
  have het : f et = kappa • et := by simpa only [et] using h
  rw [het] at hf
  simpa only [Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.smul_apply,
    Representation.IntertwiningMap.coe_one, id_eq, map_smul] using hf

private theorem algebraMap_intertwiningMap_spechtSubrepresentation_injective
    (mu : YoungDiagram) :
    Function.Injective
      (algebraMap ℚ (Representation.IntertwiningMap
        (spechtSubrepresentation mu).toRepresentation
        (spechtSubrepresentation mu).toRepresentation)) := by
  obtain ⟨t⟩ := YoungTableau.nonempty mu
  let et : (spechtSubrepresentation mu).toSubmodule :=
    ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩
  intro q r hqr
  have happ := congrArg (fun F => F et) hqr
  have happ' : q • et = r • et := by
    simpa only [Representation.IntertwiningMap.algebraMap_apply,
      Representation.IntertwiningMap.smul_apply, Representation.IntertwiningMap.coe_one,
      id_eq] using happ
  have hcoeff := congrArg
    (fun v : (spechtSubrepresentation mu).toSubmodule =>
      (v : (permutationModule (shapePartition mu)).V).coeff (tabloid t)) happ'
  simpa only [Submodule.coe_smul, MonoidAlgebra.coeff_smul, polytabloid_coeff_tabloid,
    Finsupp.smul_apply, smul_eq_mul, mul_one, et] using hcoeff

/-- Every equivariant endomorphism of the diagram-indexed rational Specht representation is a
scalar.  In the canonical algebra structure on intertwining endomorphisms, this says that the
algebra map from `ℚ` is bijective. -/
theorem algebraMap_intertwiningMap_spechtSubrepresentation_bijective (mu : YoungDiagram) :
    Function.Bijective
      (algebraMap ℚ (Representation.IntertwiningMap
        (spechtSubrepresentation mu).toRepresentation
        (spechtSubrepresentation mu).toRepresentation)) := by
  constructor
  · exact algebraMap_intertwiningMap_spechtSubrepresentation_injective mu
  · intro f
    obtain ⟨t⟩ := YoungTableau.nonempty mu
    obtain ⟨v, hv, hbv⟩ :=
      exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid t
    let v' : (spechtSubrepresentation mu).toSubmodule := ⟨v, hv⟩
    have hmap : f
        ((spechtSubrepresentation mu).toRepresentation.asAlgebraHom
          (columnAntisymmetrizer t) v') =
        (spechtSubrepresentation mu).toRepresentation.asAlgebraHom
          (columnAntisymmetrizer t) (f v') :=
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _ f).map_smul'
        (columnAntisymmetrizer t) v'
    obtain ⟨kappa, hkappa⟩ := exists_eq_smul_polytabloid t (f v' : _)
    have hpoly : f ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩ =
        kappa • ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩ := by
      apply Subtype.ext
      have hmap' := congrArg Subtype.val hmap
      have hbv' : (spechtSubrepresentation mu).toRepresentation.asAlgebraHom
          (columnAntisymmetrizer t) v' =
          ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩ := by
        apply Subtype.ext
        simpa only [Subrepresentation.coe_toRepresentation_asAlgebraHom] using hbv
      rw [hbv'] at hmap'
      exact hmap'.trans (by
        simpa only [Subrepresentation.coe_toRepresentation_asAlgebraHom,
          Submodule.coe_smul] using hkappa)
    refine ⟨kappa, ?_⟩
    have hfscalar := intertwiningMap_eq_smul_one_of_apply_polytabloid_eq t f kappa hpoly
    rw [hfscalar]
    rfl

/-- Every equivariant endomorphism of the partition-indexed rational Specht module is scalar. -/
theorem algebraMap_intertwiningMap_spechtModule_bijective {n : ℕ} (mu : n.Partition) :
    Function.Bijective
      (algebraMap ℚ (Representation.IntertwiningMap (spechtModule mu).ρ (spechtModule mu).ρ)) := by
  constructor
  · obtain ⟨t⟩ := YoungTableau.nonempty (diagramOf mu)
    let et : (spechtModule mu).V :=
      ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩
    intro q r hqr
    have happ := congrArg (fun F => F et) hqr
    have happ' : q • et = r • et := by
      simpa only [Representation.IntertwiningMap.algebraMap_apply,
        Representation.IntertwiningMap.smul_apply, Representation.IntertwiningMap.coe_one,
        id_eq] using happ
    have hcoeff := congrArg
      (fun v : (spechtModule mu).V =>
        ((v : (spechtSubrepresentation (diagramOf mu)).toSubmodule) :
          (permutationModule (shapePartition (diagramOf mu))).V).coeff (tabloid t)) happ'
    -- Expose the concrete Specht subtype hidden by the `FDRep.of` carrier.
    change (q • polytabloid t).coeff (tabloid t) =
      (r • polytabloid t).coeff (tabloid t) at hcoeff
    simpa only [Submodule.coe_smul, MonoidAlgebra.coeff_smul,
      Finsupp.smul_apply, polytabloid_coeff_tabloid, smul_eq_mul, mul_one,
      spechtModule, FDRep.of_ρ', et] using hcoeff
  · intro f
    let e := (finCongr (card_diagramOf mu).symm).permCongrHom
    let f' : Representation.IntertwiningMap
        (spechtSubrepresentation (diagramOf mu)).toRepresentation
        (spechtSubrepresentation (diagramOf mu)).toRepresentation :=
      { toLinearMap := f.toLinearMap
        isIntertwining' g := by
          have hf := f.isIntertwining' (e.symm g)
          simpa only [spechtModule, FDRep.of_ρ', MonoidHom.comp_apply,
            MulEquiv.coe_toMonoidHom, e, MulEquiv.apply_symm_apply] using hf }
    obtain ⟨q, hq⟩ :=
      (algebraMap_intertwiningMap_spechtSubrepresentation_bijective
        (diagramOf mu)).surjective f'
    refine ⟨q, ?_⟩
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    -- Expose the common underlying subtype hidden by the `FDRep.of` packaging.
    change q • x = f x
    have hx := DFunLike.congr_fun hq x
    change q • x = f x at hx
    exact hx

private noncomputable def spechtModuleScalarAlgEquiv {n : ℕ} (mu : n.Partition) :
    ℚ ≃ₐ[ℚ] Representation.IntertwiningMap (spechtModule mu).ρ (spechtModule mu).ρ := by
  apply AlgEquiv.ofBijective (Algebra.ofId ℚ _)
  have hfun : ⇑(Algebra.ofId ℚ
      (Representation.IntertwiningMap (spechtModule mu).ρ (spechtModule mu).ρ)) =
      ⇑(algebraMap ℚ
        (Representation.IntertwiningMap (spechtModule mu).ρ (spechtModule mu).ρ)) := by
    funext q
    exact Algebra.ofId_apply
      (Representation.IntertwiningMap (spechtModule mu).ρ (spechtModule mu).ρ) q
  rw [hfun]
  exact algebraMap_intertwiningMap_spechtModule_bijective mu

private theorem spechtModuleScalarAlgEquiv_apply {n : ℕ} (mu : n.Partition) (q : ℚ) :
    spechtModuleScalarAlgEquiv mu q = algebraMap ℚ _ q := by
  rw [spechtModuleScalarAlgEquiv, AlgEquiv.ofBijective_apply, Algebra.ofId_apply]

/-- The algebra of intertwining endomorphisms of a rational Specht module is `ℚ`. -/
noncomputable def spechtModuleIntertwiningEndAlgEquiv {n : ℕ} (mu : n.Partition) :
    Representation.IntertwiningMap (spechtModule mu).ρ (spechtModule mu).ρ ≃ₐ[ℚ] ℚ :=
  (spechtModuleScalarAlgEquiv mu).symm

@[simp]
theorem spechtModuleIntertwiningEndAlgEquiv_apply_algebraMap {n : ℕ}
    (mu : n.Partition) (q : ℚ) :
    spechtModuleIntertwiningEndAlgEquiv mu (algebraMap ℚ _ q) = q := by
  rw [spechtModuleIntertwiningEndAlgEquiv, ← spechtModuleScalarAlgEquiv_apply]
  exact (spechtModuleScalarAlgEquiv mu).symm_apply_apply q

@[simp]
theorem spechtModuleIntertwiningEndAlgEquiv_symm_apply {n : ℕ}
    (mu : n.Partition) (q : ℚ) :
    (spechtModuleIntertwiningEndAlgEquiv mu).symm q = algebraMap ℚ _ q := by
  rw [spechtModuleIntertwiningEndAlgEquiv, AlgEquiv.symm_symm,
    spechtModuleScalarAlgEquiv_apply]

/-- The algebra of `ℚ[S_n]`-linear endomorphisms of a rational Specht module is `ℚ`. -/
noncomputable def spechtModuleEndAlgEquiv {n : ℕ} (mu : n.Partition) :
    Module.End (MonoidAlgebra ℚ (Equiv.Perm (Fin n)))
      (_root_.Representation.asModule (spechtModule mu).ρ) ≃ₐ[ℚ] ℚ :=
  (Representation.IntertwiningMap.equivAlgEnd (ρ := (spechtModule mu).ρ)).symm.trans
    (spechtModuleIntertwiningEndAlgEquiv mu)

@[simp]
theorem spechtModuleEndAlgEquiv_apply_algebraMap {n : ℕ} (mu : n.Partition) (q : ℚ) :
    spechtModuleEndAlgEquiv mu (algebraMap ℚ _ q) = q := by
  simpa using (spechtModuleEndAlgEquiv mu).commutes q

@[simp]
theorem spechtModuleEndAlgEquiv_symm_apply {n : ℕ} (mu : n.Partition) (q : ℚ) :
    (spechtModuleEndAlgEquiv mu).symm q = algebraMap ℚ _ q := by
  simpa using (spechtModuleEndAlgEquiv mu).symm.commutes q

end TauCeti
