/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.Prod
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.OrthogonalQuotient.Bilinear
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.OrthogonalQuotient.Quadratic

/-!
# The comparison `A_(P ⊕ Q) ≅ (H⊥ / H) ⊥ (K⊥ / K)` for an orthogonal direct sum

Let `L` and `M` be nondegenerate integral lattices in rational spaces `V` and `W`, and let
`L ≤ P ≤ Lᵛ` and `M ≤ Q ≤ Mᵛ` be integral overlattices with subgroups `H = P / L ≤ A_L` and
`K = Q / M ≤ A_M`. The assembled carrier `P ⊕ Q` is an integral overlattice of `L ⊥ M`, its
subgroup is `H × K` under the canonical equivalence `A_(L ⊥ M) ≅ A_L ⊥ A_M`, and its discriminant
bilinear module is therefore computed twice over:

```text
A_(P ⊕ Q) ≅ (H × K)⊥ / (H × K) ≅ (H⊥ / H) ⊥ (K⊥ / K).
```

This file proves that the resulting comparison is componentwise: the composite isometry sends
the class of a dual vector `y` of `P ⊕ Q` to the pair of the classes of its two components under
the comparison isometries of `P` and of `Q`. Together with the naturality of that comparison
under a lattice isometry, proved in
`TauCeti.LinearAlgebra.IntegralLattice.Overlattice.OrthogonalQuotient.Bilinear`, this is the
functoriality package the gluing theory asks of the comparison isometry attached to an integral
overlattice.

For even lattices and even overlattices, the same construction and representative formula are
also given for the discriminant quadratic modules.

The two ingredients are the splitting of an orthogonal quotient of finite bilinear modules along
a product subgroup, from
`TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.Prod`, and the componentwise description
of the intermediate-carrier correspondence, from
`TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Naturality` and
`TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Dual`.

## Main declarations

* `IntermediateCarrier.discriminantBilinearOrthogonalQuotientIsometryOrthogonalSum`: the
  isometry `A_(P ⊕ Q) ≅ (H⊥ / H) ⊥ (K⊥ / K)` obtained from the comparison of `P ⊕ Q` and the
  splitting of the orthogonal quotient.
* `IntermediateCarrier.discriminantBilinearOrthogonalQuotientIsometryOrthogonalSum_mk`: it is
  componentwise, that is, it agrees with the pair of the comparison isometries of `P` and
  of `Q`.
* `IntermediateCarrier.discriminantQuadraticOrthogonalQuotientIsometryOrthogonalSum` and its
  `_mk` theorem: the corresponding componentwise comparison of discriminant quadratic modules.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

namespace TauCeti

namespace IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
variable {L : IntegralLattice V} {M : IntegralLattice W}
variable [L.IsNondegenerate] [M.IsNondegenerate]
variable {P : L.IntermediateCarrier} {Q : M.IntermediateCarrier}

namespace IntermediateCarrier

/-- **The orthogonal-sum isometry of discriminant bilinear modules on a dual class.** The
discriminant class in `A_(L ⊥ M)` of a dual vector of the assembled overlattice is the pair of the
discriminant classes of its two components. -/
theorem discriminantBilinearIsometryOrthogonalSum_dualClassHom (hP : IsIntegral P)
    (hQ : IsIntegral Q) (y : (hP.orthogonalSum hQ).toIntegralLattice.dualCarrier) :
    L.discriminantBilinearIsometryOrthogonalSum M ((hP.orthogonalSum hQ).dualClassHom y) =
      (hP.dualClassHom ⟨(y : V × W).1, fst_mem_dualCarrier_orthogonalSum hP hQ y⟩,
        hQ.dualClassHom ⟨(y : V × W).2, snd_mem_dualCarrier_orthogonalSum hP hQ y⟩) := by
  rw [discriminantBilinearIsometryOrthogonalSum_apply, IsIntegral.dualClassHom_apply,
    discriminantGroupOrthogonalSumEquiv_mk, orthogonalSumDualCarrierEquiv_apply,
    IsIntegral.dualClassHom_apply, IsIntegral.dualClassHom_apply]

/-- The transported discriminant class of a dual vector of the assembled overlattice is orthogonal
to the product subgroup, because each component is orthogonal to its own subgroup. -/
private theorem dualClassHom_mem_orthogonalComplement_prod (hP : IsIntegral P)
    (hQ : IsIntegral Q) (y : (hP.orthogonalSum hQ).toIntegralLattice.dualCarrier) :
    L.discriminantBilinearIsometryOrthogonalSum M ((hP.orthogonalSum hQ).dualClassHom y) ∈
      (L.discriminantBilinearModule.prod M.discriminantBilinearModule).orthogonalComplement
        ((L.discriminantSubgroup P).prod (M.discriminantSubgroup Q)) := by
  rw [discriminantBilinearIsometryOrthogonalSum_dualClassHom hP hQ y]
  exact (FiniteBilinearModule.mem_orthogonalComplement_prod_iff L.discriminantBilinearModule
      M.discriminantBilinearModule (L.discriminantSubgroup P) (M.discriminantSubgroup Q) _).mpr
    ⟨hP.dualClassHom_mem_orthogonalComplement _, hQ.dualClassHom_mem_orthogonalComplement _⟩

/-- The comparison isometry of the assembled overlattice, transported along the orthogonal-sum
isometry of discriminant bilinear modules to the orthogonal quotient by the product subgroup. -/
private noncomputable def discriminantBilinearOrthogonalQuotientProdStep (hP : IsIntegral P)
    (hQ : IsIntegral Q) :
    FiniteBilinearModule.Isometry
      (hP.orthogonalSum hQ).toIntegralLattice.discriminantBilinearModule
      ((L.discriminantBilinearModule.prod M.discriminantBilinearModule).orthogonalQuotient
        ((L.discriminantSubgroup P).prod (M.discriminantSubgroup Q))) :=
  (discriminantBilinearOrthogonalQuotientIsometry (hP.orthogonalSum hQ)).trans
    ((L.discriminantBilinearIsometryOrthogonalSum M).orthogonalQuotientEquiv
      (H := (L.orthogonalSum M).discriminantSubgroup
        (orthogonalSumIntermediateCarrier L M P Q))
      (K := (L.discriminantSubgroup P).prod (M.discriminantSubgroup Q))
      (by
        rw [discriminantBilinearIsometryOrthogonalSum_toAddEquiv]
        exact map_discriminantSubgroup_orthogonalSumIntermediateCarrier P Q))

/-- The transported comparison isometry sends the class of a dual vector of the assembled
overlattice to the class of its transported discriminant class. -/
private theorem discriminantBilinearOrthogonalQuotientProdStep_mk (hP : IsIntegral P)
    (hQ : IsIntegral Q) (y : (hP.orthogonalSum hQ).toIntegralLattice.dualCarrier) :
    discriminantBilinearOrthogonalQuotientProdStep hP hQ (Submodule.Quotient.mk y) =
      (L.discriminantBilinearModule.prod M.discriminantBilinearModule).orthogonalQuotientMk
        ((L.discriminantSubgroup P).prod (M.discriminantSubgroup Q))
        ⟨L.discriminantBilinearIsometryOrthogonalSum M ((hP.orthogonalSum hQ).dualClassHom y),
          dualClassHom_mem_orthogonalComplement_prod hP hQ y⟩ := by
  rw [discriminantBilinearOrthogonalQuotientProdStep]
  refine (FiniteBilinearModule.Isometry.trans_apply _ _ _).trans ?_
  rw [discriminantBilinearOrthogonalQuotientIsometry_mk]
  exact FiniteBilinearModule.Isometry.orthogonalQuotientEquiv_orthogonalQuotientMk
    (L.discriminantBilinearIsometryOrthogonalSum M) _ _

/-- **The discriminant bilinear module of an assembled overlattice as an orthogonal direct sum of
orthogonal quotients.** For integral overlattices `P` of `L` and `Q` of `M` with subgroups
`H = P / L` and `K = Q / M`, the comparison isometry of the assembled overlattice, transported
along `A_(L ⊥ M) ≅ A_L ⊥ A_M` and split along the product subgroup, is an isometry

```text
A_(P ⊕ Q) ≅ (H⊥ / H) ⊥ (K⊥ / K).
```
-/
noncomputable def discriminantBilinearOrthogonalQuotientIsometryOrthogonalSum
    (hP : IsIntegral P) (hQ : IsIntegral Q) :
    FiniteBilinearModule.Isometry
      (hP.orthogonalSum hQ).toIntegralLattice.discriminantBilinearModule
      ((L.discriminantBilinearModule.orthogonalQuotient (L.discriminantSubgroup P)).prod
        (M.discriminantBilinearModule.orthogonalQuotient (M.discriminantSubgroup Q))) :=
  (discriminantBilinearOrthogonalQuotientProdStep hP hQ).trans
    (FiniteBilinearModule.orthogonalQuotientProdIsometry
      (A := L.discriminantBilinearModule) (B := M.discriminantBilinearModule)
      (L.discriminantSubgroup P) (M.discriminantSubgroup Q))

/-- **The comparison isometry `A_(P ⊕ Q) ≅ (H⊥ / H) ⊥ (K⊥ / K)` is componentwise.** The isometry
attached to the assembled overlattice sends the class of a dual vector to the pair of the classes
of its two components under the comparison isometries `A_P ≅ H⊥ / H` of `P` and
`A_Q ≅ K⊥ / K` of `Q`. -/
theorem discriminantBilinearOrthogonalQuotientIsometryOrthogonalSum_mk
    (hP : IsIntegral P) (hQ : IsIntegral Q)
    (y : (hP.orthogonalSum hQ).toIntegralLattice.dualCarrier) :
    discriminantBilinearOrthogonalQuotientIsometryOrthogonalSum hP hQ
        (Submodule.Quotient.mk y) =
      (discriminantBilinearOrthogonalQuotientIsometry hP
          (Submodule.Quotient.mk ⟨(y : V × W).1, fst_mem_dualCarrier_orthogonalSum hP hQ y⟩),
        discriminantBilinearOrthogonalQuotientIsometry hQ
          (Submodule.Quotient.mk ⟨(y : V × W).2,
            snd_mem_dualCarrier_orthogonalSum hP hQ y⟩)) := by
  rw [discriminantBilinearOrthogonalQuotientIsometryOrthogonalSum]
  refine (FiniteBilinearModule.Isometry.trans_apply _ _ _).trans ?_
  rw [discriminantBilinearOrthogonalQuotientProdStep_mk]
  refine (FiniteBilinearModule.orthogonalQuotientProdIsometry_orthogonalQuotientMk _ _ _).trans ?_
  refine Prod.ext
    (Eq.trans (congrArg (L.discriminantBilinearModule.orthogonalQuotientMk
        (L.discriminantSubgroup P)) (Subtype.ext ?_))
      (discriminantBilinearOrthogonalQuotientIsometry_mk hP _).symm)
    (Eq.trans (congrArg (M.discriminantBilinearModule.orthogonalQuotientMk
        (M.discriminantSubgroup Q)) (Subtype.ext ?_))
      (discriminantBilinearOrthogonalQuotientIsometry_mk hQ _).symm)
  · exact (FiniteBilinearModule.coe_orthogonalComplementProdFst _ _ _).trans
      (congrArg Prod.fst (discriminantBilinearIsometryOrthogonalSum_dualClassHom hP hQ y))
  · exact (FiniteBilinearModule.coe_orthogonalComplementProdSnd _ _ _).trans
      (congrArg Prod.snd (discriminantBilinearIsometryOrthogonalSum_dualClassHom hP hQ y))

/-! ## The quadratic comparison for even overlattices -/

/-- **The discriminant quadratic module of an assembled even overlattice as an orthogonal direct
sum of orthogonal quotients.** This is the even refinement of
`discriminantBilinearOrthogonalQuotientIsometryOrthogonalSum`. -/
noncomputable def discriminantQuadraticOrthogonalQuotientIsometryOrthogonalSum
    (hL : L.IsEven) (hM : M.IsEven) (hP : IsEven P) (hQ : IsEven Q) :
    FiniteQuadraticModule.Isometry
      ((hP.isIntegral.orthogonalSum hQ.isIntegral).toIntegralLattice.discriminantQuadraticModule
        ((isEven_orthogonalSumIntermediateCarrier_iff P Q).mpr
          ⟨hP, hQ⟩).isEven_toIntegralLattice)
      (((L.discriminantQuadraticModule hL).orthogonalQuotient
          (L.discriminantSubgroup P)
          ((isEven_iff_isIsotropic_discriminantSubgroup hL P).mp hP)).prod
        ((M.discriminantQuadraticModule hM).orthogonalQuotient
          (M.discriminantSubgroup Q)
          ((isEven_iff_isIsotropic_discriminantSubgroup hM Q).mp hQ))) := by
  let hLM : (L.orthogonalSum M).IsEven :=
    (L.isEven_orthogonalSum_iff M).mpr ⟨hL, hM⟩
  let hPQ : IsEven (orthogonalSumIntermediateCarrier L M P Q) :=
    (isEven_orthogonalSumIntermediateCarrier_iff P Q).mpr ⟨hP, hQ⟩
  let hSubgroup := (isEven_iff_isIsotropic_discriminantSubgroup hLM
    (orthogonalSumIntermediateCarrier L M P Q)).mp hPQ
  have hMap := map_discriminantSubgroup_orthogonalSumIntermediateCarrier P Q
  rw [← L.discriminantQuadraticIsometryOrthogonalSum_toAddEquiv M hL hM] at hMap
  exact ((discriminantOrthogonalQuotientIsometry hLM hPQ).trans
    ((L.discriminantQuadraticIsometryOrthogonalSum M hL hM).orthogonalQuotientEquiv
      hSubgroup hMap)).trans
    (FiniteQuadraticModule.orthogonalQuotientProdIsometry
      ((isEven_iff_isIsotropic_discriminantSubgroup hL P).mp hP)
      ((isEven_iff_isIsotropic_discriminantSubgroup hM Q).mp hQ))

/-- **The quadratic comparison for an assembled even overlattice is componentwise.** It sends a
dual-vector class to the pair of its component classes under the two quadratic comparison
isometries. -/
theorem discriminantQuadraticOrthogonalQuotientIsometryOrthogonalSum_mk
    (hL : L.IsEven) (hM : M.IsEven) (hP : IsEven P) (hQ : IsEven Q)
    (y : (hP.isIntegral.orthogonalSum hQ.isIntegral).toIntegralLattice.dualCarrier) :
    discriminantQuadraticOrthogonalQuotientIsometryOrthogonalSum hL hM hP hQ
        (Submodule.Quotient.mk y) =
      (discriminantOrthogonalQuotientIsometry hL hP
          (Submodule.Quotient.mk ⟨(y : V × W).1,
            fst_mem_dualCarrier_orthogonalSum hP.isIntegral hQ.isIntegral y⟩),
        discriminantOrthogonalQuotientIsometry hM hQ
          (Submodule.Quotient.mk ⟨(y : V × W).2,
            snd_mem_dualCarrier_orthogonalSum hP.isIntegral hQ.isIntegral y⟩)) := by
  rw [discriminantQuadraticOrthogonalQuotientIsometryOrthogonalSum]
  -- The definition is a composite of three quadratic isometries whose quotient carriers use
  -- propositionally identified discriminant-group types. Expose the composite application after
  -- elaboration so that the three public representative formulas can rewrite it.
  change (FiniteQuadraticModule.orthogonalQuotientProdIsometry _ _)
    (((L.discriminantQuadraticIsometryOrthogonalSum M hL hM).orthogonalQuotientEquiv _ _)
      (discriminantOrthogonalQuotientIsometry _ _ (Submodule.Quotient.mk y))) = _
  rw [discriminantOrthogonalQuotientIsometry_mk]
  refine (congrArg (FiniteQuadraticModule.orthogonalQuotientProdIsometry _ _)
    (FiniteQuadraticModule.Isometry.orthogonalQuotientEquiv_orthogonalQuotientMk
      _ _ _ _)).trans ?_
  refine (FiniteQuadraticModule.orthogonalQuotientProdIsometry_orthogonalQuotientMk
    _ _ _).trans ?_
  have hclass :
      L.discriminantQuadraticIsometryOrthogonalSum M hL hM
          ((hP.isIntegral.orthogonalSum hQ.isIntegral).dualClassHom y) =
        (hP.isIntegral.dualClassHom
            ⟨(y : V × W).1, fst_mem_dualCarrier_orthogonalSum
              hP.isIntegral hQ.isIntegral y⟩,
          hQ.isIntegral.dualClassHom
            ⟨(y : V × W).2, snd_mem_dualCarrier_orthogonalSum
              hP.isIntegral hQ.isIntegral y⟩) := by
    rw [discriminantQuadraticIsometryOrthogonalSum_apply]
    rw [← discriminantBilinearIsometryOrthogonalSum_apply]
    exact discriminantBilinearIsometryOrthogonalSum_dualClassHom
      hP.isIntegral hQ.isIntegral y
  refine Prod.ext
    (Eq.trans (congrArg ((L.discriminantQuadraticModule hL).orthogonalQuotientMk
        (L.discriminantSubgroup P) _) (Subtype.ext ?_))
      (discriminantOrthogonalQuotientIsometry_mk hL hP _).symm)
    (Eq.trans (congrArg ((M.discriminantQuadraticModule hM).orthogonalQuotientMk
        (M.discriminantSubgroup Q) _) (Subtype.ext ?_))
      (discriminantOrthogonalQuotientIsometry_mk hM hQ _).symm)
  · exact (FiniteBilinearModule.coe_orthogonalComplementProdFst _ _ _).trans
      (congrArg Prod.fst hclass)
  · exact (FiniteBilinearModule.coe_orthogonalComplementProdSnd _ _ _).trans
      (congrArg Prod.snd hclass)

end IntermediateCarrier

end IntegralLattice

end TauCeti
