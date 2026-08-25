/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.Coalgebra.Convolution

/-!
# Central points of an affine group scheme

Let `H` be a commutative bialgebra over `R`, so that `A ↦ (H →ₐ[R] A)` is the functor of points
of the affine monoid scheme `Spec H`, a group functor when `H` is a Hopf algebra. A point
`g : H →ₐ[R] A` is **central** when its image in `G(B)` commutes with *every* `B`-point of `G`,
for every `A`-algebra `B`, and not merely with the points over `A` itself.

Quantifying over all value algebras is what makes the notion correct: an element of the abstract
group `G(A)` may commute with everything in `G(A)` without commuting with the points of `G` over
larger algebras, so the naive condition does not describe a subgroup scheme. The same functorial
formulation is used for the kernel of a central isogeny in
`TauCeti.GroupScheme.HasCentralKernel`.

The main result is that a single test algebra decides the question:
`TauCeti.HopfAlgebra.isCentralPoint_iff_commute_includeRight` says that `g` is central exactly
when its image in `G(A ⊗[R] H)` commutes with the tautological point `h ↦ 1 ⊗ₜ h`. Every other
value algebra is a specialization of that universal one, because an algebra map out of
`A ⊗[R] H` is exactly a pair consisting of an `A`-algebra and a point.

Specialized to the tautological point of `G` over `H` itself, the criterion says that `G` is a
commutative group functor exactly when `H` is cocommutative
(`TauCeti.HopfAlgebra.isCentralPoint_id_iff_isCocomm`).

## Main declarations

* `TauCeti.HopfAlgebra.IsCentralPoint`: centrality of a point of the functor of points.
* `TauCeti.HopfAlgebra.center`: the central points as a subgroup of the group of points.
* `TauCeti.HopfAlgebra.instIsMulCommutativeCenter`: the central points form a commutative group.

## Main results

* `TauCeti.HopfAlgebra.isCentralPoint_iff_commute_includeRight`: **one test algebra suffices**.
* `TauCeti.HopfAlgebra.commute_includeLeft_includeRight_iff_isCocomm`: the two tensor-factor
  points of `H` commute exactly when `H` is cocommutative.
* `TauCeti.HopfAlgebra.convMul_includeRight_includeLeft`: the convolution product of the two
  tensor-factor points in the reversed order is the flipped comultiplication.
* `TauCeti.HopfAlgebra.isCentralPoint_id_iff_isCocomm`: the tautological point is central exactly
  when `H` is cocommutative.
* `TauCeti.HopfAlgebra.IsCentralPoint.mapDomain_bialgEquiv` and
  `TauCeti.HopfAlgebra.isCentralPoint_mapDomain_bialgEquiv_iff`: centrality is invariant under a
  change of coordinate bialgebra by an equivalence.

## References

* J. S. Milne, *Algebraic Groups* (2017), §1.k and §2.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This is a prerequisite for the center `Z(G)` in Layer 6, "Reductive and semisimple groups", of
`TauCetiRoadmap/ReductiveGroups/README.md`.
-/

public section

open TensorProduct WithConv

namespace TauCeti

namespace HopfAlgebra

universe u v

section Definition

variable {R : Type u} {H : Type v} {A : Type v}
variable [CommRing R] [Ring H] [_root_.Bialgebra R H] [CommRing A] [Algebra R A]

/-- A point `g` of `Spec H` with values in `A` is **central** when, for every `R`-algebra map
`φ : A →ₐ[R] B` into a commutative `R`-algebra, the point `φ ∘ g` commutes with every `B`-point
of `Spec H`.

Commuting with the points over `A` alone is a strictly weaker condition and does not describe a
subgroup scheme; this is why the value algebra is quantified over. Restricting the quantifier to
`Type v` loses nothing: `TauCeti.HopfAlgebra.isCentralPoint_iff_commute_includeRight` shows that
the single value algebra `A ⊗[R] H` already decides centrality. -/
def IsCentralPoint (g : WithConv (H →ₐ[R] A)) : Prop :=
  ∀ ⦃B : Type v⦄ [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (h : WithConv (H →ₐ[R] B)),
    Commute (AlgHom.mapValue φ g) h

/-- Centrality, restated as the defining condition. -/
theorem isCentralPoint_def (g : WithConv (H →ₐ[R] A)) :
    IsCentralPoint g ↔
      ∀ ⦃B : Type v⦄ [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (h : WithConv (H →ₐ[R] B)),
        Commute (AlgHom.mapValue φ g) h :=
  Iff.rfl

/-- A central point commutes with every point over its own value algebra. -/
theorem IsCentralPoint.commute {g : WithConv (H →ₐ[R] A)} (hg : IsCentralPoint g)
    (h : WithConv (H →ₐ[R] A)) : Commute g h := by
  simpa using hg (AlgHom.id R A) h

/-- Centrality is preserved by change of value algebra. -/
theorem IsCentralPoint.mapValue {g : WithConv (H →ₐ[R] A)} (hg : IsCentralPoint g)
    {B : Type v} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) :
    IsCentralPoint (AlgHom.mapValue φ g) := by
  intro C _ _ ψ h
  rw [← MonoidHom.comp_apply, ← AlgHom.mapValue_comp]
  exact hg (ψ.comp φ) h

section CoordinateEquiv

variable {K : Type v} [Ring K] [_root_.Bialgebra R K]

/-- Precomposition by a bialgebra equivalence preserves universal centrality of points. -/
theorem IsCentralPoint.mapDomain_bialgEquiv {g : WithConv (K →ₐ[R] A)}
    (hg : IsCentralPoint g) (e : H ≃ₐc[R] K) :
    IsCentralPoint (AlgHom.mapDomain (A := A) e.toBialgHom g) := by
  intro B _ _ φ h
  let E := AlgHom.mapDomainMulEquiv (A := B) e
  have hc := hg φ (E.symm h)
  have hc' := hc.map E.toMonoidHom
  simp only [MulEquiv.coe_toMonoidHom] at hc'
  have hnatural :
      E (AlgHom.mapValue (H := K) φ g) =
        AlgHom.mapValue (H := H) φ (AlgHom.mapDomain (A := A) e.toBialgHom g) :=
    DFunLike.congr_fun (AlgHom.mapValue_mapDomain e.toBialgHom φ) g
  rw [hnatural, E.apply_symm_apply] at hc'
  exact hc'

/-- Precomposition by a bialgebra equivalence preserves and reflects universal centrality of
points. This is invariance of the center of the functor of points under a change of coordinate
Hopf algebra. -/
theorem isCentralPoint_mapDomain_bialgEquiv_iff (e : H ≃ₐc[R] K)
    (g : WithConv (K →ₐ[R] A)) :
    IsCentralPoint (AlgHom.mapDomain (A := A) e.toBialgHom g) ↔ IsCentralPoint g := by
  constructor
  · intro hg
    have htransport := hg.mapDomain_bialgEquiv e.symm
    simp only [BialgEquiv.toBialgHom_eq_coe] at htransport
    rw [← AlgHom.mapDomainMulEquiv_apply (A := A) e,
      ← AlgHom.mapDomainMulEquiv_symm_apply (A := A) e,
      (AlgHom.mapDomainMulEquiv (A := A) e).symm_apply_apply] at htransport
    exact htransport
  · exact fun hg ↦ hg.mapDomain_bialgEquiv e

end CoordinateEquiv

/-- The identity point is central. -/
theorem isCentralPoint_one : IsCentralPoint (1 : WithConv (H →ₐ[R] A)) := by
  intro B _ _ φ h
  rw [map_one]
  exact Commute.one_left h

/-- A product of central points is central. -/
theorem IsCentralPoint.mul {g g' : WithConv (H →ₐ[R] A)} (hg : IsCentralPoint g)
    (hg' : IsCentralPoint g') : IsCentralPoint (g * g') := by
  intro B _ _ φ h
  rw [map_mul]
  exact (hg φ h).mul_left (hg' φ h)

/-- Over a cocommutative bialgebra every point is central, the group functor being commutative. -/
theorem isCentralPoint_of_isCocomm [_root_.Coalgebra.IsCocomm R H]
    (g : WithConv (H →ₐ[R] A)) : IsCentralPoint g :=
  fun _ _ _ _ h ↦ Commute.all _ h

end Definition

section Group

variable {R : Type u} {H : Type v} {A : Type v}
variable [CommRing R] [Ring H] [_root_.HopfAlgebra R H] [CommRing A] [Algebra R A]

/-- The inverse of a central point is central. -/
theorem IsCentralPoint.inv {g : WithConv (H →ₐ[R] A)} (hg : IsCentralPoint g) :
    IsCentralPoint g⁻¹ := by
  intro B _ _ φ h
  rw [map_inv]
  exact (hg φ h).inv_left

variable (R H A) in
/-- The **center** of the functor of points, as a subgroup of the group of `A`-points.

Its elements are the points that stay central after every change of value algebra, so the
construction is natural in `A` (`TauCeti.HopfAlgebra.mapValue_mem_center`). It is contained in,
and in general strictly smaller than, the abstract center of the group `G(A)`. -/
noncomputable def center : Subgroup (WithConv (H →ₐ[R] A)) where
  carrier := {g | IsCentralPoint g}
  mul_mem' hg hg' := IsCentralPoint.mul hg hg'
  one_mem' := isCentralPoint_one
  inv_mem' hg := IsCentralPoint.inv hg

@[simp]
theorem mem_center {g : WithConv (H →ₐ[R] A)} : g ∈ center R H A ↔ IsCentralPoint g :=
  Iff.rfl

/-- The center of the functor of points is contained in the abstract center of the group of
`A`-points. The inclusion is generally strict: an abstractly central point need not stay central
over larger value algebras. -/
theorem center_le_center : center R H A ≤ Subgroup.center (WithConv (H →ₐ[R] A)) :=
  fun _ hg ↦ Subgroup.mem_center_iff.mpr fun h ↦ ((mem_center.mp hg).commute h).symm

/-- The universally central points form a commutative group. -/
noncomputable instance instIsMulCommutativeCenter : IsMulCommutative (center R H A) :=
  IsMulCommutative.of_setLike_mul_comm fun _ ha b _ ↦ ((mem_center.mp ha).commute b).eq

/-- The center is natural in the value algebra. -/
theorem mapValue_mem_center {B : Type v} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    {g : WithConv (H →ₐ[R] A)} (hg : g ∈ center R H A) :
    AlgHom.mapValue φ g ∈ center R H B :=
  (mem_center.mp hg).mapValue φ

end Group

section Universal

variable {R : Type u} {H : Type v} {A : Type v}
variable [CommRing R] [CommRing H] [_root_.Bialgebra R H] [CommRing A] [Algebra R A]

/-- **A single value algebra decides centrality.** A point `g` of `Spec H` over `A` is central
exactly when its image over `A ⊗[R] H` commutes with the tautological point `h ↦ 1 ⊗ₜ h`.

Every pair consisting of an `A`-algebra `B` and a `B`-point of `Spec H` is the same thing as an
algebra map `A ⊗[R] H →ₐ[R] B`, and the convolution product is functorial in the value algebra,
so the universal case implies all the others. -/
theorem isCentralPoint_iff_commute_includeRight (g : WithConv (H →ₐ[R] A)) :
    IsCentralPoint g ↔
      Commute
        (AlgHom.mapValue
          (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := H)) g)
        (toConv (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := H))) := by
  refine ⟨fun hg ↦ hg _ _, fun hg B _ _ φ h ↦ ?_⟩
  have key := hg.map (AlgHom.mapValue (H := H) (Algebra.TensorProduct.productMap φ h.ofConv))
  have h₁ : AlgHom.mapValue (H := H) (Algebra.TensorProduct.productMap φ h.ofConv)
      (AlgHom.mapValue
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := H)) g) =
      AlgHom.mapValue φ g := by
    rw [← MonoidHom.comp_apply, ← AlgHom.mapValue_comp, Algebra.TensorProduct.productMap_left]
  have h₂ : AlgHom.mapValue (H := H) (Algebra.TensorProduct.productMap φ h.ofConv)
      (toConv (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := H))) = h := by
    rw [AlgHom.mapValue_apply, ofConv_toConv, Algebra.TensorProduct.productMap_right, toConv_ofConv]
  rwa [h₁, h₂] at key

end Universal

section Cocommutative

variable {R : Type u} {H : Type v}
variable [CommRing R] [CommRing H] [_root_.Bialgebra R H]

private theorem coe_algebraTensorProductComm (y : H ⊗[R] H) :
    (Algebra.TensorProduct.comm R H H) y = _root_.TensorProduct.comm R H H y := rfl

private theorem comm_toAlgHom_comp_includeLeft :
    (Algebra.TensorProduct.comm R H H).toAlgHom.comp
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)) =
      Algebra.TensorProduct.includeRight := by
  ext x
  simp

private theorem comm_toAlgHom_comp_includeRight :
    (Algebra.TensorProduct.comm R H H).toAlgHom.comp
        (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)) =
      Algebra.TensorProduct.includeLeft := by
  ext x
  simp

/-- The convolution product of the two tensor-factor points, taken in the other order, is the
comultiplication followed by the flip of the tensor factors. -/
theorem convMul_includeRight_includeLeft :
    toConv (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)) *
        toConv (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)) =
      toConv ((Algebra.TensorProduct.comm R H H).toAlgHom.comp
        (_root_.Bialgebra.comulAlgHom R H)) := by
  have key := map_mul (AlgHom.mapValue (H := H) (Algebra.TensorProduct.comm R H H).toAlgHom)
    (toConv (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)))
    (toConv (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)))
  simp only [← Bialgebra.TensorProduct.includeLeft_toAlgHom,
    ← Bialgebra.TensorProduct.includeRight_toAlgHom] at key
  rw [← Bialgebra.comulPoint_eq_include_mul] at key
  simp only [Bialgebra.TensorProduct.includeLeft_toAlgHom,
    Bialgebra.TensorProduct.includeRight_toAlgHom] at key
  rw [AlgHom.mapValue_apply, AlgHom.mapValue_apply, AlgHom.mapValue_apply, ofConv_toConv,
    ofConv_toConv, ofConv_toConv, comm_toAlgHom_comp_includeLeft,
    comm_toAlgHom_comp_includeRight] at key
  exact key.symm

variable (R H) in
/-- **The two tensor-factor points of `H` commute exactly when `H` is cocommutative.** The two
convolution products are the comultiplication and its flip, so their equality is precisely
cocommutativity. -/
theorem commute_includeLeft_includeRight_iff_isCocomm :
    Commute (toConv (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)))
        (toConv (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H))) ↔
      _root_.Coalgebra.IsCocomm R H := by
  simp only [← Bialgebra.TensorProduct.includeLeft_toAlgHom,
    ← Bialgebra.TensorProduct.includeRight_toAlgHom]
  rw [commute_iff_eq, ← Bialgebra.comulPoint_eq_include_mul]
  simp only [Bialgebra.TensorProduct.includeLeft_toAlgHom,
    Bialgebra.TensorProduct.includeRight_toAlgHom]
  rw [convMul_includeRight_includeLeft]
  constructor
  · intro h
    refine ⟨LinearMap.ext fun x ↦ ?_⟩
    have hx := congrArg (fun f ↦ f.ofConv x) h
    simpa [coe_algebraTensorProductComm] using hx.symm
  · intro _
    refine congrArg toConv (AlgHom.ext fun x ↦ ?_)
    simp [coe_algebraTensorProductComm]

end Cocommutative

section Tautological

variable {R : Type u} {H : Type v}
variable [CommRing R] [CommRing H] [_root_.Bialgebra R H]

variable (R H) in
/-- **The tautological point is central exactly when `H` is cocommutative**, that is, exactly
when the group functor of `Spec H` is commutative. -/
theorem isCentralPoint_id_iff_isCocomm :
    IsCentralPoint (toConv (AlgHom.id R H)) ↔ _root_.Coalgebra.IsCocomm R H := by
  have h : AlgHom.mapValue (H := H)
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H))
        (toConv (AlgHom.id R H)) =
      toConv (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)) := by
    rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_id]
  rw [isCentralPoint_iff_commute_includeRight, h,
    commute_includeLeft_includeRight_iff_isCocomm]

end Tautological

end HopfAlgebra

end TauCeti
