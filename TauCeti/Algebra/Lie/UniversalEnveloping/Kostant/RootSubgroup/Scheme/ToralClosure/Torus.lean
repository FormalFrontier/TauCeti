/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Subsystem
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Torus

/-!
# The weight torus inside a Kostant toral-subsystem carrier

A toral-subsystem carrier indexed by `S` is generated scheme-theoretically by the represented root
subgroups selected by `S` and a represented split torus. This file proves that, when the weights
span the character lattice, the factored torus morphism into any such carrier is itself a closed
immersion. It therefore packages the split torus as a closed subgroup scheme of the assembled
carrier, rather than only as a morphism to it.

The proof compares the two existing constructions of the diagonal weight representation: the
coordinate-map construction used by the carrier and the comodule construction whose
closed-immersion criterion is already available. Since the inclusion of the carrier in `GL_n` is
a closed immersion, closedness descends from their composite to the factored torus.

For Chevalley weight data this supplies the closed embedding needed toward constructing the torus
component of a pinning on the assembled carrier. Identifying it as a maximal torus and constructing
the compatible Borel remain part of Layer 9 of the ReductiveGroups roadmap, on the path to the
ambient groups required by milestone L0 of the CFSGStatement roadmap.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantWeightTorusToToralSubsystem`:
  spanning weights make the factored weight torus a closed immersion.
* `TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusInToralSubsystem`: the corresponding
  closed subgroup scheme of a Kostant toral-subsystem carrier.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Finite κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)
variable (S : Set I)
variable (hnil : ∀ i ∈ S, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))

omit [Module ℚ V] in
private theorem weightTorusCoordinateMap_eq_diagonalCoordinateMap [Fintype κ] :
    GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt =
      CommHopfAlgCat.ofHom (DiagonalizableGroup.diagonalCoordinateMap b
        fun x => SplitTorus.weightCharacter (wt x)) := by
  apply _root_.CommHopfAlgCat.hom_ext
  apply BialgHom.ext
  intro x
  have hAlg :
      (GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt).hom.toAlgHom =
        (CommHopfAlgCat.ofHom (DiagonalizableGroup.diagonalCoordinateMap b
          fun y => SplitTorus.weightCharacter (wt y))).hom.toAlgHom := by
    apply GeneralLinear.coordinateHopfAlgebra_algHom_ext ℤ n
    intro i j
    let H := MonoidAlgebra ℤ (SplitTorus.characterGroup κ)
    let p : WithConv (H →ₐ[ℤ] H) := toConv (AlgHom.id ℤ H)
    have hmap := GeneralLinear.mapPointsFunctor_weightTorusCoordinateMap_app wt
      (CommAlgCat.of ℤ H) p
    have hweight (y : Fin n) :
        (DiagonalizableGroup.charOfPoint p.ofConv
          (SplitTorus.weightCharacter (wt y)) : H) =
          MonoidAlgebra.single (SplitTorus.weightCharacter (wt y)) 1 := by
      have hp : p.ofConv = AlgHom.id ℤ H := WithConv.ofConv_toConv _
      rw [DiagonalizableGroup.charOfPoint_apply_coe, hp, AlgHom.id_apply]
    have hleft := congrArg (fun q =>
        ((GeneralLinear.pointsMulEquiv n q : Matrix.GeneralLinearGroup (Fin n) H) :
          Matrix (Fin n) (Fin n) H) i j) hmap
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply,
      GeneralLinear.pointsMulEquiv_diagonalTorusPoints] at hleft
    rw [GeneralLinear.pointsMulEquiv_apply,
      GeneralLinear.pointToGeneralLinear_apply] at hleft
    -- The point-evaluation lemmas leave `hleft` behind the `pointsMulEquiv` wrapper;
    -- expose the underlying coordinate-algebra application used by `hAlg`.
    change (GeneralLinear.weightTorusCoordinateMap wt).hom.toAlgHom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
          (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (i, j)))) = _ at hleft
    -- `BialgHom.ext` presents the right side through `CommHopfAlgCat.ofHom`; expose its
    -- underlying algebra homomorphism so `diagonalCoordinateMap_X` can rewrite it.
    change _ = DiagonalizableGroup.diagonalCoordinateMap b
      (fun y => SplitTorus.weightCharacter (wt y))
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
          (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (i, j))))
    rw [DiagonalizableGroup.diagonalCoordinateMap_X]
    rcases eq_or_ne i j with rfl | hij
    · simp only [diagGL_apply, ↓reduceIte] at hleft
      have hcoord :
          (GeneralLinear.diagonalTorusCoordinates
              (SplitTorus.pointsMulEquiv
                (DiagonalizableGroup.pointsMap (GeneralLinear.weightCharacterMap wt) p)) i : H) =
            MonoidAlgebra.single (SplitTorus.weightCharacter (wt i)) 1 := by
        have hcoordUnits :=
          GeneralLinear.diagonalTorusCoordinates_pointsMap_weightCharacterMap wt
            (CommAlgCat.of ℤ H) p i
        rw [← SplitTorus.charOfPoint_weightCharacter] at hcoordUnits
        exact (congrArg Units.val hcoordUnits).trans (hweight i)
      rw [hcoord] at hleft
      simpa using hleft
    · simp only [diagGL_apply, hij, ↓reduceIte] at hleft
      simpa [Matrix.diagonal_apply_ne _ hij] using hleft
  exact DFunLike.congr_fun hAlg x

omit [Module ℚ V] in
private theorem weightTorusRepresentation_eq_weightTorus [Fintype κ] :
    weightTorusRepresentation b wt = GeneralLinear.weightTorus (R := ℤ) wt := by
  rw [weightTorusRepresentation_def, DiagonalizableGroup.diagonalGroupSchemeHom_def,
    GeneralLinear.weightTorus_def,
    weightTorusCoordinateMap_eq_diagonalCoordinateMap (M := M) b wt]

/-- **Spanning weights embed the represented split torus as a closed subgroup of a
toral-subsystem carrier indexed by `S`.** -/
theorem isClosedImmersion_kostantWeightTorusToToralSubsystem
    (hwt : Submodule.span ℤ (Set.range wt) = ⊤) :
    IsClosedImmersion
      (kostantWeightTorusToToralSubsystem e h ρ M hM b wt S hnil).hom.hom.left := by
  classical
  let _ := Fintype.ofFinite κ
  have hcomp : IsClosedImmersion
      ((kostantWeightTorusToToralSubsystem e h ρ M hM b wt S hnil ≫
        kostantToralSubsystemGroupSchemeι e h ρ M hM b wt S hnil).hom.hom.left) := by
    rw [kostantWeightTorusToToralSubsystem_comp_ι,
      ← weightTorusRepresentation_eq_weightTorus (M := M) b wt]
    exact isClosedImmersion_weightTorusRepresentation b wt hwt
  exact @IsClosedImmersion.of_comp _ _ _
    (kostantWeightTorusToToralSubsystem e h ρ M hM b wt S hnil).hom.hom.left
    (kostantToralSubsystemGroupSchemeι e h ρ M hM b wt S hnil).hom.hom.left hcomp inferInstance

/-- The split weight torus, with spanning weights, as a closed subgroup scheme of a
toral-subsystem carrier indexed by `S`. -/
noncomputable def kostantWeightTorusInToralSubsystem
    (hwt : Submodule.span ℤ (Set.range wt) = ⊤) :
    ClosedSubgroupScheme (kostantToralSubsystemGroupScheme e h ρ M hM b wt S hnil) :=
  have _ := isClosedImmersion_kostantWeightTorusToToralSubsystem
    e h ρ M hM b wt S hnil hwt
  ClosedSubgroupScheme.mk (kostantWeightTorusToToralSubsystem e h ρ M hM b wt S hnil)

/-- The underlying subobject of the closed weight torus in the toral-subsystem carrier is
represented by the factored weight-torus morphism. -/
@[simp]
theorem coe_kostantWeightTorusInToralSubsystem
    (hwt : Submodule.span ℤ (Set.range wt) = ⊤) :
    let _ := isClosedImmersion_kostantWeightTorusToToralSubsystem
      e h ρ M hM b wt S hnil hwt
    (kostantWeightTorusInToralSubsystem e h ρ M hM b wt S hnil hwt).1 =
      Subobject.mk (kostantWeightTorusToToralSubsystem e h ρ M hM b wt S hnil) := by
  have _ := isClosedImmersion_kostantWeightTorusToToralSubsystem
    e h ρ M hM b wt S hnil hwt
  rw [kostantWeightTorusInToralSubsystem]
  exact ClosedSubgroupScheme.coe_mk _

end TauCeti.UniversalEnvelopingAlgebra
