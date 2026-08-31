/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.Commutator
import TauCeti.Algebra.TensorProduct.Injective
import TauCeti.RingTheory.FiniteType.PointSeparation
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Geometric solvability, dense morphisms, and base change

An injective morphism `f : H ⟶ K` of coordinate Hopf algebras represents a schematically
dense homomorphism `Spec K ⟶ Spec H` of affine groups. If `K` is smooth over the field `k`,
then it is finite type, and solvability of the geometric points of `K` descends to `H`.

The proof turns a derived-word identity into a polynomial identity. The value algebra of the
universal depth-`n` derived word is built by repeatedly tensoring `K` with itself. Smoothness
makes this algebra reduced, so algebraic-closure-valued points separate its elements. Injectivity
of `f`, and hence of all its iterated tensor powers, then reflects the universal identity from
`K` to `H`.

For a finite-type affine group, the same argument makes each coordinate of the universal
derived-word defect nilpotent. Every field-valued point kills that defect, proving that geometric
solvability survives arbitrary field extension without a smoothness hypothesis.

## Main declarations

* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty.of_injective_of_smooth`: geometric
  solvability descends along an injective coordinate morphism with smooth codomain.
* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty.baseChange`: geometric solvability of a
  finite-type affine group is preserved by field extension.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.

These results supply the image-solvability and scalar-extension steps for the solvable radical in
Layer 6 of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv
open scoped commutatorElement TensorProduct

namespace TauCeti

universe u v w

noncomputable section

/-! The following universal-word construction is private proof machinery for the descent theorem.
Its public interface is deliberately the theorem at the end of the file. -/

/-- The coordinate algebra carrying the universal depth-`n` derived word. -/
private noncomputable abbrev derivedWordCoordinateAlgebra {k : Type u} [Field k]
    (H : CommHopfAlgCat.{v} k) (n : ℕ) : CommHopfAlgCat.{v} k :=
  Nat.rec H (fun _ D => CommHopfAlgCat.of k (D ⊗[k] D)) n

namespace derivedWordCoordinateAlgebra

variable {k : Type u} [Field k]
variable {H K : CommHopfAlgCat.{v} k}

/-- A coordinate morphism acts on universal derived-word value algebras by its iterated tensor
power. -/
private def map (f : H →ₐc[k] K) : (n : ℕ) →
    derivedWordCoordinateAlgebra H n →ₐc[k] derivedWordCoordinateAlgebra K n
  | 0 => f
  | n + 1 => Bialgebra.TensorProduct.map (map f n) (map f n)

@[simp] private theorem map_zero (f : H →ₐc[k] K) : map f 0 = f := rfl

@[simp] private theorem map_succ (f : H →ₐc[k] K) (n : ℕ) :
    map f (n + 1) = Bialgebra.TensorProduct.map (map f n) (map f n) := rfl

/-- Iterated tensor powers of an injective coordinate morphism remain injective. -/
private theorem map_injective (f : H →ₐc[k] K) (hf : Function.Injective f) (n : ℕ) :
    Function.Injective (map f n) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
      -- Expose the underlying algebra map to apply the shared tensor-injectivity lemma.
      change Function.Injective
        (Bialgebra.TensorProduct.map (map f n) (map f n)).toAlgHom
      rw [Bialgebra.TensorProduct.map_toAlgHom]
      exact Algebra.TensorProduct.map_injective_of_injective
        (map f n).toAlgHom (map f n).toAlgHom ih ih

/-- If the original coordinate algebra is smooth, every universal derived-word value algebra is
smooth. -/
private theorem smooth (hH : Algebra.Smooth k H) (n : ℕ) :
    Algebra.Smooth k (derivedWordCoordinateAlgebra H n) := by
  induction n with
  | zero => exact hH
  | succ n ih =>
      let _ : Algebra.Smooth k (derivedWordCoordinateAlgebra H n) := ih
      let _ : Algebra.Smooth (derivedWordCoordinateAlgebra H n)
          ((derivedWordCoordinateAlgebra H n) ⊗[k]
            (derivedWordCoordinateAlgebra H n)) :=
        Algebra.Smooth.baseChange k (derivedWordCoordinateAlgebra H n)
          (derivedWordCoordinateAlgebra H n)
      exact Algebra.Smooth.comp k (derivedWordCoordinateAlgebra H n)
        ((derivedWordCoordinateAlgebra H n) ⊗[k]
          (derivedWordCoordinateAlgebra H n))

/-- If the original coordinate algebra is finite type, every universal derived-word value
algebra is finite type. -/
private theorem finiteType (hH : Algebra.FiniteType k H) (n : ℕ) :
    Algebra.FiniteType k (derivedWordCoordinateAlgebra H n) := by
  induction n with
  | zero => exact hH
  | succ n ih =>
      let _ : Algebra.FiniteType k (derivedWordCoordinateAlgebra H n) := ih
      exact Algebra.FiniteType.trans (R := k) (S := derivedWordCoordinateAlgebra H n)
        (A := (derivedWordCoordinateAlgebra H n) ⊗[k]
          (derivedWordCoordinateAlgebra H n)) inferInstance inferInstance

end derivedWordCoordinateAlgebra

namespace HopfAlgebra

variable {k : Type u} [Field k]
variable (H : CommHopfAlgCat.{v} k)

/-- The universal depth-`n` derived word, valued in an iterated tensor product with one
independent coordinate copy for every leaf. -/
private def universalDerivedWord : (n : ℕ) →
    points (R := k) (H := H) (CommAlgCat.of k (derivedWordCoordinateAlgebra H n))
  | 0 => toConv (AlgHom.id k H)
  | n + 1 => toConv <| (Algebra.TensorProduct.map
      (universalDerivedWord n).ofConv (universalDerivedWord n).ofConv).comp
        (TauCeti.HopfAlgebra.commutatorAlgHom (R := k) (H := H))

@[simp] private theorem universalDerivedWord_zero :
    universalDerivedWord H 0 = toConv (AlgHom.id k H) := rfl

@[simp] private theorem universalDerivedWord_succ (n : ℕ) :
    universalDerivedWord H (n + 1) = toConv ((Algebra.TensorProduct.map
      (universalDerivedWord H n).ofConv (universalDerivedWord H n).ofConv).comp
        (TauCeti.HopfAlgebra.commutatorAlgHom (R := k) (H := H))) := rfl

/-- The `k`-algebra map out of the depth-`n` value algebra determined by a tree of points.
Composing it with the universal derived word gives the derived word of that tree. -/
private def derivedWordEvaluation {A : Type w} [CommRing A] [Algebra k A] :
    (n : ℕ) → DerivedWordArgs (points (R := k) (H := H) (CommAlgCat.of k A)) n →
      derivedWordCoordinateAlgebra H n →ₐ[k] A
  | 0, .leaf g => g.ofConv
  | n + 1, .node x y => Algebra.TensorProduct.productMap
      (derivedWordEvaluation n x) (derivedWordEvaluation n y)

@[simp] private theorem derivedWordEvaluation_leaf {A : Type w} [CommRing A] [Algebra k A]
    (g : points (R := k) (H := H) (CommAlgCat.of k A)) :
    derivedWordEvaluation H 0 (.leaf g) = g.ofConv := rfl

@[simp] private theorem derivedWordEvaluation_node {A : Type w} [CommRing A] [Algebra k A]
    (n : ℕ) (x y : DerivedWordArgs (points (R := k) (H := H) (CommAlgCat.of k A)) n) :
    derivedWordEvaluation H (n + 1) (.node x y) = Algebra.TensorProduct.productMap
      (derivedWordEvaluation H n x) (derivedWordEvaluation H n y) := rfl

/-- Decode an algebra homomorphism out of a universal derived-word value algebra into its tree
of leaf points. -/
private def derivedWordArgumentsOfAlgHom {A : Type w} [CommRing A] [Algebra k A] :
    (n : ℕ) → (derivedWordCoordinateAlgebra H n →ₐ[k] A) →
      DerivedWordArgs (points (R := k) (H := H) (CommAlgCat.of k A)) n
  | 0, q => .leaf (toConv q)
  | n + 1, q => .node
      (derivedWordArgumentsOfAlgHom n <| q.comp <|
        (Bialgebra.TensorProduct.includeLeft (R := k)
          (H₁ := derivedWordCoordinateAlgebra H n)
          (H₂ := derivedWordCoordinateAlgebra H n)).toAlgHom)
      (derivedWordArgumentsOfAlgHom n <| q.comp <|
        (Bialgebra.TensorProduct.includeRight (R := k)
          (H₁ := derivedWordCoordinateAlgebra H n)
          (H₂ := derivedWordCoordinateAlgebra H n)).toAlgHom)

@[simp] private theorem derivedWordArgumentsOfAlgHom_zero {A : Type w} [CommRing A]
    [Algebra k A] (q : H →ₐ[k] A) :
    derivedWordArgumentsOfAlgHom H 0 q = .leaf (toConv q) := rfl

@[simp] private theorem derivedWordArgumentsOfAlgHom_succ {A : Type w} [CommRing A]
    [Algebra k A] (n : ℕ) (q : derivedWordCoordinateAlgebra H (n + 1) →ₐ[k] A) :
    derivedWordArgumentsOfAlgHom H (n + 1) q = .node
      (derivedWordArgumentsOfAlgHom H n (q.comp
        (Bialgebra.TensorProduct.includeLeft (R := k)
          (H₁ := derivedWordCoordinateAlgebra H n)
          (H₂ := derivedWordCoordinateAlgebra H n)).toAlgHom))
      (derivedWordArgumentsOfAlgHom H n (q.comp
        (Bialgebra.TensorProduct.includeRight (R := k)
          (H₁ := derivedWordCoordinateAlgebra H n)
          (H₂ := derivedWordCoordinateAlgebra H n)).toAlgHom)) := rfl

/-- Decoding an algebra homomorphism into leaf points and evaluating those leaves recovers the
homomorphism. -/
@[simp] private theorem derivedWordEvaluation_argumentsOfAlgHom
    {A : Type w} [CommRing A] [Algebra k A]
    (n : ℕ) (q : derivedWordCoordinateAlgebra H n →ₐ[k] A) :
    derivedWordEvaluation H n (derivedWordArgumentsOfAlgHom H n q) = q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [derivedWordArgumentsOfAlgHom_succ, derivedWordEvaluation_node]
      rw [ih, ih]
      simpa only [Bialgebra.TensorProduct.includeLeft_toAlgHom,
        Bialgebra.TensorProduct.includeRight_toAlgHom] using
        AffineGroup.Product.productMap_restrict q

/-- Evaluating the universal point at a tree of points gives the corresponding derived word. -/
@[simp] private theorem mapValue_universalDerivedWord {A : Type w} [CommRing A] [Algebra k A]
    (n : ℕ) (x : DerivedWordArgs (points (R := k) (H := H) (CommAlgCat.of k A)) n) :
    toConv ((derivedWordEvaluation H n x).comp (universalDerivedWord H n).ofConv) =
      derivedWord (points (R := k) (H := H) (CommAlgCat.of k A)) n x := by
  induction n with
  | zero =>
      cases x with
      | leaf g =>
          simp only [universalDerivedWord_zero, derivedWord_leaf]
          apply WithConv.ofConv_injective
          ext z
          rfl
  | succ n ih =>
      cases x with
      | node x y =>
          rw [derivedWordEvaluation_node]
          apply WithConv.ofConv_injective
          have ihx : (derivedWordEvaluation H n x).comp
              (universalDerivedWord H n).ofConv =
              (derivedWord (points (R := k) (H := H) (CommAlgCat.of k A)) n x).ofConv := by
            simpa only [ofConv_toConv] using congrArg WithConv.ofConv (ih x)
          have ihy : (derivedWordEvaluation H n y).comp
              (universalDerivedWord H n).ofConv =
              (derivedWord (points (R := k) (H := H) (CommAlgCat.of k A)) n y).ofConv := by
            simpa only [ofConv_toConv] using congrArg WithConv.ofConv (ih y)
          simp only [universalDerivedWord_succ,
            ofConv_toConv, derivedWord_node]
          rw [← AlgHom.comp_assoc, Algebra.TensorProduct.productMap_eq_comp_map,
            AlgHom.comp_assoc (Algebra.TensorProduct.lmul' k),
            ← Algebra.TensorProduct.map_comp,
            ← Algebra.TensorProduct.productMap_eq_comp_map, ihx, ihy]
          exact TauCeti.HopfAlgebra.productMap_comp_commutatorAlgHom _ _

variable {H K : CommHopfAlgCat.{v} k}

/-- Universal derived words are natural in the coordinate Hopf algebra. -/
private theorem universalDerivedWord_natural (f : H →ₐc[k] K) (n : ℕ) :
    AlgHom.mapValue (derivedWordCoordinateAlgebra.map f n).toAlgHom
        (universalDerivedWord H n) =
      AlgHom.mapDomain f (universalDerivedWord K n) := by
  induction n with
  | zero =>
      apply WithConv.ofConv_injective
      ext z
      rfl
  | succ n ih =>
      apply WithConv.ofConv_injective
      have ih' : (derivedWordCoordinateAlgebra.map f n).toAlgHom.comp
          (universalDerivedWord H n).ofConv =
          (universalDerivedWord K n).ofConv.comp f.toAlgHom := by
        simpa only [AlgHom.mapValue_apply, AlgHom.mapDomain_apply] using
          congrArg WithConv.ofConv ih
      simp only [derivedWordCoordinateAlgebra.map_succ, universalDerivedWord_succ,
        AlgHom.mapValue_apply,
        AlgHom.mapDomain_apply, ofConv_toConv]
      rw [← AlgHom.comp_assoc, Bialgebra.TensorProduct.map_toAlgHom,
        ← Algebra.TensorProduct.map_comp, ih', Algebra.TensorProduct.map_comp,
        AlgHom.comp_assoc]
      have hcomm := TauCeti.HopfAlgebra.map_comp_commutatorAlgHom f
      rw [Bialgebra.TensorProduct.map_toAlgHom] at hcomm
      rw [hcomm, ← AlgHom.comp_assoc]

end HopfAlgebra

namespace geometricallySolvablePointsCommHopfAlgProperty

variable {k : Type u} [Field k]
variable {H K : CommHopfAlgCat.{v} k}

/-- Finite-type geometric solvability makes every coordinate of a universal derived-word defect
nilpotent. -/
private theorem exists_universalDerivedWord_sub_one_isNilpotent
    (hH_finite : Algebra.FiniteType k H)
    (hH : geometricallySolvablePointsCommHopfAlgProperty k H) :
    ∃ n, ∀ z, IsNilpotent ((HopfAlgebra.universalDerivedWord H n).ofConv z -
      algebraMap k (derivedWordCoordinateAlgebra H n) (Coalgebra.counit (R := k) z)) := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff,
    isSolvable_iff_exists_derivedWord_eq_one] at hH
  obtain ⟨n, hn⟩ := hH
  refine ⟨n, fun z ↦ ?_⟩
  let _ : Algebra.FiniteType k (derivedWordCoordinateAlgebra H n) :=
    derivedWordCoordinateAlgebra.finiteType hH_finite n
  rw [← TauCeti.forall_algHom_apply_eq_zero_iff_isNilpotent
    (k := k) (K := AlgebraicClosure k)]
  intro q
  let args := HopfAlgebra.derivedWordArgumentsOfAlgHom H n q
  have hq := HopfAlgebra.mapValue_universalDerivedWord H n args
  rw [HopfAlgebra.derivedWordEvaluation_argumentsOfAlgHom] at hq
  have hqz := congrArg (fun g : HopfAlgebra.points (R := k) (H := H)
    (CommAlgCat.of k (AlgebraicClosure k)) ↦ g.ofConv z) hq
  rw [hn] at hqz
  simpa [AlgHom.mapValue_apply, AlgHom.convOne_apply, sub_eq_zero] using hqz

/-- Smooth geometric solvability gives a universal derived-word identity in the coordinate
algebra. -/
private theorem exists_universalDerivedWord_eq_one
    (hH_smooth : Algebra.Smooth k H)
    (hH : geometricallySolvablePointsCommHopfAlgProperty k H) :
    ∃ n, HopfAlgebra.universalDerivedWord H n = 1 := by
  let _ : Algebra.Smooth k H := hH_smooth
  obtain ⟨n, hn⟩ := exists_universalDerivedWord_sub_one_isNilpotent
    (inferInstance : Algebra.FiniteType k H) hH
  refine ⟨n, ?_⟩
  let _ : Algebra.Smooth k (derivedWordCoordinateAlgebra H n) :=
    derivedWordCoordinateAlgebra.smooth hH_smooth n
  let _ : IsReduced (derivedWordCoordinateAlgebra H n) :=
    isReduced_of_smooth_of_field k (derivedWordCoordinateAlgebra H n)
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro z
  exact sub_eq_zero.mp (isNilpotent_iff_eq_zero.mp (hn z))

/-- A universal derived-word identity makes the points over every value algebra solvable. -/
private theorem isSolvable_points_of_universalDerivedWord_eq_one
    {A : Type w} [CommRing A] [Algebra k A] (n : ℕ)
    (hH : HopfAlgebra.universalDerivedWord H n = 1) :
    Group.IsSolvable
      (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k A)) := by
  rw [isSolvable_iff_exists_derivedWord_eq_one]
  refine ⟨n, fun x ↦ ?_⟩
  rw [← HopfAlgebra.mapValue_universalDerivedWord H n x, hH]
  apply WithConv.ofConv_injective
  ext z
  simp only [AlgHom.comp_apply, AlgHom.convOne_apply]
  exact (HopfAlgebra.derivedWordEvaluation H n x).commutes _

/-- A coordinatewise nilpotent universal derived-word defect vanishes at every field-valued
point. -/
private theorem isSolvable_points_of_universalDerivedWord_sub_one_isNilpotent
    {A : Type w} [Field A] [Algebra k A] (n : ℕ)
    (hH : ∀ z, IsNilpotent ((HopfAlgebra.universalDerivedWord H n).ofConv z -
      algebraMap k (derivedWordCoordinateAlgebra H n) (Coalgebra.counit (R := k) z))) :
    Group.IsSolvable
      (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k A)) := by
  rw [isSolvable_iff_exists_derivedWord_eq_one]
  refine ⟨n, fun x ↦ ?_⟩
  rw [← HopfAlgebra.mapValue_universalDerivedWord H n x]
  apply WithConv.ofConv_injective
  ext z
  have hz := (hH z).map (HopfAlgebra.derivedWordEvaluation H n x)
  rw [isNilpotent_iff_eq_zero] at hz
  simpa [AlgHom.convOne_apply, sub_eq_zero] using hz

/-- Geometric solvability descends along an injective morphism of coordinate Hopf algebras whose
codomain is smooth.

Contravariantly, the morphism represents a schematically dense homomorphism from `Spec K` to
`Spec H`. A derived-word identity on the algebraic-closure-valued points of `K` holds in the
universal iterated tensor product by point separation, and injectivity reflects that identity to
`H`. -/
theorem of_injective_of_smooth (f : H ⟶ K) (hf : Function.Injective f.hom)
    (hK_smooth : Algebra.Smooth k K)
    (hK : geometricallySolvablePointsCommHopfAlgProperty k K) :
    geometricallySolvablePointsCommHopfAlgProperty k H := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff]
  let f₀ := f.hom
  obtain ⟨n, hKuniv⟩ := exists_universalDerivedWord_eq_one hK_smooth hK
  -- Naturality and injectivity of the iterated tensor power of `f` reflect that universal
  -- identity from `K` to `H`.
  have hHuniv : HopfAlgebra.universalDerivedWord H n = 1 := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro z
    apply (derivedWordCoordinateAlgebra.map_injective f₀ hf n)
    have hnatural := HopfAlgebra.universalDerivedWord_natural f₀ n
    have hz := congrArg (fun g : HopfAlgebra.points (R := k) (H := H)
      (CommAlgCat.of k (derivedWordCoordinateAlgebra K n)) ↦ g.ofConv z) hnatural
    rw [hKuniv] at hz
    calc
      (derivedWordCoordinateAlgebra.map f₀ n)
          ((HopfAlgebra.universalDerivedWord H n).ofConv z) =
          algebraMap k (derivedWordCoordinateAlgebra K n)
            (Coalgebra.counit (R := k) z) := by
        simpa [AlgHom.mapDomain_apply, AlgHom.convOne_apply] using hz
      _ = (derivedWordCoordinateAlgebra.map f₀ n)
          (algebraMap k (derivedWordCoordinateAlgebra H n)
            (Coalgebra.counit (R := k) z)) :=
        ((derivedWordCoordinateAlgebra.map f₀ n).toAlgHom.commutes _).symm
      _ = (derivedWordCoordinateAlgebra.map f₀ n) ((1 : HopfAlgebra.points
          (R := k) (H := H) (CommAlgCat.of k (derivedWordCoordinateAlgebra H n))).ofConv z) := by
        rw [AlgHom.convOne_apply]
  exact isSolvable_points_of_universalDerivedWord_eq_one n hHuniv

/-- Geometric solvability of a finite-type affine group is preserved by arbitrary field
extension.

Finite-type Nullstellensatz makes the coordinates of a universal derived-word defect nilpotent.
They vanish under points valued in the algebraic closure of the larger field, and the standard
base-change equivalence of point groups transfers solvability. -/
theorem baseChange {K : Type w} [Field K] [Algebra k K]
    (H : CommHopfAlgCat.{v} k) [Algebra.FiniteType k H]
    (hH : geometricallySolvablePointsCommHopfAlgProperty k H) :
    geometricallySolvablePointsCommHopfAlgProperty K
      (CommHopfAlgCat.baseChange (K := K) H) := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff]
  obtain ⟨n, hword⟩ := exists_universalDerivedWord_sub_one_isNilpotent
    (inferInstance : Algebra.FiniteType k H) hH
  let _ : Algebra k (AlgebraicClosure K) :=
    Algebra.compHom (AlgebraicClosure K) (algebraMap k K)
  have hpoints : Group.IsSolvable
      (HopfAlgebra.points (R := k) (H := H)
        (CommAlgCat.of k (AlgebraicClosure K))) :=
    isSolvable_points_of_universalDerivedWord_sub_one_isNilpotent n hword
  let e := CommHopfAlgCat.baseChangePointsMulEquiv (K := K)
    (CommAlgCat.of K (AlgebraicClosure K)) H
  let _ := hpoints
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end geometricallySolvablePointsCommHopfAlgProperty

end

end TauCeti
