/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Commutator
public import TauCeti.Algebra.AlgebraicGroup.Smooth.Product
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic
public import TauCeti.GroupTheory.Solvable
import TauCeti.RingTheory.FiniteType.PointSeparation
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Solvability under schematically dense affine group morphisms

An injective morphism of coordinate Hopf algebras represents a schematically dense homomorphism
of affine groups. If the source coordinate algebra is smooth and finite type over a field, then
solvability of its geometric points descends to the target.

The proof turns a derived-word identity into a polynomial identity. The value algebra of the
universal depth-`n` derived word is built by repeatedly tensoring the source coordinate algebra
with itself. Smoothness makes this algebra reduced, so algebraic-closure-valued points separate
its elements. Injectivity of the original coordinate morphism, and hence of all its iterated
tensor powers, then reflects the universal identity to the target.

## Main declarations

* `TauCeti.derivedWordCoordinateAlgebra`: the value algebra of the universal derived word.
* `TauCeti.HopfAlgebra.universalDerivedWord`: the universal point obtained by evaluating a
  balanced derived word.
* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty.of_injective_of_smooth`: geometric
  solvability descends along an injective coordinate morphism with smooth finite-type codomain.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.

This supplies the image-solvability step needed to close solvable-radical candidates under
scheme-theoretic products in Layer 6 of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv
open scoped commutatorElement TensorProduct

namespace TauCeti

universe u

noncomputable section

/-- The coordinate algebra carrying the universal depth-`n` derived word. At depth zero it is
the original coordinate algebra; at a successor it has two independent copies of the preceding
value algebra. -/
noncomputable abbrev derivedWordCoordinateAlgebra {k : Type u} [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (n : ℕ) :
    FiniteTypeCommHopfAlgCat.{u, u} k :=
  Nat.rec H (fun _ D => FiniteTypeCommHopfAlgCat.tensorProduct D D) n

namespace derivedWordCoordinateAlgebra

variable {k : Type u} [Field k]
variable {H K : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A coordinate morphism acts on universal derived-word value algebras by its iterated tensor
power. -/
def map (f : H →ₐc[k] K) : (n : ℕ) →
    derivedWordCoordinateAlgebra H n →ₐc[k] derivedWordCoordinateAlgebra K n
  | 0 => f
  | n + 1 => Bialgebra.TensorProduct.map (map f n) (map f n)

/-- Iterated tensor powers of an injective coordinate morphism remain injective. -/
theorem map_injective (f : H →ₐc[k] K) (hf : Function.Injective f) (n : ℕ) :
    Function.Injective (map f n) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
      have h := TensorProduct.map_injective_of_flat_flat
        (map f n).toLinearMap (map f n).toLinearMap ih ih
      intro x y hxy
      apply h
      change (Algebra.TensorProduct.map (map f n).toAlgHom
        (map f n).toAlgHom) x = _
      exact hxy

/-- If the original coordinate algebra is smooth, every universal derived-word value algebra is
smooth. -/
theorem smooth (hH : Algebra.Smooth k H) (n : ℕ) :
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

end derivedWordCoordinateAlgebra

namespace HopfAlgebra

variable {k : Type u} [Field k]
variable (H : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- The universal depth-`n` derived word, valued in the iterated tensor product containing one
independent coordinate copy for every leaf. -/
def universalDerivedWord : (n : ℕ) →
    points (R := k) (H := H)
      (CommAlgCat.of k (derivedWordCoordinateAlgebra H n))
  | 0 => toConv (AlgHom.id k H)
  | n + 1 => by
      change points (R := k) (H := H)
        (CommAlgCat.of k ((derivedWordCoordinateAlgebra H n) ⊗[k]
          (derivedWordCoordinateAlgebra H n)))
      exact ⁅AlgHom.mapValue
          (Bialgebra.TensorProduct.includeLeft (R := k)
            (H₁ := derivedWordCoordinateAlgebra H n)
            (H₂ := derivedWordCoordinateAlgebra H n)).toAlgHom
          (universalDerivedWord n),
        AlgHom.mapValue
          (Bialgebra.TensorProduct.includeRight (R := k)
            (H₁ := derivedWordCoordinateAlgebra H n)
            (H₂ := derivedWordCoordinateAlgebra H n)).toAlgHom
          (universalDerivedWord n)⁆

/-- Evaluate the leaves of a universal derived word at a specified tree of points. -/
def derivedWordEvaluation {A : Type u} [CommRing A] [Algebra k A] :
    (n : ℕ) → DerivedWordArgs (points (R := k) (H := H) (CommAlgCat.of k A)) n →
      derivedWordCoordinateAlgebra H n →ₐ[k] A
  | 0, .leaf g => g.ofConv
  | n + 1, .node x y => Algebra.TensorProduct.productMap
      (derivedWordEvaluation n x) (derivedWordEvaluation n y)

/-- Decode an algebra homomorphism out of a universal derived-word value algebra into its tree
of leaf points. -/
def derivedWordArgumentsOfAlgHom {A : Type u} [CommRing A] [Algebra k A] :
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

/-- Decoding an algebra homomorphism into leaf points and evaluating those leaves recovers the
homomorphism. -/
theorem derivedWordEvaluation_argumentsOfAlgHom {A : Type u} [CommRing A] [Algebra k A]
    (n : ℕ) (q : derivedWordCoordinateAlgebra H n →ₐ[k] A) :
    derivedWordEvaluation H n (derivedWordArgumentsOfAlgHom H n q) = q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      apply AlgHom.ext
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
          change (Algebra.TensorProduct.productMap
            (derivedWordEvaluation H n (derivedWordArgumentsOfAlgHom H n (q.comp
              (Bialgebra.TensorProduct.includeLeft (R := k)
                (H₁ := derivedWordCoordinateAlgebra H n)
                (H₂ := derivedWordCoordinateAlgebra H n)).toAlgHom)))
            (derivedWordEvaluation H n (derivedWordArgumentsOfAlgHom H n (q.comp
              (Bialgebra.TensorProduct.includeRight (R := k)
                (H₁ := derivedWordCoordinateAlgebra H n)
                (H₂ := derivedWordCoordinateAlgebra H n)).toAlgHom)))) (a ⊗ₜ[k] b) =
              q (a ⊗ₜ[k] b)
          rw [Algebra.TensorProduct.productMap_apply_tmul]
          rw [ih, ih]
          simp only [AlgHom.comp_apply]
          rw [show (Bialgebra.TensorProduct.includeLeft (R := k)
              (H₁ := derivedWordCoordinateAlgebra H n)
              (H₂ := derivedWordCoordinateAlgebra H n)).toAlgHom a =
                a ⊗ₜ[k] (1 : derivedWordCoordinateAlgebra H n) from
            Bialgebra.TensorProduct.includeLeft_apply a,
            show (Bialgebra.TensorProduct.includeRight (R := k)
              (H₁ := derivedWordCoordinateAlgebra H n)
              (H₂ := derivedWordCoordinateAlgebra H n)).toAlgHom b =
                (1 : derivedWordCoordinateAlgebra H n) ⊗ₜ[k] b from
            Bialgebra.TensorProduct.includeRight_apply b,
            ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      | add x y hx hy => simp only [map_add, hx, hy]

/-- Evaluating the universal point at a tree of points gives the corresponding derived word. -/
theorem mapValue_universalDerivedWord {A : Type u} [CommRing A] [Algebra k A]
    (n : ℕ) (x : DerivedWordArgs (points (R := k) (H := H) (CommAlgCat.of k A)) n) :
    AlgHom.mapValue (derivedWordEvaluation H n x) (universalDerivedWord H n) =
      derivedWord (points (R := k) (H := H) (CommAlgCat.of k A)) n x := by
  induction n with
  | zero =>
      cases x with
      | leaf g =>
          simp only [derivedWordEvaluation, universalDerivedWord, derivedWord_leaf]
          apply WithConv.ofConv_injective
          apply AlgHom.ext
          intro z
          rfl
  | succ n ih =>
      cases x with
      | node x y =>
       simp only [universalDerivedWord, derivedWord_node]
       change AlgHom.mapValue (Algebra.TensorProduct.productMap
         (derivedWordEvaluation H n x) (derivedWordEvaluation H n y))
           (id ⁅AlgHom.mapValue
               (Bialgebra.TensorProduct.includeLeft (R := k)
                 (H₁ := derivedWordCoordinateAlgebra H n)
                 (H₂ := derivedWordCoordinateAlgebra H n)).toAlgHom
               (universalDerivedWord H n),
             AlgHom.mapValue
               (Bialgebra.TensorProduct.includeRight (R := k)
                 (H₁ := derivedWordCoordinateAlgebra H n)
                 (H₂ := derivedWordCoordinateAlgebra H n)).toAlgHom
               (universalDerivedWord H n)⁆) = _
       rw [id_eq]
       rw [map_commutatorElement]
       congr 1
       · rw [← MonoidHom.comp_apply, ← AlgHom.mapValue_comp]
         have hleft : (Algebra.TensorProduct.productMap
           (derivedWordEvaluation H n x) (derivedWordEvaluation H n y)).comp
             (Bialgebra.TensorProduct.includeLeft (R := k)
               (H₁ := derivedWordCoordinateAlgebra H n)
               (H₂ := derivedWordCoordinateAlgebra H n)).toAlgHom =
                 derivedWordEvaluation H n x := by
           simpa only [Bialgebra.TensorProduct.includeLeft_toAlgHom] using
             Algebra.TensorProduct.productMap_left
               (derivedWordEvaluation H n x) (derivedWordEvaluation H n y)
         rw [hleft, ih x]
       · rw [← MonoidHom.comp_apply, ← AlgHom.mapValue_comp]
         have hright : (Algebra.TensorProduct.productMap
           (derivedWordEvaluation H n x) (derivedWordEvaluation H n y)).comp
             (Bialgebra.TensorProduct.includeRight (R := k)
               (H₁ := derivedWordCoordinateAlgebra H n)
               (H₂ := derivedWordCoordinateAlgebra H n)).toAlgHom =
                 derivedWordEvaluation H n y := by
           simpa only [Bialgebra.TensorProduct.includeRight_toAlgHom] using
             Algebra.TensorProduct.productMap_right
               (derivedWordEvaluation H n x) (derivedWordEvaluation H n y)
         rw [hright, ih y]

variable {H K : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Universal derived words are natural in the coordinate Hopf algebra. -/
theorem universalDerivedWord_natural (f : H →ₐc[k] K) (n : ℕ) :
    AlgHom.mapValue (derivedWordCoordinateAlgebra.map f n).toAlgHom
        (universalDerivedWord H n) =
      AlgHom.mapDomain f (universalDerivedWord K n) := by
  induction n with
  | zero =>
      apply WithConv.ofConv_injective
      ext h
      rfl
  | succ n ih =>
      change AlgHom.mapValue
        (Bialgebra.TensorProduct.map
          (derivedWordCoordinateAlgebra.map f n)
          (derivedWordCoordinateAlgebra.map f n)).toAlgHom
          ⁅AlgHom.mapValue
              (Bialgebra.TensorProduct.includeLeft (R := k)
                (H₁ := derivedWordCoordinateAlgebra H n)
                (H₂ := derivedWordCoordinateAlgebra H n)).toAlgHom
              (universalDerivedWord H n),
            AlgHom.mapValue
              (Bialgebra.TensorProduct.includeRight (R := k)
                (H₁ := derivedWordCoordinateAlgebra H n)
                (H₂ := derivedWordCoordinateAlgebra H n)).toAlgHom
              (universalDerivedWord H n)⁆ =
        AlgHom.mapDomain f
          ⁅AlgHom.mapValue
              (Bialgebra.TensorProduct.includeLeft (R := k)
                (H₁ := derivedWordCoordinateAlgebra K n)
                (H₂ := derivedWordCoordinateAlgebra K n)).toAlgHom
              (universalDerivedWord K n),
            AlgHom.mapValue
              (Bialgebra.TensorProduct.includeRight (R := k)
                (H₁ := derivedWordCoordinateAlgebra K n)
                (H₂ := derivedWordCoordinateAlgebra K n)).toAlgHom
              (universalDerivedWord K n)⁆
      rw [map_commutatorElement, map_commutatorElement]
      congr 1
      · rw [← MonoidHom.comp_apply, ← AlgHom.mapValue_comp]
        rw [← MonoidHom.comp_apply, AlgHom.mapValue_mapDomain]
        rw [MonoidHom.comp_apply, ← ih]
        rw [← MonoidHom.comp_apply, ← AlgHom.mapValue_comp]
        congr 2
        simpa only [Bialgebra.TensorProduct.map_toAlgHom,
          Bialgebra.TensorProduct.includeLeft_toAlgHom] using
            Algebra.TensorProduct.map_comp_includeLeft
              (derivedWordCoordinateAlgebra.map f n).toAlgHom
              (derivedWordCoordinateAlgebra.map f n).toAlgHom
      · rw [← MonoidHom.comp_apply, ← AlgHom.mapValue_comp]
        rw [← MonoidHom.comp_apply, AlgHom.mapValue_mapDomain]
        rw [MonoidHom.comp_apply, ← ih]
        rw [← MonoidHom.comp_apply, ← AlgHom.mapValue_comp]
        congr 2
        simpa only [Bialgebra.TensorProduct.map_toAlgHom,
          Bialgebra.TensorProduct.includeRight_toAlgHom] using
            Algebra.TensorProduct.map_comp_includeRight
              (derivedWordCoordinateAlgebra.map f n).toAlgHom
              (derivedWordCoordinateAlgebra.map f n).toAlgHom

end HopfAlgebra

namespace geometricallySolvablePointsCommHopfAlgProperty

variable {k : Type u} [Field k]
variable {H K : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Geometric solvability descends along an injective morphism of coordinate Hopf algebras whose
codomain is smooth and finite type.

Contravariantly, the morphism is a schematically dense homomorphism from the smooth source affine
group. A derived-word identity on its algebraic-closure-valued points holds in the universal
iterated tensor product by point separation, and injectivity reflects that identity to the target
group. -/
theorem of_injective_of_smooth (f : H ⟶ K) (hf : Function.Injective f.hom)
    (hK_smooth : Algebra.Smooth k K)
    (hK : geometricallySolvablePointsCommHopfAlgProperty k K.obj) :
    geometricallySolvablePointsCommHopfAlgProperty k H.obj := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff] at hK ⊢
  rw [isSolvable_iff_exists_derivedWord_eq_one] at hK ⊢
  obtain ⟨n, hn⟩ := hK
  refine ⟨n, fun x ↦ ?_⟩
  let f₀ := FiniteTypeCommHopfAlgCat.toBialgHom f
  let _ : Algebra.Smooth k (derivedWordCoordinateAlgebra K n) :=
    derivedWordCoordinateAlgebra.smooth hK_smooth n
  let _ : IsReduced (derivedWordCoordinateAlgebra K n) :=
    isReduced_of_smooth_of_field k (derivedWordCoordinateAlgebra K n)
  have hKuniv : HopfAlgebra.universalDerivedWord K n = 1 := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro z
    apply TauCeti.eq_of_forall_algHom_apply_eq
      (k := k) (K := AlgebraicClosure k)
    intro q
    let args := HopfAlgebra.derivedWordArgumentsOfAlgHom K n q
    have hq := HopfAlgebra.mapValue_universalDerivedWord K n args
    rw [HopfAlgebra.derivedWordEvaluation_argumentsOfAlgHom] at hq
    have hqz := congrArg (fun g : HopfAlgebra.points (R := k) (H := K)
      (CommAlgCat.of k (AlgebraicClosure k)) ↦ g.ofConv z) hq
    rw [hn] at hqz
    simpa [AlgHom.mapValue_apply, AlgHom.convOne_apply] using hqz
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
  rw [← HopfAlgebra.mapValue_universalDerivedWord (A := AlgebraicClosure k) H n x,
    hHuniv, map_one]

end geometricallySolvablePointsCommHopfAlgProperty

end

end TauCeti
