/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Basic
public import TauCeti.LinearAlgebra.RootSystem.BraidRelation
public import TauCeti.LinearAlgebra.RootSystem.Inversions.Length

/-!
# The Coxeter presentation maps onto the Weyl group

The Coxeter matrix of a base gives an abstract presented group. Its generators map to the simple
reflections of the Weyl group because those reflections satisfy the Coxeter relations, and the
resulting homomorphism is surjective because the simple reflections generate the Weyl group.

This is the relation-and-generation half of the Coxeter presentation of a Weyl group. The remaining
half of Tits' theorem is injectivity: proving that the kernel is trivial, so that there are no
relations beyond the Coxeter relations.

## Main definitions

* `TauCeti.weylCoxeterHom`: the canonical homomorphism from the Coxeter group of a base to its Weyl
  group.

## Main results

* `TauCeti.weylCoxeterHom_apply_simple`: the abstract generator maps to the corresponding simple
  root reflection.
* `TauCeti.weylCoxeterHom_wordProd`: the homomorphism sends an abstract word to the same word in
  the Weyl group.
* `TauCeti.weylCoxeterHom_surjective`: the canonical homomorphism is surjective.
* `TauCeti.exists_coxeterWord_map_eq_and_length_eq_ncard_inversions`: every Weyl-group element has
  an abstract word preimage whose length is its number of inversions.

## References

This file advances the presentation item of Layer 2 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. It constructs the induced map from the
presented Coxeter group and proves the surjectivity that the roadmap obtains from generation. The
injectivity of this map is the remaining `weylCoxeterSystem` target.
-/

public section

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] (b : P.Base)

/-- The simple reflections of a base satisfy the relations of its Coxeter matrix. -/
lemma isLiftable_coxeterMatrixOfBase_ofIdx :
    (coxeterMatrixOfBase P b).IsLiftable
      (fun i : b.support => RootPairing.weylGroup.ofIdx P (i : ι)) :=
  RootPairing.weylGroup.pow_coxeterMatrixOfBase_ofIdx_mul_ofIdx_eq_one P b

/-- The canonical homomorphism from the abstract Coxeter group attached to a base to its Weyl
group, sending each abstract generator to the corresponding simple root reflection. -/
noncomputable def weylCoxeterHom :
    (coxeterMatrixOfBase P b).Group →* P.weylGroup :=
  (coxeterMatrixOfBase P b).toCoxeterSystem.lift
    ⟨fun i : b.support => RootPairing.weylGroup.ofIdx P (i : ι),
      isLiftable_coxeterMatrixOfBase_ofIdx P b⟩

/-- The canonical homomorphism sends an abstract Coxeter generator to the corresponding simple
root reflection. -/
@[simp]
theorem weylCoxeterHom_apply_simple (i : b.support) :
    weylCoxeterHom P b ((coxeterMatrixOfBase P b).simple i) =
      RootPairing.weylGroup.ofIdx P (i : ι) :=
  (coxeterMatrixOfBase P b).toCoxeterSystem.lift_apply_simple
    (isLiftable_coxeterMatrixOfBase_ofIdx P b) i

/-- The canonical homomorphism sends a word in the abstract Coxeter generators to the same word in
the simple reflections of the Weyl group. -/
@[simp]
theorem weylCoxeterHom_wordProd (l : List b.support) :
    weylCoxeterHom P b ((coxeterMatrixOfBase P b).toCoxeterSystem.wordProd l) = wordProd P b l := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, CoxeterMatrix.toCoxeterSystem_simple,
      weylCoxeterHom_apply_simple, ih, wordProd_cons]

variable [P.IsReduced]

/-- The canonical homomorphism from the Coxeter presentation to the Weyl group is surjective. -/
theorem weylCoxeterHom_surjective : Function.Surjective (weylCoxeterHom P b) := by
  intro w
  obtain ⟨l, hl⟩ := exists_wordProd_eq P b w
  exact ⟨(coxeterMatrixOfBase P b).toCoxeterSystem.wordProd l, by simpa using hl⟩

/-- The canonical homomorphism has the whole Weyl group as its range. -/
@[simp]
theorem weylCoxeterHom_range : (weylCoxeterHom P b).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (weylCoxeterHom_surjective P b)

/-- Every Weyl-group element is the image of an abstract Coxeter word whose length is exactly the
number of inversions of that element. This records the shortest preimage supplied by the root-level
length theorem, in the form consumed by the eventual injectivity proof. -/
theorem exists_coxeterWord_map_eq_and_length_eq_ncard_inversions (w : P.weylGroup) :
    ∃ l : List b.support,
      weylCoxeterHom P b ((coxeterMatrixOfBase P b).toCoxeterSystem.wordProd l) = w ∧
        l.length = (inversions P b w).ncard := by
  obtain ⟨l, hl, hlen⟩ := exists_wordProd_eq_and_length_eq_ncard_inversions P b w
  exact ⟨l, by simpa using hl, hlen⟩

end TauCeti
