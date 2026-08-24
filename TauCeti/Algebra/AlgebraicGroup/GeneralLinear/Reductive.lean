/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.Reductive.LinearlyReductive
import TauCeti.Algebra.AlgebraicGroup.Representation.ClosedSubgroup
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding

/-!
# The general linear group is reductive

The coordinate Hopf algebra of `GL_n` is reductive over every field and in every natural rank.
The proof uses the geometric definition, so it works in arbitrary characteristic.

First, the determinant localization defining `O(GL_n)` is smooth and geometrically connected.
For the normal-subgroup condition, work over an algebraically closed field and let `I` cut out a
normal smooth unipotent closed subgroup. The simple standard `GL_n`-comodule is completely
reducible, so the general normal-unipotent elimination theorem makes the subgroup act trivially.
Faithfulness of the standard representation then identifies `I` with the augmentation ideal.

The final theorem transports this argument across the canonical identification

`AlgebraicClosure k ⊗[k] O(GL_n) ≃ O(GL_n, AlgebraicClosure k)`.

## Main declarations

* `TauCeti.GeneralLinear.eq_augmentation_of_isNormal_of_smoothUnipotent`: a normal smooth
  unipotent closed subgroup of `GL_n` over an algebraically closed field is trivial.
* `TauCeti.GeneralLinear.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`:
  **`GL_n` is reductive.**

## References

* J. S. Milne, *Algebraic Groups* (2017), §§4.a, 5, 19.b, and Chapter 14.
* T. A. Springer, *Linear Algebraic Groups*, §§2.2 and 2.4.

This gives the reductivity half of the `GL_n` worked example requested alongside Layer 6,
"Reductive and semisimple groups", of the ReductiveGroups roadmap. The characteristic-zero
complete-reducibility route remains open.
-/

public section

open CategoryTheory

namespace TauCeti.GeneralLinear

universe u v

noncomputable section

open HopfIdeal

/-- The coordinate Hopf algebra and the underlying object of its finite-type package are
canonically identical. -/
private noncomputable def coordinateHopfAlgebraFiniteTypeObjIso
    (R : Type u) [CommRing R] (n : Nat) :
    coordinateHopfAlgebra R n ≅ (finiteTypeCoordinateHopfAlgebra R n).obj :=
  eqToIso (finiteTypeCoordinateHopfAlgebra_obj R n).symm

/-- A normal smooth unipotent closed subgroup of `GL_n` over an algebraically closed field is
trivial. No positivity hypothesis on `n` is needed. -/
theorem eq_augmentation_of_isNormal_of_smoothUnipotent
    (k : Type u) [Field k] [IsAlgClosed k] (n : Nat)
    (I : HopfIdeal k (finiteTypeCoordinateHopfAlgebra k n)) (hI : I.IsNormal)
    (hU : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra k n) I)) :
    I = HopfIdeal.augmentation k (finiteTypeCoordinateHopfAlgebra k n) := by
  let e := coordinateHopfAlgebraFiniteTypeObjIso k n
  let f : coordinateHopfAlgebra k n →ₐc[k] (finiteTypeCoordinateHopfAlgebra k n) :=
    CommHopfAlgCat.ofIso e
  have hf : Function.Bijective f := ConcreteCategory.bijective_of_isIso e.hom
  let J : HopfIdeal k (coordinateHopfAlgebra k n) := I.comap f hf.2
  have hJnormal : J.IsNormal := hI.comap_of_bijective f hf.1 hf.2
  let qIso : CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) J ≅
      CommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra k n).obj I :=
    CommHopfAlgCat.quotientIsoOfIso e I
  have hU' := (smoothUnipotentCommHopfAlgProperty_iff k
    (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra k n) I)).mp hU
  let _ : Algebra.Smooth k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) J) :=
    (smoothCommHopfAlgProperty_iff _).mp <|
      (smoothCommHopfAlgProperty k).prop_of_iso qIso.symm
        ((smoothCommHopfAlgProperty_iff _).mpr hU'.1)
  have hJunipotent : geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) J) :=
    (geometricallyUnipotentPointsCommHopfAlgProperty k).prop_of_iso qIso.symm
      ((geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).mpr hU'.2)
  let _ : IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) J) :=
    isReduced_of_smooth_of_field k _
  let _ : Comodule k (coordinateHopfAlgebra k n) (Fin n → k) := standardComodule k n
  have hu :=
    geometricallyUnipotentPointsCommHopfAlgProperty.forall_isUnipotentPoint hJunipotent
  have hcr : Comodule.IsCompletelyReducible k (coordinateHopfAlgebra k n) (Fin n → k) := by
    apply Comodule.IsCompletelyReducible.of_exists_isCompl
    intro W
    cases n with
    | zero =>
        have hW : W = ⊥ := by
          ext m
          constructor
          · intro _
            rw [Subcomodule.mem_bot]
            exact Subsingleton.elim _ _
          · intro hm
            exact (Subcomodule.mem_bot.mp hm) ▸ zero_mem W
        refine ⟨⊤, ?_⟩
        simpa [hW] using
          (isCompl_bot_top : IsCompl (⊥ : Submodule k (Fin 0 → k)) ⊤)
    | succ n =>
        let _ : NeZero n.succ := ⟨Nat.succ_ne_zero n⟩
        exact (eq_bot_or_eq_top W).elim
          (fun h ↦ ⟨⊤, by
            simpa [h] using
              (isCompl_bot_top : IsCompl (⊥ : Submodule k (Fin n.succ → k)) ⊤)⟩)
          (fun h ↦ ⟨⊥, by
            simpa [h] using
              (isCompl_top_bot : IsCompl (⊤ : Submodule k (Fin n.succ → k)) ⊥)⟩)
  have htrivial :=
    mkQuotient_coact_eq_tmul_one_of_isNormal_of_forall_isUnipotentPoint_of_isCompletelyReducible
      hJnormal hu hcr
  have hJ : J = HopfIdeal.augmentation k (coordinateHopfAlgebra k n) :=
    Comodule.eq_augmentation_of_isFaithful_of_quotient_coact_eq_tmul_one J
      (isFaithful_standardComodule k n) htrivial
  rw [← HopfIdeal.comap_eq_comap_iff_of_surjective f hf.2,
    HopfIdeal.comap_augmentation]
  exact hJ

/-- **The general linear group is reductive over every field.** -/
theorem reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra
    (k : Type u) [Field k] (n : Nat) :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k n) := by
  rw [reductiveCommHopfAlgProperty_iff]
  let e := coordinateHopfAlgebraFiniteTypeObjIso k n
  refine ⟨(smoothCommHopfAlgProperty_iff _).mp <|
      (smoothCommHopfAlgProperty k).prop_of_iso e
        ((smoothCommHopfAlgProperty_iff _).mpr inferInstance),
    (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e
      (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k n), ?_⟩
  intro I hI _ hU
  let K := AlgebraicClosure k
  let Hbar := FiniteTypeCommHopfAlgCat.baseChange (K := K)
    (finiteTypeCoordinateHopfAlgebra k n)
  let Gbar := finiteTypeCoordinateHopfAlgebra K n
  let e : Hbar ≅ Gbar := finiteTypeCoordinateHopfAlgebraBaseChangeIso k K n
  let f : Gbar →ₐc[K] Hbar := FiniteTypeCommHopfAlgCat.toBialgHom e.inv
  have hf : Function.Bijective f := ConcreteCategory.bijective_of_isIso e.inv
  let J : HopfIdeal K Gbar := I.comap f hf.2
  have hJnormal : J.IsNormal := hI.comap_of_bijective f hf.1 hf.2
  let qIso : FiniteTypeCommHopfAlgCat.quotient Gbar J ≅
      FiniteTypeCommHopfAlgCat.quotient Hbar I :=
    FiniteTypeCommHopfAlgCat.quotientIsoOfIso e.symm I
  have hJU : smoothUnipotentCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient Gbar J) :=
    (smoothUnipotentCommHopfAlgProperty K).prop_of_iso qIso.symm hU
  have hJ : J = HopfIdeal.augmentation K Gbar :=
    eq_augmentation_of_isNormal_of_smoothUnipotent K n J hJnormal hJU
  rw [← HopfIdeal.comap_eq_comap_iff_of_surjective f hf.2,
    HopfIdeal.comap_augmentation]
  exact hJ

end

end TauCeti.GeneralLinear
