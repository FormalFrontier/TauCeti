module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Induced

/-!
# Transitivity of induction and coinduction

This file records restriction and coinduction in stages for representations along composable monoid
homomorphisms, and induction in stages along composable group homomorphisms. It obtains the natural
isomorphisms from the functoriality of restriction and
Mathlib's induction--restriction and restriction--coinduction adjunctions. This is the categorical
core used by the subgroup form of induction in the induction and Mackey-theory roadmap.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w x

variable {k : Type u} {G : Type v} {H : Type w} {K : Type x}

namespace Rep

section Restriction

variable [Semiring k] [Monoid G] [Monoid H] [Monoid K]

/-- Restriction along two composable group homomorphisms is naturally isomorphic to restriction
along their composite. -/
noncomputable def resFunctorCompIso (φ : G →* H) (ψ : H →* K) :
    _root_.Rep.resFunctor.{max u v w x} (k := k) ψ ⋙
      _root_.Rep.resFunctor.{max u v w x} (k := k) φ ≅
        _root_.Rep.resFunctor.{max u v w x} (k := k) (ψ.comp φ) :=
  NatIso.ofComponents
    (fun A ↦ _root_.Rep.mkIso <|
      Representation.Equiv.mk (LinearEquiv.refl k A.V) fun _ ↦ by rfl)
    (by
      intro _ _ f
      ext
      rfl)

/-- The forward component of `resFunctorCompIso` acts as the identity on vectors. -/
@[simp↓]
lemma resFunctorCompIso_hom_app_apply (φ : G →* H) (ψ : H →* K) (A : _root_.Rep k K) (x : A.V) :
    ((resFunctorCompIso φ ψ).hom.app A) x = x :=
  by
    unfold resFunctorCompIso
    rfl

/-- The inverse component of `resFunctorCompIso` acts as the identity on vectors. -/
@[simp↓]
lemma resFunctorCompIso_inv_app_apply (φ : G →* H) (ψ : H →* K) (A : _root_.Rep k K) (x : A.V) :
    ((resFunctorCompIso φ ψ).inv.app A) x = x :=
  by
    unfold resFunctorCompIso
    rfl

/-- Restriction along a multiplicative equivalence is an equivalence of representation
categories. -/
noncomputable def resEquivalence (e : G ≃* H) :
    _root_.Rep k H ≌ _root_.Rep k G := by
  let unitIso :
      𝟭 (_root_.Rep k H) ≅
        _root_.Rep.resFunctor e.toMonoidHom ⋙
          _root_.Rep.resFunctor e.symm.toMonoidHom :=
    (NatIso.ofComponents
      (fun A ↦ _root_.Rep.mkIso <|
        Representation.Equiv.mk (LinearEquiv.refl k A.V) fun _ ↦ by
          change LinearMap.id.comp (A.ρ (e (e.symm _))) =
            (A.ρ _).comp LinearMap.id
          rw [LinearMap.id_comp, LinearMap.comp_id]
          rw [e.apply_symm_apply])
      (by
        intro A B f
        ext
        rfl)).symm.trans
      (resFunctorCompIso e.symm.toMonoidHom e.toMonoidHom).symm
  let counitIso :
      _root_.Rep.resFunctor e.symm.toMonoidHom ⋙
          _root_.Rep.resFunctor e.toMonoidHom ≅
        𝟭 (_root_.Rep k G) :=
    (resFunctorCompIso e.toMonoidHom e.symm.toMonoidHom).trans
      (NatIso.ofComponents
        (fun A ↦ _root_.Rep.mkIso <|
          Representation.Equiv.mk (LinearEquiv.refl k A.V) fun _ ↦ by
            change LinearMap.id.comp (A.ρ (e.symm (e _))) =
              (A.ρ _).comp LinearMap.id
            rw [LinearMap.id_comp, LinearMap.comp_id]
            rw [e.symm_apply_apply])
        (by
          intro A B f
          ext
          rfl))
  exact CategoryTheory.Equivalence.mk
    (_root_.Rep.resFunctor e.toMonoidHom)
    (_root_.Rep.resFunctor e.symm.toMonoidHom)
    unitIso counitIso

/-- The forward functor of restriction along an equivalence is restriction along its
underlying homomorphism. -/
@[simp]
theorem resEquivalence_functor (e : G ≃* H) :
    (resEquivalence (k := k) e).functor = _root_.Rep.resFunctor e.toMonoidHom := by
  rfl

/-- The inverse functor of restriction along an equivalence is restriction along the inverse
homomorphism. -/
@[simp]
theorem resEquivalence_inverse (e : G ≃* H) :
    (resEquivalence (k := k) e).inverse = _root_.Rep.resFunctor e.symm.toMonoidHom := by
  rfl

end Restriction

section Induction

variable [CommRing k] [Group G] [Group H] [Group K]

/-- Induction in stages: induction along a composite is naturally isomorphic to successive
inductions along the two group homomorphisms. -/
noncomputable def indFunctorCompIso (φ : G →* H) (ψ : H →* K) :
    _root_.Rep.indFunctor.{max u v w x} k φ ⋙
      _root_.Rep.indFunctor.{max u v w x} k ψ ≅
        _root_.Rep.indFunctor.{max u v w x} k (ψ.comp φ) :=
  Adjunction.leftAdjointCompIso (_root_.Rep.indResAdjunction.{max u v w x} k φ)
    (_root_.Rep.indResAdjunction.{max u v w x} k ψ)
    (_root_.Rep.indResAdjunction.{max u v w x} k (ψ.comp φ))
    (resFunctorCompIso φ ψ)

/-- The induction-in-stages isomorphism is characterized by the restriction-composition
isomorphism under the adjunction equivalence. -/
@[simp]
lemma conjugateEquiv_indFunctorCompIso_inv (φ : G →* H) (ψ : H →* K) :
    conjugateEquiv
      ((_root_.Rep.indResAdjunction.{max u v w x} k φ).comp
        (_root_.Rep.indResAdjunction.{max u v w x} k ψ))
      (_root_.Rep.indResAdjunction.{max u v w x} k (ψ.comp φ))
      (indFunctorCompIso φ ψ).inv =
        (resFunctorCompIso φ ψ).hom :=
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

end Induction

section Coinduction

variable [CommRing k] [Monoid G] [Monoid H] [Monoid K]

/-- Coinduction in stages: successive coinductions are naturally isomorphic to coinduction along
the composite homomorphism. -/
noncomputable def coindFunctorCompIso (φ : G →* H) (ψ : H →* K) :
    _root_.Rep.coindFunctor.{max u v w x} k φ ⋙
      _root_.Rep.coindFunctor.{max u v w x} k ψ ≅
        _root_.Rep.coindFunctor.{max u v w x} k (ψ.comp φ) := by
  let adjφ := _root_.Rep.resCoindAdjunction.{max u v w x} k φ
  let adjψ := _root_.Rep.resCoindAdjunction.{max u v w x} k ψ
  let adjφψ := adjψ.comp adjφ
  let adjψφ := _root_.Rep.resCoindAdjunction.{max u v w x} k (ψ.comp φ)
  exact conjugateIsoEquiv adjφψ adjψφ (resFunctorCompIso φ ψ).symm

/-- The coinduction-in-stages isomorphism is characterized by the inverse
restriction-composition isomorphism under the inverse adjunction equivalence. -/
@[simp]
lemma conjugateEquiv_symm_coindFunctorCompIso_hom (φ : G →* H) (ψ : H →* K) :
    ((conjugateEquiv
      ((_root_.Rep.resCoindAdjunction.{max u v w x} k ψ).comp
        (_root_.Rep.resCoindAdjunction.{max u v w x} k φ))
      (_root_.Rep.resCoindAdjunction.{max u v w x} k (ψ.comp φ))).symm
      (coindFunctorCompIso φ ψ).hom) =
    (resFunctorCompIso φ ψ).inv := by
  unfold coindFunctorCompIso
  exact Equiv.symm_apply_apply _ _

end Coinduction

end Rep

end TauCeti
