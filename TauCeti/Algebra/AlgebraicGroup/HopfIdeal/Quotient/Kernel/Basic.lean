/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Map

/-!
# The kernel Hopf ideal of a morphism of commutative Hopf algebras

For a morphism `f : H ⟶ K` of commutative Hopf algebras, the kernel Hopf ideal is the
extension of the augmentation ideal of `H` along `f` — the ideal `K·f(H⁺)` of the
codomain, which is the coordinate ring of the *source* of the induced morphism of affine
group schemes. Quotienting by it cuts out the kernel closed subgroup scheme
(`TauCeti.CommHopfAlgCat.kernelSpec`, in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Kernel`).

The kernel semantics live at this coordinate level: the trivialization criterion says a
map out of `K` kills the kernel Hopf ideal exactly when its composite with `f` is the
trivial (counit-unit) morphism, for an arbitrary ring-valued algebra target, for
Hopf-algebra morphisms, and for Hopf-ideal quotients; the coordinate-ring triangle is the
`mkQuotient` special case. The coordinate-level factorization and its uniqueness are
`TauCeti.CommHopfAlgCat.liftQuotient` and `TauCeti.CommHopfAlgCat.liftQuotient_unique`.

## Main declarations

* `TauCeti.CommHopfAlgCat.kernelHopfIdeal`: the kernel Hopf ideal of a morphism.
* `TauCeti.CommHopfAlgCat.kernelHopfIdeal_toIdeal_le_ker_iff` and
  `TauCeti.CommHopfAlgCat.comp_eq_unit_comp_counit_iff`: the trivialization criterion.
* `TauCeti.CommHopfAlgCat.comp_mkQuotient_kernelHopfIdeal`: the coordinate-ring triangle.
* `TauCeti.CommHopfAlgCat.kernelHopfIdeal_le_iff`: the Hopf-ideal-quotient form.

## References

Milne, *Algebraic Groups*, Proposition 4.1: the kernel of a homomorphism of affine
algebraic groups is represented by the quotient by this ideal.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R}

/-- The kernel Hopf ideal of a morphism of commutative Hopf algebras: the image of the
augmentation ideal of the source. It is an ideal of the *codomain* `K`, the coordinate
ring of the source of the induced group-scheme morphism `Spec K ⟶ Spec H`; its quotient
represents the kernel of that morphism. -/
noncomputable def kernelHopfIdeal (f : H ⟶ K) : HopfIdeal R K :=
  (HopfIdeal.augmentation R H).map f.hom

/-- `kernelHopfIdeal` is the extension of the augmentation ideal along the morphism. -/
theorem kernelHopfIdeal_def (f : H ⟶ K) :
    kernelHopfIdeal f = (HopfIdeal.augmentation R H).map f.hom := by
  -- `kernelHopfIdeal` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change (HopfIdeal.augmentation R H).map f.hom = _
  rfl

/-- The underlying ideal of the kernel Hopf ideal is the extension of the augmentation
ideal. -/
@[simp]
theorem kernelHopfIdeal_toIdeal (f : H ⟶ K) :
    (kernelHopfIdeal f).toIdeal =
      Ideal.map (f.hom : ↥H →+* ↥K) (HopfIdeal.augmentation R H).toIdeal := by
  -- `kernelHopfIdeal` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding to a `HopfIdeal.map` application.
  change ((HopfIdeal.augmentation R H).map f.hom).toIdeal = _
  rw [HopfIdeal.map_toIdeal]

/-- The kernel Hopf ideal contains the image of every counit-vanishing element. -/
theorem mem_kernelHopfIdeal_of_mem_augmentation (f : H ⟶ K) {x : H}
    (hx : Coalgebra.counit (R := R) x = 0) : f.hom x ∈ kernelHopfIdeal f :=
  HopfIdeal.mem_map_of_mem f.hom ((HopfIdeal.mem_augmentation R H).mpr hx)

-- Mathlib has no application lemma for `Bialgebra.unitBialgHom`; this contains its
-- definitional unfolding to `algebraMap` in one place (upstream candidate).
private lemma unitBialgHom_apply {A : Type*} [Semiring A] [Bialgebra R A] (r : R) :
    Bialgebra.unitBialgHom R A r = algebraMap R A r :=
  rfl

/-- The difference between a morphism value and the counit-unit value lies in the kernel
Hopf ideal. -/
private theorem sub_algebraMap_counit_mem_kernelHopfIdeal (f : H ⟶ K) (h : H) :
    f.hom h - algebraMap R K (Coalgebra.counit (R := R) h) ∈ kernelHopfIdeal f := by
  have hx : Coalgebra.counit (R := R)
      (h - algebraMap R H (Coalgebra.counit (R := R) h)) = 0 := by
    simp
  simpa [map_sub, AlgHomClass.commutes] using
    mem_kernelHopfIdeal_of_mem_augmentation f hx

/-- Algebra-level trivialization criterion: an algebra map out of the coordinate ring of
the source group scheme kills the kernel Hopf ideal exactly when its composite with `f`
is the counit-unit composite. This is the kernel property tested against an arbitrary
commutative `R`-algebra; `TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff` (in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel`) packages it on the functors of
points. -/
theorem kernelHopfIdeal_toIdeal_le_ker_iff (f : H ⟶ K) {A : Type w} [Ring A]
    [Algebra R A] (φ : ↥K →ₐ[R] A) :
    (kernelHopfIdeal f).toIdeal ≤ RingHom.ker φ.toRingHom ↔
      φ.comp (f.hom : ↥H →ₐ[R] ↥K) =
        (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R ↥H) := by
  constructor
  · intro hle
    ext h
    have hker := hle (HopfIdeal.mem_toIdeal.mpr (sub_algebraMap_counit_mem_kernelHopfIdeal f h))
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hker
    simpa [Algebra.ofId_apply, AlgHomClass.commutes] using hker
  · intro heq
    rw [kernelHopfIdeal_toIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    have hx0 : Coalgebra.counit (R := R) x = 0 :=
      (HopfIdeal.mem_augmentation R H).mp (HopfIdeal.mem_toIdeal.mp hx)
    have hval := congrArg (fun ψ : ↥H →ₐ[R] A => ψ x) heq
    simp only [AlgHom.comp_apply, Algebra.ofId_apply, Bialgebra.counitAlgHom_apply] at hval
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simpa [hx0] using hval

/-- The trivialization criterion for Hopf-algebra morphisms: a morphism out of `K` kills
the kernel Hopf ideal of `f` exactly when its composite with `f` is the trivial
(counit-unit) morphism. -/
theorem comp_eq_unit_comp_counit_iff (f : H ⟶ K) {L : _root_.CommHopfAlgCat.{v} R}
    (g : K ⟶ L) :
    f ≫ g =
        _root_.CommHopfAlgCat.ofHom
          ((Bialgebra.unitBialgHom R L).comp (Bialgebra.counitBialgHom R H)) ↔
      (kernelHopfIdeal f).toIdeal ≤ RingHom.ker g.hom.toAlgHom.toRingHom := by
  rw [kernelHopfIdeal_toIdeal_le_ker_iff f g.hom.toAlgHom]
  constructor
  · intro heq
    ext h
    have hval := congrArg (fun ψ : H ⟶ L => ψ.hom h) heq
    simpa [_root_.CommHopfAlgCat.comp_apply, _root_.CommHopfAlgCat.hom_ofHom,
      BialgHom.comp_apply, unitBialgHom_apply, Algebra.ofId_apply] using hval
  · intro heq
    ext h
    have hval := congrArg (fun ψ : ↥H →ₐ[R] ↥L => ψ h) heq
    simpa [_root_.CommHopfAlgCat.comp_apply, _root_.CommHopfAlgCat.hom_ofHom,
      BialgHom.comp_apply, unitBialgHom_apply, Algebra.ofId_apply] using hval

/-- The coordinate-ring triangle: composing `f` with the quotient by its kernel Hopf
ideal is the counit-unit composite, i.e. the coordinate map of the trivial group-scheme
morphism. -/
@[simp]
theorem comp_mkQuotient_kernelHopfIdeal (f : H ⟶ K) :
    f ≫ mkQuotient K (kernelHopfIdeal f) =
      _root_.CommHopfAlgCat.ofHom
        ((Bialgebra.unitBialgHom R (quotient K (kernelHopfIdeal f))).comp
          (Bialgebra.counitBialgHom R H)) :=
  (comp_eq_unit_comp_counit_iff f _).mpr (mkQuotient_ker K (kernelHopfIdeal f) ▸ le_rfl)

/-- The Hopf-ideal-quotient form of the trivialization criterion: `f` trivializes on the
closed subgroup scheme cut out by `J` exactly when `J` contains the kernel Hopf ideal.
Combined with `TauCeti.CommHopfAlgCat.quotientSpecMapOfLe` and
`TauCeti.CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι`, such a quotient closed
subgroup scheme includes into the kernel compatibly with the inclusions. -/
theorem kernelHopfIdeal_le_iff (f : H ⟶ K) {J : HopfIdeal R K} :
    kernelHopfIdeal f ≤ J ↔
      f ≫ mkQuotient K J =
        _root_.CommHopfAlgCat.ofHom
          ((Bialgebra.unitBialgHom R (quotient K J)).comp
            (Bialgebra.counitBialgHom R H)) := by
  rw [comp_eq_unit_comp_counit_iff, mkQuotient_ker]
  exact HopfIdeal.toIdeal_le_toIdeal.symm

end CommHopfAlgCat

end TauCeti
