/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!
# Group-like elements of monoid algebras

Over a commutative ring with connected prime spectrum, the group-like elements of a
monoid algebra are exactly its standard basis elements. The proof compares coefficients
in the group-like comultiplication identity. Connectedness makes every idempotent
coefficient zero or one, and the counit condition excludes the zero element.

Consequently, a bialgebra morphism between monoid algebras over such a base uniquely
recovers the monoid homomorphism on their standard basis indices. This gives a two-sided
inverse to `MonoidAlgebra.mapDomainBialgHom` on the corresponding hom-sets.

## Main declarations

* `TauCeti.MonoidAlgebra.isGroupLikeElem_single_one`: standard basis elements are
  group-like.
* `TauCeti.MonoidAlgebra.isGroupLikeElem_iff_eq_single`: classification of group-like
  elements in a monoid algebra over a connected base.
* `TauCeti.MonoidAlgebra.mapDomainBialgHomPreimage`: recover the monoid homomorphism
  inducing a bialgebra morphism between monoid algebras over a connected base.
* `TauCeti.MonoidAlgebra.mapDomainBialgHom_surjective`: every bialgebra morphism between
  monoid algebras over a connected base is induced by a monoid homomorphism.
-/

public section

namespace TauCeti

universe u v w

namespace MonoidAlgebra

variable (R : Type u)

private theorem eq_zero_or_eq_one_of_isIdempotentElem
    [CommRing R] [ConnectedSpace (PrimeSpectrum R)] (e : R) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have hopen : IsClopen
      (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases _root_.isClopen_iff.mp hopen with hempty | huniv
  · left
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he .zero
    apply SetLike.ext'
    simpa only [PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.coe_bot] using hempty
  · right
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he .one
    apply SetLike.ext'
    simpa only [PrimeSpectrum.basicOpen_one, TopologicalSpace.Opens.coe_top] using huniv

/-- A standard basis element of a monoid algebra with coefficient one is group-like. -/
@[simp]
theorem isGroupLikeElem_single_one [CommSemiring R] {H : Type v} [Monoid H] (h : H) :
    IsGroupLikeElem R (_root_.MonoidAlgebra.single h (1 : R)) := by
  constructor
  · simp
  · rw [_root_.MonoidAlgebra.comul_single, CommSemiring.comul_apply]
    simp

private theorem tensorEquiv_comul_apply [CommSemiring R]
    {H : Type v} [Monoid H] [DecidableEq H]
    (x : _root_.MonoidAlgebra R H) (g h : H) :
    (_root_.MonoidAlgebra.tensorEquiv R (Coalgebra.comul x)).coeff (g, h) =
      if g = h then x.coeff g else 0 := by
  induction x using _root_.MonoidAlgebra.induction_on with
  | of k =>
      by_cases hgh : g = h <;>
        simp_all [Finsupp.single_apply]
  | add x y hx hy =>
      by_cases hgh : g = h <;> simp_all
  | smul r x hx =>
      by_cases hgh : g = h <;> simp_all

/-- Over a commutative ring with connected prime spectrum, the group-like elements
of a monoid algebra are exactly its standard basis elements, with a unique basis
index. -/
theorem isGroupLikeElem_iff_eq_single [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {H : Type v} [Monoid H]
    (x : _root_.MonoidAlgebra R H) :
    IsGroupLikeElem R x ↔
      ∃! h : H, x = _root_.MonoidAlgebra.single h 1 := by
  classical
  letI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  constructor
  · intro hx
    have hcoeff (g h : H) :
        (if g = h then x.coeff g else 0) = x.coeff g * x.coeff h := by
      have hcomul := congrArg
        (fun y : TensorProduct R (_root_.MonoidAlgebra R H) (_root_.MonoidAlgebra R H) =>
          (_root_.MonoidAlgebra.tensorEquiv R y).coeff (g, h)) hx.comul_eq_tmul_self
      rw [tensorEquiv_comul_apply] at hcomul
      simpa using hcomul
    have hcoeff_zero_or_one (g : H) : x.coeff g = 0 ∨ x.coeff g = 1 := by
      apply eq_zero_or_eq_one_of_isIdempotentElem R
      exact isIdempotentElem_iff.mpr (by simpa using (hcoeff g g).symm)
    have hx_coeff_ne : x.coeff ≠ 0 := by
      intro hzero
      apply hx.ne_zero
      apply _root_.MonoidAlgebra.coeff_injective
      simpa using hzero
    obtain ⟨h, hh⟩ := Finsupp.support_nonempty_iff.mpr hx_coeff_ne
    have hh_one : x.coeff h = 1 :=
      (hcoeff_zero_or_one h).resolve_left (Finsupp.mem_support_iff.mp hh)
    have hx_single : x = _root_.MonoidAlgebra.single h 1 := by
      apply _root_.MonoidAlgebra.ext
      ext k
      by_cases hk : k = h
      · subst k
        simp [hh_one]
      · have hk_zero : x.coeff k = 0 := by
          have horth := hcoeff k h
          rw [if_neg hk, hh_one, mul_one] at horth
          exact horth.symm
        simp [hk, hk_zero]
    refine ⟨h, hx_single, ?_⟩
    intro h' hx_single'
    exact _root_.MonoidAlgebra.single_left_injective
      (R := R) (M := H) one_ne_zero (hx_single'.symm.trans hx_single)
  · rintro ⟨h, rfl, -⟩
    exact isGroupLikeElem_single_one R h

/-- The unique index of a group-like element in a monoid algebra over a base with
connected prime spectrum. -/
private noncomputable def groupLikeIndex [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {H : Type w} [Monoid H]
    (x : _root_.MonoidAlgebra R H) (hx : IsGroupLikeElem R x) : H :=
  Classical.choose ((isGroupLikeElem_iff_eq_single R x).mp hx)

private theorem eq_single_groupLikeIndex [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {H : Type w} [Monoid H]
    (x : _root_.MonoidAlgebra R H) (hx : IsGroupLikeElem R x) :
    x = _root_.MonoidAlgebra.single (groupLikeIndex R x hx) 1 :=
  Classical.choose_spec ((isGroupLikeElem_iff_eq_single R x).mp hx) |>.1

private theorem groupLikeIndex_eq_iff [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {H : Type w} [Monoid H]
    (x : _root_.MonoidAlgebra R H) (hx : IsGroupLikeElem R x) (h : H) :
    groupLikeIndex R x hx = h ↔ x = _root_.MonoidAlgebra.single h 1 := by
  letI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  constructor
  · rintro rfl
    exact eq_single_groupLikeIndex R x hx
  · intro hx_single
    apply _root_.MonoidAlgebra.single_left_injective (R := R) (M := H) one_ne_zero
    exact (eq_single_groupLikeIndex R x hx).symm.trans hx_single

/-- Recover the monoid homomorphism inducing a bialgebra morphism between monoid
algebras over a base with connected prime spectrum. -/
noncomputable def mapDomainBialgHomPreimage [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {G : Type v} {H : Type w}
    [Monoid G] [Monoid H]
    (F : _root_.MonoidAlgebra R G →ₐc[R] _root_.MonoidAlgebra R H) : G →* H :=
  letI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let φ : G → H := fun g ↦
    groupLikeIndex R (F (_root_.MonoidAlgebra.single g 1))
      ((isGroupLikeElem_single_one R g).map F)
  have hφ (g : G) :
      F (_root_.MonoidAlgebra.single g 1) =
        _root_.MonoidAlgebra.single (φ g) 1 :=
    eq_single_groupLikeIndex R _ _
  { toFun := φ
    map_one' := by
      apply _root_.MonoidAlgebra.single_left_injective (R := R) (M := H) one_ne_zero
      calc
        _root_.MonoidAlgebra.single (φ 1) 1 =
            F (_root_.MonoidAlgebra.single 1 1) := (hφ 1).symm
        _ = F 1 := congrArg F _root_.MonoidAlgebra.one_def.symm
        _ = 1 := map_one F
        _ = _root_.MonoidAlgebra.single 1 1 := _root_.MonoidAlgebra.one_def
    map_mul' := by
      intro g g'
      apply _root_.MonoidAlgebra.single_left_injective (R := R) (M := H) one_ne_zero
      calc
        _root_.MonoidAlgebra.single (φ (g * g')) 1 =
            F (_root_.MonoidAlgebra.single (g * g') 1) := (hφ (g * g')).symm
        _ = F (_root_.MonoidAlgebra.single g 1 *
            _root_.MonoidAlgebra.single g' 1) := by simp
        _ = F (_root_.MonoidAlgebra.single g 1) *
            F (_root_.MonoidAlgebra.single g' 1) := map_mul F _ _
        _ = _root_.MonoidAlgebra.single (φ g) 1 *
            _root_.MonoidAlgebra.single (φ g') 1 := by rw [hφ g, hφ g']
        _ = _root_.MonoidAlgebra.single (φ g * φ g') 1 := by simp }

/-- The recovered monoid homomorphism takes `g` to `h` exactly when the bialgebra
morphism takes the corresponding standard basis element to the standard basis element
indexed by `h`. -/
theorem mapDomainBialgHomPreimage_apply_eq_iff [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {G : Type v} {H : Type w}
    [Monoid G] [Monoid H]
    (F : _root_.MonoidAlgebra R G →ₐc[R] _root_.MonoidAlgebra R H)
    (g : G) (h : H) :
    mapDomainBialgHomPreimage R F g = h ↔
      F (_root_.MonoidAlgebra.single g 1) = _root_.MonoidAlgebra.single h 1 := by
  let hx : IsGroupLikeElem R (F (_root_.MonoidAlgebra.single g 1)) :=
    (isGroupLikeElem_single_one R g).map F
  simpa only [mapDomainBialgHomPreimage, MonoidHom.coe_mk, OneHom.coe_mk] using
    groupLikeIndex_eq_iff R (F (_root_.MonoidAlgebra.single g 1)) hx h

/-- The image of a standard basis element under a bialgebra morphism is indexed by
the recovered monoid homomorphism. -/
@[simp]
theorem mapDomainBialgHomPreimage_single [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {G : Type v} {H : Type w}
    [Monoid G] [Monoid H]
    (F : _root_.MonoidAlgebra R G →ₐc[R] _root_.MonoidAlgebra R H) (g : G) :
    F (_root_.MonoidAlgebra.single g 1) =
      _root_.MonoidAlgebra.single (mapDomainBialgHomPreimage R F g) 1 := by
  exact (mapDomainBialgHomPreimage_apply_eq_iff R F g _).mp rfl

/-- Mapping the domain by the recovered monoid homomorphism gives the original
bialgebra morphism. -/
@[simp]
theorem mapDomainBialgHom_mapDomainBialgHomPreimage [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {G : Type v} {H : Type w}
    [Monoid G] [Monoid H]
    (F : _root_.MonoidAlgebra R G →ₐc[R] _root_.MonoidAlgebra R H) :
    _root_.MonoidAlgebra.mapDomainBialgHom R (mapDomainBialgHomPreimage R F) = F := by
  apply BialgHom.coe_toAlgHom_injective
  apply _root_.MonoidAlgebra.algHom_ext
  · intro g
    exact (_root_.MonoidAlgebra.mapDomain_single (R := R) (f :=
      mapDomainBialgHomPreimage R F)).trans
        (mapDomainBialgHomPreimage_single R F g).symm
  · ext

/-- Over a nontrivial base, distinct monoid homomorphisms induce distinct bialgebra
morphisms between monoid algebras. -/
theorem mapDomainBialgHom_injective [CommSemiring R] [Nontrivial R]
    {G : Type v} {H : Type w} [Monoid G] [Monoid H] :
    Function.Injective (_root_.MonoidAlgebra.mapDomainBialgHom R :
      (G →* H) →
        (_root_.MonoidAlgebra R G →ₐc[R] _root_.MonoidAlgebra R H)) := by
  intro φ ψ h
  ext g
  apply _root_.MonoidAlgebra.single_left_injective (R := R) (M := H) one_ne_zero
  calc
    _root_.MonoidAlgebra.single (φ g) 1 =
        _root_.MonoidAlgebra.mapDomainBialgHom R φ
          (_root_.MonoidAlgebra.single g 1) :=
      (_root_.MonoidAlgebra.mapDomain_single (R := R) (f := φ)).symm
    _ = _root_.MonoidAlgebra.mapDomainBialgHom R ψ
          (_root_.MonoidAlgebra.single g 1) := by rw [h]
    _ = _root_.MonoidAlgebra.single (ψ g) 1 :=
      _root_.MonoidAlgebra.mapDomain_single

/-- Recovering from the bialgebra morphism induced by a monoid homomorphism returns
that monoid homomorphism. -/
@[simp]
theorem mapDomainBialgHomPreimage_mapDomainBialgHom [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {G : Type v} {H : Type w}
    [Monoid G] [Monoid H] (φ : G →* H) :
    mapDomainBialgHomPreimage R (_root_.MonoidAlgebra.mapDomainBialgHom R φ) = φ := by
  ext g
  apply (mapDomainBialgHomPreimage_apply_eq_iff R _ g _).mpr
  exact _root_.MonoidAlgebra.mapDomain_single

/-- Every bialgebra morphism between monoid algebras over a base with connected prime
spectrum is induced by a monoid homomorphism. -/
theorem mapDomainBialgHom_surjective [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {G : Type v} {H : Type w}
    [Monoid G] [Monoid H] :
    Function.Surjective (_root_.MonoidAlgebra.mapDomainBialgHom R :
      (G →* H) →
        (_root_.MonoidAlgebra R G →ₐc[R] _root_.MonoidAlgebra R H)) := by
  intro F
  exact ⟨mapDomainBialgHomPreimage R F, mapDomainBialgHom_mapDomainBialgHomPreimage R F⟩

end MonoidAlgebra

end TauCeti
