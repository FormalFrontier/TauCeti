/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Algebra.Bialgebra.Quotient
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Comap

/-!
# Hopf-ideal quotients of finite-type commutative Hopf algebras

This file packages the quotient of a finite-type commutative Hopf algebra by a Hopf ideal
as another object of `FiniteTypeCommHopfAlgCat`. The Hopf algebra structure and quotient
bialgebra morphism are supplied by Mathlib's quotient instances and morphisms; the only extra
ingredient here is that finite type descends along the surjective quotient algebra map.

This is a small Layer 3 prerequisite for the reductive-groups roadmap target
"Hopf ideals ↔ closed subgroup schemes": once closed subgroup schemes are represented by
Hopf ideals on coordinate rings, their quotient coordinate Hopf algebras should remain in
the finite-type coordinate-Hopf-algebra category.

## Main declarations

* `TauCeti.CommHopfAlgCat.quotient`: the quotient object in `CommHopfAlgCat`.
* `TauCeti.FiniteTypeCommHopfAlgCat.quotient`: the quotient object in
  `FiniteTypeCommHopfAlgCat`.
* `TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient`: the quotient morphism.
* `TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_ker`: its kernel characterization.
* `TauCeti.FiniteTypeCommHopfAlgCat.liftQuotient`: the induced morphism out of a quotient.
* `TauCeti.CommHopfAlgCat.quotientMapOfLe`: the morphism `H ⧸ I ⟶ H ⧸ J` induced by
  `I ≤ J`.
* `TauCeti.CommHopfAlgCat.quotientBotIso`: quotienting by the zero Hopf ideal does not
  change a commutative Hopf algebra.
* `TauCeti.CommHopfAlgCat.quotientIsoOfIso`: an ambient isomorphism induces an isomorphism
  between the corresponding Hopf-ideal quotients.

## References

The quotient Hopf algebra construction is Mathlib's
(`Mathlib.RingTheory.HopfAlgebra.Quotient`), applied through the instances of
`TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic`; see Sweedler, *Hopf Algebras*, Chapter 4, and
Waterhouse, *Introduction to Affine Group Schemes*, §16. The finite-type descent is Mathlib's
`Algebra.FiniteType.quotient`.
-/

public section

namespace TauCeti

universe u v

namespace CommHopfAlgCat

open CategoryTheory
open _root_.CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The quotient of a commutative Hopf algebra by a Hopf ideal, as a bundled commutative
Hopf algebra. -/
noncomputable abbrev quotient (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    _root_.CommHopfAlgCat.{v} R :=
  _root_.CommHopfAlgCat.of R (H ⧸ I.toIdeal)

/-- The quotient morphism `H ⟶ H ⧸ I` in `CommHopfAlgCat`. -/
noncomputable abbrev mkQuotient (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    H ⟶ quotient H I :=
  _root_.CommHopfAlgCat.ofHom (Bialgebra.Quotient.mkBialgHom I.toIdeal)

/-- The quotient morphism has the expected underlying bialgebra morphism. -/
lemma hom_mkQuotient (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    (mkQuotient H I).hom = Bialgebra.Quotient.mkBialgHom I.toIdeal :=
  _root_.CommHopfAlgCat.hom_ofHom _

/-- The quotient morphism sends an element to its quotient class. -/
lemma mkQuotient_apply (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) (h : H) :
    (mkQuotient H I).hom h = Ideal.Quotient.mkₐ R I.toIdeal h := by
  rw [hom_mkQuotient, Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.mkₐ_eq_mk]

/-- The kernel of the quotient morphism is the Hopf ideal being quotiented by. -/
lemma mkQuotient_ker (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    RingHom.ker (mkQuotient H I).hom.toAlgHom.toRingHom = I.toIdeal := by
  rw [hom_mkQuotient]
  exact Ideal.Quotient.mkₐ_ker (R₁ := R) I.toIdeal

/-- An element maps to zero in the quotient exactly when it belongs to the Hopf ideal. -/
lemma mkQuotient_eq_zero_iff (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) (h : H) :
    (mkQuotient H I).hom h = 0 ↔ h ∈ I.toIdeal := by
  rw [mkQuotient_apply]
  exact Ideal.Quotient.eq_zero_iff_mem

variable {H K : _root_.CommHopfAlgCat.{v} R}

/-- A morphism of commutative Hopf algebras out of `H` which kills a Hopf ideal factors
through the quotient object. -/
noncomputable abbrev liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom) : quotient H I ⟶ K :=
  _root_.CommHopfAlgCat.ofHom (Bialgebra.Quotient.liftBialgHom I.toIdeal f.hom hf)

/-- The quotient lift has the expected underlying bialgebra morphism. -/
lemma hom_liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom) :
    (liftQuotient I f hf).hom = Bialgebra.Quotient.liftBialgHom I.toIdeal f.hom hf :=
  _root_.CommHopfAlgCat.hom_ofHom _

/-- The quotient lift evaluates on quotient classes as the original morphism. -/
lemma liftQuotient_mk (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom) (h : H) :
    (liftQuotient I f hf).hom (Ideal.Quotient.mkₐ R I.toIdeal h) =
      f.hom h :=
  Bialgebra.Quotient.liftBialgHom_mk I.toIdeal f.hom hf h

/-- The quotient lift composed with the quotient morphism is the original morphism. -/
@[simp]
lemma mkQuotient_comp_liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom) :
    mkQuotient H I ≫ liftQuotient I f hf = f := by
  ext h
  exact BialgHom.congr_fun
    (Bialgebra.Quotient.liftBialgHom_comp_mkBialgHom I.toIdeal f.hom hf) h

/-- A morphism out of the quotient object is determined by its precomposition with the
quotient morphism. -/
lemma liftQuotient_unique (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom) (g : quotient H I ⟶ K)
    (hg : mkQuotient H I ≫ g = f) : g = liftQuotient I f hf := by
  ext q
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q
  calc
    g.hom (Ideal.Quotient.mkₐ R I.toIdeal h) =
        (mkQuotient H I ≫ g).hom h := by
      rw [_root_.CommHopfAlgCat.comp_apply, mkQuotient_apply]
    _ = f.hom h := by rw [hg]
    _ = (liftQuotient I f hf).hom (Ideal.Quotient.mkₐ R I.toIdeal h) :=
      (liftQuotient_mk I f hf h).symm

/-- An isomorphism of commutative Hopf algebras induces an isomorphism from the quotient by
the inverse-image Hopf ideal to the corresponding quotient of the target. -/
noncomputable def quotientIsoOfIso (e : H ≅ K) (I : HopfIdeal R K) :
    quotient H (I.comap e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2) ≅
      quotient K I := by
  let J := I.comap e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2
  let φ : quotient H J ⟶ quotient K I :=
    liftQuotient J (e.hom ≫ mkQuotient K I) (by
      intro x hx
      rw [RingHom.mem_ker]
      change (mkQuotient K I).hom (e.hom.hom x) = 0
      rw [mkQuotient_eq_zero_iff]
      exact HopfIdeal.mem_toIdeal.mpr (HopfIdeal.mem_comap.mp (HopfIdeal.mem_toIdeal.mp hx)))
  let ψ : quotient K I ⟶ quotient H J :=
    liftQuotient I (e.inv ≫ mkQuotient H J) (by
      intro y hy
      rw [RingHom.mem_ker]
      change (mkQuotient H J).hom (e.inv.hom y) = 0
      rw [mkQuotient_eq_zero_iff]
      apply HopfIdeal.mem_toIdeal.mpr
      apply HopfIdeal.mem_comap.mpr
      simpa using HopfIdeal.mem_toIdeal.mp hy)
  exact
    { hom := φ
      inv := ψ
      hom_inv_id := by
        ext q
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R J.toIdeal q
        simp [φ, ψ]
      inv_hom_id := by
        ext q
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q
        simp [φ, ψ] }

/-- The forward map of the quotient isomorphism commutes with the quotient morphisms. -/
@[simp]
lemma mkQuotient_comp_quotientIsoOfIso_hom (e : H ≅ K) (I : HopfIdeal R K) :
    mkQuotient H (I.comap e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2) ≫
        (quotientIsoOfIso e I).hom =
      e.hom ≫ mkQuotient K I := by
  simp only [quotientIsoOfIso]
  apply mkQuotient_comp_liftQuotient

/-- The inverse map of the quotient isomorphism commutes with the quotient morphisms. -/
@[simp]
lemma mkQuotient_comp_quotientIsoOfIso_inv (e : H ≅ K) (I : HopfIdeal R K) :
    mkQuotient K I ≫ (quotientIsoOfIso e I).inv =
      e.inv ≫ mkQuotient H
        (I.comap e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2) := by
  simp only [quotientIsoOfIso]
  apply mkQuotient_comp_liftQuotient

private lemma bot_le_ker_id (H : _root_.CommHopfAlgCat.{v} R) :
    (⊥ : HopfIdeal R H).toIdeal ≤
      RingHom.ker (𝟙 H : H ⟶ H).hom.toAlgHom.toRingHom := by
  simp

/-- Quotienting a commutative Hopf algebra by the zero Hopf ideal gives an isomorphic object
of `CommHopfAlgCat`. -/
noncomputable def quotientBotIso (H : _root_.CommHopfAlgCat.{v} R) :
    quotient H (⊥ : HopfIdeal R H) ≅ H where
  hom := liftQuotient (⊥ : HopfIdeal R H) (𝟙 H) (bot_le_ker_id H)
  inv := mkQuotient H (⊥ : HopfIdeal R H)
  hom_inv_id := by
    ext q
    obtain ⟨h, rfl⟩ :=
      Ideal.Quotient.mkₐ_surjective R (⊥ : HopfIdeal R H).toIdeal q
    rw [_root_.CommHopfAlgCat.comp_apply,
      liftQuotient_mk (hf := bot_le_ker_id H), mkQuotient_apply]
    rfl
  inv_hom_id := mkQuotient_comp_liftQuotient
    (⊥ : HopfIdeal R H) (𝟙 H) (bot_le_ker_id H)

/-- The forward map of the quotient-by-zero isomorphism is the lift of the identity. -/
@[simp]
lemma quotientBotIso_hom (H : _root_.CommHopfAlgCat.{v} R) :
    (quotientBotIso H).hom =
      liftQuotient (⊥ : HopfIdeal R H) (𝟙 H) (by simp) :=
  by rw [quotientBotIso]

/-- The inverse map of the quotient-by-zero isomorphism is the quotient morphism. -/
@[simp]
lemma quotientBotIso_inv (H : _root_.CommHopfAlgCat.{v} R) :
    (quotientBotIso H).inv = mkQuotient H (⊥ : HopfIdeal R H) :=
  by rw [quotientBotIso]

/-- If `I ≤ J`, then the quotient map by `J` kills every element of `I`. -/
lemma toIdeal_le_ker_mkQuotient_of_le
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    I.toIdeal ≤ RingHom.ker (mkQuotient H J).hom.toAlgHom.toRingHom := by
  rw [mkQuotient_ker]
  exact HopfIdeal.toIdeal_le_toIdeal.mpr hIJ

/-- The coordinate morphism `H ⧸ I ⟶ H ⧸ J` induced by an inclusion `I ≤ J` of Hopf
ideals.

It is the unique morphism out of `H ⧸ I` whose composite with `H ⟶ H ⧸ I` is the quotient
map `H ⟶ H ⧸ J`. -/
noncomputable abbrev quotientMapOfLe (H : _root_.CommHopfAlgCat.{v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) : quotient H I ⟶ quotient H J :=
  liftQuotient I (mkQuotient H J) (toIdeal_le_ker_mkQuotient_of_le H hIJ)

/-- The quotient-to-quotient morphism sends the class of `h` modulo `I` to its class
modulo `J`. -/
lemma quotientMapOfLe_mk (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H}
    (hIJ : I ≤ J) (h : H) :
    (quotientMapOfLe H hIJ).hom (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Ideal.Quotient.mkₐ R J.toIdeal h := by
  rw [quotientMapOfLe, liftQuotient_mk, mkQuotient_apply]

/-- Composing the quotient map `H ⟶ H ⧸ I` with the quotient-to-quotient morphism for
`I ≤ J` gives the quotient map `H ⟶ H ⧸ J`. -/
lemma mkQuotient_comp_quotientMapOfLe (H : _root_.CommHopfAlgCat.{v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    mkQuotient H I ≫ quotientMapOfLe H hIJ = mkQuotient H J :=
  mkQuotient_comp_liftQuotient I (mkQuotient H J)
    (toIdeal_le_ker_mkQuotient_of_le H hIJ)

/-- The quotient-to-quotient morphism for `I ≤ I` is the identity morphism. -/
@[simp]
lemma quotientMapOfLe_refl (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    quotientMapOfLe H (le_refl I) = 𝟙 (quotient H I) := by
  ext q
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q
  rw [quotientMapOfLe_mk]
  rfl

/-- Quotient-to-quotient morphisms compose along inclusions of Hopf ideals. -/
@[simp]
lemma quotientMapOfLe_comp (H : _root_.CommHopfAlgCat.{v} R)
    {I J K : HopfIdeal R H} (hIJ : I ≤ J) (hJK : J ≤ K) :
    quotientMapOfLe H hIJ ≫ quotientMapOfLe H hJK =
      quotientMapOfLe H (hIJ.trans hJK) := by
  ext q
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q
  rw [_root_.CommHopfAlgCat.comp_apply, quotientMapOfLe_mk, quotientMapOfLe_mk,
    quotientMapOfLe_mk]

end CommHopfAlgCat

namespace FiniteTypeCommHopfAlgCat

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- The quotient of a finite-type commutative Hopf algebra by a Hopf ideal, as a bundled
finite-type commutative Hopf algebra. -/
noncomputable abbrev quotient (H : FiniteTypeCommHopfAlgCat.{u, v} R) (I : HopfIdeal R H) :
    FiniteTypeCommHopfAlgCat.{u, v} R :=
  ⟨CommHopfAlgCat.quotient H.obj I, inferInstanceAs (Algebra.FiniteType R (H ⧸ I.toIdeal))⟩

/-- Quotienting a finite-type commutative Hopf algebra by the zero Hopf ideal gives an
isomorphic finite-type commutative Hopf algebra. -/
noncomputable def quotientBotIso (H : FiniteTypeCommHopfAlgCat.{u, v} R) :
    quotient H (⊥ : HopfIdeal R H) ≅ H :=
  ObjectProperty.isoMk _ (CommHopfAlgCat.quotientBotIso H.obj)

/-- The quotient morphism `H ⟶ H ⧸ I` in `FiniteTypeCommHopfAlgCat`. -/
noncomputable abbrev mkQuotient (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    (I : HopfIdeal R H) : H ⟶ quotient H I :=
  ObjectProperty.homMk (CommHopfAlgCat.mkQuotient H.obj I)

/-- The inverse map of the finite-type quotient-by-zero isomorphism is the quotient morphism. -/
@[simp]
lemma quotientBotIso_inv (H : FiniteTypeCommHopfAlgCat.{u, v} R) :
    (quotientBotIso H).inv = mkQuotient H (⊥ : HopfIdeal R H) :=
  by
    rw [quotientBotIso]
    apply ObjectProperty.hom_ext
    exact CommHopfAlgCat.quotientBotIso_inv H.obj

/-- The finite-type quotient morphism forgets to the `CommHopfAlgCat` quotient morphism. -/
lemma forget₂_commHopfAlgCat_map_mkQuotient (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    (I : HopfIdeal R H) :
    (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R) (_root_.CommHopfAlgCat.{v} R)).map
      (mkQuotient H I) = CommHopfAlgCat.mkQuotient H.obj I :=
  rfl

/-- The kernel of the finite-type quotient morphism is the Hopf ideal being quotiented by. -/
lemma mkQuotient_ker (H : FiniteTypeCommHopfAlgCat.{u, v} R) (I : HopfIdeal R H) :
    RingHom.ker (toBialgHom (mkQuotient H I)).toAlgHom.toRingHom = I.toIdeal :=
  CommHopfAlgCat.mkQuotient_ker H.obj I

/-- An element maps to zero in the finite-type quotient exactly when it belongs to the Hopf
ideal. -/
lemma mkQuotient_eq_zero_iff (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    (I : HopfIdeal R H) (h : H) : toBialgHom (mkQuotient H I) h = 0 ↔ h ∈ I.toIdeal :=
  CommHopfAlgCat.mkQuotient_eq_zero_iff H.obj I h

variable {H K : FiniteTypeCommHopfAlgCat.{u, v} R}

/-- A morphism of finite-type commutative Hopf algebras out of `H` which kills a Hopf ideal
factors through the quotient object. -/
noncomputable abbrev liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) : quotient H I ⟶ K :=
  ObjectProperty.homMk (CommHopfAlgCat.liftQuotient I f.hom hf)

/-- The forward map of the finite-type quotient-by-zero isomorphism is the lift of the identity. -/
@[simp]
lemma quotientBotIso_hom (H : FiniteTypeCommHopfAlgCat.{u, v} R) :
    (quotientBotIso H).hom =
      liftQuotient (⊥ : HopfIdeal R H) (𝟙 H) (by simp) :=
  by
    rw [quotientBotIso]
    apply ObjectProperty.hom_ext
    exact CommHopfAlgCat.quotientBotIso_hom H.obj

/-- The finite-type quotient lift forgets to the `CommHopfAlgCat` quotient lift. -/
lemma forget₂_commHopfAlgCat_map_liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) :
    (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R) (_root_.CommHopfAlgCat.{v} R)).map
      (liftQuotient I f hf) = CommHopfAlgCat.liftQuotient I f.hom hf :=
  rfl

/-- The quotient lift composed with the quotient morphism is the original morphism. -/
@[simp]
lemma mkQuotient_comp_liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) :
    mkQuotient H I ≫ liftQuotient I f hf = f := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (_root_.CommHopfAlgCat.{v} R)).map_injective
  exact CommHopfAlgCat.mkQuotient_comp_liftQuotient I f.hom hf

/-- A morphism out of the quotient object is determined by its precomposition with the
quotient morphism. -/
lemma liftQuotient_unique (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) (g : quotient H I ⟶ K)
    (hg : mkQuotient H I ≫ g = f) : g = liftQuotient I f hf := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (_root_.CommHopfAlgCat.{v} R)).map_injective
  have hg' : _root_.CommHopfAlgCat.ofHom (Bialgebra.Quotient.mkBialgHom I.toIdeal) ≫ g.hom =
      f.hom :=
    congrArg
      (fun φ => (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
        (_root_.CommHopfAlgCat.{v} R)).map φ) hg
  exact CommHopfAlgCat.liftQuotient_unique (H := _root_.CommHopfAlgCat.of R H) I f.hom hf
    g.hom hg'

/-- The finite-type coordinate morphism `H ⧸ I ⟶ H ⧸ J` induced by an inclusion `I ≤ J` of
Hopf ideals. -/
noncomputable abbrev quotientMapOfLe (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) : quotient H I ⟶ quotient H J :=
  ObjectProperty.homMk (CommHopfAlgCat.quotientMapOfLe H.obj hIJ)

/-- The finite-type quotient-to-quotient morphism forgets to the `CommHopfAlgCat`
quotient-to-quotient morphism. -/
lemma forget₂_commHopfAlgCat_map_quotientMapOfLe
    (H : FiniteTypeCommHopfAlgCat.{u, v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R) (_root_.CommHopfAlgCat.{v} R)).map
        (quotientMapOfLe H hIJ) =
      CommHopfAlgCat.quotientMapOfLe H.obj hIJ :=
  rfl

/-- The finite-type quotient-to-quotient morphism sends the class of `h` modulo `I` to its
class modulo `J`. -/
lemma quotientMapOfLe_mk (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) (h : H) :
    (toBialgHom (quotientMapOfLe H hIJ)) (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Ideal.Quotient.mkₐ R J.toIdeal h :=
  CommHopfAlgCat.quotientMapOfLe_mk H.obj hIJ h

/-- Composing the finite-type quotient map `H ⟶ H ⧸ I` with the quotient-to-quotient
morphism for `I ≤ J` gives the quotient map `H ⟶ H ⧸ J`. -/
@[simp]
lemma mkQuotient_comp_quotientMapOfLe (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    mkQuotient H I ≫ quotientMapOfLe H hIJ = mkQuotient H J := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (_root_.CommHopfAlgCat.{v} R)).map_injective
  exact CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe H.obj hIJ

/-- The finite-type quotient-to-quotient morphism for `I ≤ I` is the identity morphism. -/
@[simp]
lemma quotientMapOfLe_refl (H : FiniteTypeCommHopfAlgCat.{u, v} R) (I : HopfIdeal R H) :
    quotientMapOfLe H (le_refl I) = 𝟙 (quotient H I) := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (_root_.CommHopfAlgCat.{v} R)).map_injective
  exact CommHopfAlgCat.quotientMapOfLe_refl H.obj I

/-- Finite-type quotient-to-quotient morphisms compose along inclusions of Hopf ideals. -/
@[simp]
lemma quotientMapOfLe_comp (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    {I J K : HopfIdeal R H} (hIJ : I ≤ J) (hJK : J ≤ K) :
    quotientMapOfLe H hIJ ≫ quotientMapOfLe H hJK =
      quotientMapOfLe H (hIJ.trans hJK) := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (_root_.CommHopfAlgCat.{v} R)).map_injective
  exact CommHopfAlgCat.quotientMapOfLe_comp H.obj hIJ hJK

end FiniteTypeCommHopfAlgCat

end TauCeti
