/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Functoriality of class groups under ring equivalences

Mathlib defines `ClassGroup.mulEquiv f`, the multiplicative equivalence on ideal class groups
induced by a ring equivalence `f : R ≃+* S`. This file supplies its basic functorial API: the
induced map respects identity, composition, and inverses, and computes on the class of a unit
fractional ideal.

This is a prerequisite for the genus-field layer of the multiquadratic roadmap. For a quadratic
field, conjugation is a ring automorphism of its ring of integers; the roadmap's proof that
conjugation acts on the class group by inversion first needs to treat that action functorially and
compute it on ideal classes.

## Main results

* `ClassGroup.mulEquiv_mk_fractionRing`: the `simp`-usable computation of the induced equivalence on
  the class of a unit fractional ideal over the canonical fraction field.
* `ClassGroup.mulEquiv_mk`: the same computation over arbitrary fraction fields, as an `rw`-form
  with the target fraction field explicit.
* `ClassGroup.mulEquiv_refl`: the identity ring equivalence induces the identity on class groups.
* `ClassGroup.mulEquiv_trans`: induced equivalences respect composition.
* `ClassGroup.mulEquiv_symm`: the inverse induced equivalence comes from the inverse ring
  equivalence.
* `ClassGroup.mulEquivHom`: the induced action bundled as a monoid homomorphism
  `(R ≃+* R) →* MulAut (ClassGroup R)`.
* `ClassGroup.mulEquiv_involutive`: an involutive ring equivalence acts involutively on the class
  group.
* `ClassGroup.mulEquiv_mk0`: the induced class-group equivalence sends the class `ClassGroup.mk0 I`
  of a nonzero ideal to the class of its pushforward ideal `Ideal.map f I`.
* `ClassGroup.mulEquiv_apply_eq_inv_of_forall_isPrincipal`: if `I · (Ideal.map f I)` is principal
  for every nonzero ideal, the induced class-group map is inversion `C ↦ C⁻¹`.
-/

public section

open scoped nonZeroDivisors

namespace ClassGroup

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [IsDomain R] [IsDomain S] [IsDomain T]

/-- `ClassGroup.mulEquiv f` sends the class of a unit fractional ideal `I` to the class of its
image under `FractionalIdeal.ringEquivOfRingEquiv f`. This is the characteristic computation of the
induced map on ideal classes; the functorial laws below are corollaries. Its fully-determined
left-hand side makes it the `simp`-usable form; `mulEquiv_mk` is the general `rw`-form over
arbitrary fraction fields. -/
@[simp high] theorem mulEquiv_mk_fractionRing (f : R ≃+* S)
    (I : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    ClassGroup.mulEquiv f (ClassGroup.mk (FractionRing R) I) =
      ClassGroup.mk (FractionRing S)
        (Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv
          (FractionRing R) (FractionRing S) f) I) := by
  apply (ClassGroup.equiv (FractionRing S)).injective
  erw [ClassGroup.mulEquiv_apply]
  rw [MulEquiv.apply_symm_apply, ClassGroup.equiv_mk, ClassGroup.equiv_mk]
  erw [QuotientGroup.congr_mk']
  apply congrArg (QuotientGroup.mk' (toPrincipalIdeal S (FractionRing S)).range)
  apply Units.ext
  simp [FractionalIdeal.canonicalEquiv_self]

/-- The canonical equivalence between the fractional ideals of two fraction fields of `R` is
transport along the identity ring equivalence. This lets a change of fraction field and a transport
along a ring equivalence be composed by `FractionalIdeal.ringEquivOfRingEquiv_trans_apply`. -/
private theorem canonicalEquiv_eq_ringEquivOfRingEquiv (K K' : Type*) [Field K] [Field K']
    [Algebra R K] [Algebra R K'] [IsFractionRing R K] [IsFractionRing R K'] :
    FractionalIdeal.canonicalEquiv R⁰ K K' =
      FractionalIdeal.ringEquivOfRingEquiv K K' (RingEquiv.refl R) := by
  letI : RingHomInvPair (RingEquiv.refl R : R →+* R) (RingEquiv.refl R).symm :=
    RingHomInvPair.of_ringEquiv (RingEquiv.refl R)
  letI : RingHomInvPair ((RingEquiv.refl R).symm : R →+* R) (RingEquiv.refl R) :=
    RingHomInvPair.of_ringEquiv (RingEquiv.refl R).symm
  ext I x
  rw [FractionalIdeal.mem_canonicalEquiv_apply]
  erw [FractionalIdeal.ringEquivOfRingEquiv_apply]
  -- the right-hand side is the image submodule under the semilinear equivalence, presented by
  -- `erw` through the equivalence's coercion; `change` names it so `Submodule.mem_map` fires.
  change _ ↔ x ∈ Submodule.map
      (IsFractionRing.semilinearEquivOfRingEquiv K K' (RingEquiv.refl R)).toLinearMap I.val
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    erw [IsFractionRing.semilinearEquivOfRingEquiv_apply,
      IsFractionRing.ringEquivOfRingEquiv_apply]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    erw [IsFractionRing.semilinearEquivOfRingEquiv_apply,
      IsFractionRing.ringEquivOfRingEquiv_apply]
    -- what is left is `IsLocalization.map K' (RingHom.id R) _ y = IsLocalization.map K'
    -- ↑(RingEquiv.refl R) _ y`: the coercion of `RingEquiv.refl R` *is* `RingHom.id R`, and the
    -- two remaining field arguments are proofs.
    rfl

/-- `ClassGroup.mulEquiv f` sends the class of a unit fractional ideal `I` to the class of its
image under `FractionalIdeal.ringEquivOfRingEquiv f`. This is independent of the chosen fraction
fields. -/
theorem mulEquiv_mk {K : Type*} (L : Type*) [Field K] [Field L] [Algebra R K]
    [Algebra S L] [IsFractionRing R K] [IsFractionRing S L] (f : R ≃+* S)
    (I : (FractionalIdeal R⁰ K)ˣ) :
    ClassGroup.mulEquiv f (ClassGroup.mk K I) =
      ClassGroup.mk L
        (Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv K L f) I) := by
  rw [← ClassGroup.mk_canonicalEquiv (K := K) (FractionRing R) I,
    mulEquiv_mk_fractionRing]
  rw [← ClassGroup.mk_canonicalEquiv (K := FractionRing S) L]
  congr 1
  apply Units.ext
  -- Both sides are two-step transports of `I` along ring equivalences: the left changes fraction
  -- field over `R` and then applies `f`, the right applies `f` and then changes fraction field
  -- over `S`. Rewriting the change-of-fraction-field steps as transports along `RingEquiv.refl`
  -- collapses both composites to the single transport along `f`.
  have key (J : FractionalIdeal R⁰ K) :
      FractionalIdeal.ringEquivOfRingEquiv (FractionRing S) L (RingEquiv.refl S)
          (FractionalIdeal.ringEquivOfRingEquiv (FractionRing R) (FractionRing S) f
            (FractionalIdeal.ringEquivOfRingEquiv K (FractionRing R) (RingEquiv.refl R) J)) =
        FractionalIdeal.ringEquivOfRingEquiv K L f J := by
    have hf : ((RingEquiv.refl R).trans f).trans (RingEquiv.refl S) = f := by ext; rfl
    rw [← FractionalIdeal.ringEquivOfRingEquiv_trans_apply K (FractionRing R) (FractionRing S),
      ← FractionalIdeal.ringEquivOfRingEquiv_trans_apply K (FractionRing S) L, hf]
  simpa only [Units.coe_mapEquiv, Units.coe_map, canonicalEquiv_eq_ringEquivOfRingEquiv,
    MonoidHom.coe_coe, RingEquiv.coe_toMulEquiv] using key I

/-- The identity ring equivalence induces the identity class-group equivalence. -/
@[simp] theorem mulEquiv_refl :
    ClassGroup.mulEquiv (RingEquiv.refl R) = MulEquiv.refl (ClassGroup R) := by
  apply MulEquiv.ext
  intro x
  refine ClassGroup.induction (FractionRing R) (fun I => ?_) x
  rw [MulEquiv.refl_apply, mulEquiv_mk (K := FractionRing R) (L := FractionRing R),
    FractionalIdeal.ringEquivOfRingEquiv_refl]
  apply congrArg (ClassGroup.mk (FractionRing R))
  apply Units.ext
  simp

/-- Composition of ring equivalences is carried to composition of the induced class-group
equivalences. -/
@[simp] theorem mulEquiv_trans (f : R ≃+* S) (g : S ≃+* T) :
    ClassGroup.mulEquiv (f.trans g) =
      (ClassGroup.mulEquiv f).trans (ClassGroup.mulEquiv g) := by
  apply MulEquiv.ext
  intro x
  refine ClassGroup.induction (FractionRing R) (fun I => ?_) x
  rw [MulEquiv.trans_apply,
    mulEquiv_mk (K := FractionRing R) (L := FractionRing T),
    mulEquiv_mk (K := FractionRing R) (L := FractionRing S),
    mulEquiv_mk (K := FractionRing S) (L := FractionRing T)]
  apply congrArg (ClassGroup.mk (FractionRing T))
  apply Units.ext
  simpa using FractionalIdeal.ringEquivOfRingEquiv_trans_apply
    (FractionRing R) (FractionRing S) (FractionRing T) f g I

/-- Pointwise form of `ClassGroup.mulEquiv_trans`. This is not a simp lemma because
`ClassGroup.mulEquiv_apply` already rewrites its left-hand side. -/
theorem mulEquiv_trans_apply (f : R ≃+* S) (g : S ≃+* T) (x : ClassGroup R) :
    ClassGroup.mulEquiv (f.trans g) x = ClassGroup.mulEquiv g (ClassGroup.mulEquiv f x) :=
  DFunLike.congr_fun (mulEquiv_trans f g) x

/-- Pointwise form of `ClassGroup.mulEquiv_refl`. This is not a simp lemma because
`ClassGroup.mulEquiv_refl` already proves the bundled normal form. -/
theorem mulEquiv_refl_apply (x : ClassGroup R) :
    ClassGroup.mulEquiv (RingEquiv.refl R) x = x :=
  DFunLike.congr_fun mulEquiv_refl x

/-- The inverse of the class-group equivalence induced by `f` is induced by `f.symm`. -/
@[simp] theorem mulEquiv_symm (f : R ≃+* S) :
    (ClassGroup.mulEquiv f).symm = ClassGroup.mulEquiv f.symm := by
  apply MulEquiv.ext
  intro x
  apply (ClassGroup.mulEquiv f).injective
  rw [MulEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun (mulEquiv_trans f.symm f) x
  rw [f.symm_trans_self, mulEquiv_refl] at h
  exact h

/-- Pointwise form of `ClassGroup.mulEquiv_symm`. This is not a simp lemma because
`ClassGroup.mulEquiv_apply` already rewrites its left-hand side. -/
theorem mulEquiv_symm_apply' (f : R ≃+* S) (x : ClassGroup S) :
    (ClassGroup.mulEquiv f).symm x = ClassGroup.mulEquiv f.symm x :=
  DFunLike.congr_fun (mulEquiv_symm f) x

/-- The action of ring automorphisms of `R` on `ClassGroup R`, bundled as a monoid homomorphism
`(R ≃+* R) →* MulAut (ClassGroup R)`. This is the object the roadmap's Galois action on ideal
classes transports along; it is the class-group analogue of
`IsFractionRing.ringEquivOfRingEquivHom`. -/
noncomputable def mulEquivHom : (R ≃+* R) →* MulAut (ClassGroup R) where
  toFun := ClassGroup.mulEquiv
  map_one' := mulEquiv_refl
  map_mul' f g := mulEquiv_trans g f

/-- `ClassGroup.mulEquivHom` acts as `ClassGroup.mulEquiv` on each ring automorphism. -/
@[simp] theorem mulEquivHom_apply (f : R ≃+* R) :
    mulEquivHom f = ClassGroup.mulEquiv f := by
  simp [mulEquivHom]

/-- An involutive ring equivalence induces an involution on the class group. This is the form
used for quadratic conjugation; it is the pointwise specialization of `ClassGroup.mulEquivHom`
at an order-two automorphism. -/
theorem mulEquiv_involutive {f : R ≃+* R} (hf : Function.Involutive f) :
    Function.Involutive (ClassGroup.mulEquiv f) := by
  have hff : f * f = 1 := RingEquiv.ext hf
  have h : ClassGroup.mulEquiv f * ClassGroup.mulEquiv f = 1 := by
    rw [← mulEquivHom_apply f, ← map_mul, hff, map_one]
  intro x
  have := DFunLike.congr_fun h x
  rwa [MulAut.mul_apply, MulAut.one_apply] at this

end ClassGroup

namespace ClassGroup

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- Transport of a `coeIdeal` along `FractionalIdeal.ringEquivOfRingEquiv f` is the `coeIdeal` of
the pushforward ideal `Ideal.map f`. This is the fraction-field shadow of `Ideal.map` used to
compute the induced class-group map on `ClassGroup.mk0`. -/
private theorem ringEquivOfRingEquiv_coeIdeal [IsDomain R] [IsDomain R'] (K L : Type*) [Field K]
    [Field L] [Algebra R K] [Algebra R' L] [IsFractionRing R K] [IsFractionRing R' L] (f : R ≃+* R')
    (I : Ideal R) :
    FractionalIdeal.ringEquivOfRingEquiv K L f (I : FractionalIdeal R⁰ K) =
      (Ideal.map (f : R →+* R') I : FractionalIdeal R'⁰ L) := by
  -- Pin the `RingHomInvPair` instances to resolve an `f`/`f.symm.symm` defeq diamond, so the `erw`
  -- rewrites below fire without a transparency option.
  letI : RingHomInvPair (f : R →+* R') (f.symm : R' →+* R) := RingHomInvPair.of_ringEquiv f
  letI : RingHomInvPair (f.symm : R' →+* R) (f : R →+* R') := RingHomInvPair.of_ringEquiv f.symm
  apply FractionalIdeal.coeToSubmodule_injective
  dsimp only
  rw [← FractionalIdeal.val_eq_coe, FractionalIdeal.ringEquivOfRingEquiv_apply_val,
    FractionalIdeal.val_eq_coe, FractionalIdeal.coe_coeIdeal, FractionalIdeal.coe_coeIdeal]
  ext x
  simp only [Submodule.mem_map, FractionalIdeal.mem_coeSubmodule]
  constructor
  · rintro ⟨y, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨f r, Ideal.mem_map_of_mem _ hr, by
      erw [IsFractionRing.semilinearEquivOfRingEquiv_algebraMap]⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective (f : R →+* R') f.surjective).mp hs
    exact ⟨algebraMap R K r, ⟨r, hr, rfl⟩, by
      erw [IsFractionRing.semilinearEquivOfRingEquiv_algebraMap]; rfl⟩

/-- **The class-group map induced by a ring isomorphism, on ideal classes.** For a ring isomorphism
`f : R ≃+* R'` of Dedekind domains, `ClassGroup.mulEquiv f` sends the class of a nonzero ideal `I`
to the class of its pushforward `Ideal.map f I`. This is the bridge between the abstract functorial
action `ClassGroup.mulEquiv` and the concrete pushforward of ideals. -/
theorem mulEquiv_mk0 [IsDedekindDomain R] [IsDedekindDomain R'] (f : R ≃+* R')
    (I : (Ideal R)⁰) :
    ClassGroup.mulEquiv f (ClassGroup.mk0 I) =
      ClassGroup.mk0 ⟨Ideal.map (f : R →+* R') (I : Ideal R), mem_nonZeroDivisors_iff_ne_zero.mpr
        (by rw [ne_eq, Ideal.zero_eq_bot,
              Ideal.map_eq_bot_iff_of_injective (f := (f : R →+* R')) f.injective,
              ← Ideal.zero_eq_bot]
            exact mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩ := by
  rw [← ClassGroup.mk_mk0 (FractionRing R) I, ClassGroup.mulEquiv_mk_fractionRing,
    ← ClassGroup.mk_mk0 (FractionRing R')]
  congr 1
  apply Units.ext
  simp only [Units.coe_mapEquiv, FractionalIdeal.coe_mk0, RingEquiv.coe_toMulEquiv]
  exact ringEquivOfRingEquiv_coeIdeal (FractionRing R) (FractionRing R') f I

/-- **Inversion criterion for the class-group action.** If a ring automorphism `f : R ≃+* R` of a
Dedekind domain makes `I · (Ideal.map f I)` principal for every nonzero ideal `I`, then the induced
map on the class group is inversion: `ClassGroup.mulEquiv f C = C⁻¹`. -/
theorem mulEquiv_apply_eq_inv_of_forall_isPrincipal [IsDedekindDomain R] {f : R ≃+* R}
    (hf : ∀ I : (Ideal R)⁰, ((I : Ideal R) * Ideal.map (f : R →+* R) (I : Ideal R)).IsPrincipal)
    (C : ClassGroup R) : ClassGroup.mulEquiv f C = C⁻¹ := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective C
  rw [mulEquiv_mk0, ClassGroup.mk0_eq_mk0_inv_iff]
  obtain ⟨x, hx⟩ := (hf I).principal
  have hIne : (I : Ideal R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hmapne : Ideal.map (f : R →+* R) (I : Ideal R) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot,
      Ideal.map_eq_bot_iff_of_injective (f := (f : R →+* R)) f.injective, ← Ideal.zero_eq_bot]
    exact hIne
  refine ⟨x, ?_, ?_⟩
  · intro hx0
    subst hx0
    rw [Submodule.span_zero_singleton] at hx
    exact mul_ne_zero hIne hmapne (hx.trans Ideal.zero_eq_bot.symm)
  · rw [mul_comm]; exact hx

end ClassGroup
