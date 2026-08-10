/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# Points valued in an equalizer, and fixed points of an endomorphism of the value algebra

Let `H` be a Hopf algebra over `R`, so that `A ↦ WithConv (H →ₐ[R] A)` is the functor of points
of the affine group scheme represented by `H`, with post-composition
`TauCeti.AlgHom.mapValue` as its action on morphisms of value algebras.

Two `R`-algebra homomorphisms `φ ψ : A →ₐ[R] B` induce two group homomorphisms
`mapValue φ, mapValue ψ` on points. This file proves that the equalizer of those two group
homomorphisms is the group of points valued in the equalizer subalgebra `AlgHom.equalizer φ ψ`:
a point `f : H →ₐ[R] A` satisfies `φ ∘ f = ψ ∘ f` exactly when all of its values lie in the
subalgebra where `φ` and `ψ` agree, and the resulting bijection is an isomorphism of groups.
In other words, the functor of points carries an equalizer of value algebras to an equalizer of
groups.

The case `ψ = AlgHom.id R A` is the one a construction of a finite group of Lie type asks for.
There `φ` is a Steinberg endomorphism of the value algebra — for the untwisted families the
`q`-power Frobenius of an algebraically closed field `k` of characteristic `p` — the equalizer
subalgebra is the subfield `𝔽_q` fixed by it, and the theorem below says that the fixed subgroup
`(mapValue φ).eqLocus (MonoidHom.id _)` of the induced endomorphism of `G(k)` is `G(𝔽_q)`. Nothing
here assumes that the value algebra is a field, that it is algebraically closed, or that `φ` is a
Frobenius: the statement is about an arbitrary pair of homomorphisms of the value algebra.

## Main definitions and results

* `TauCeti.AlgHom.mapValue_injective`: post-composition with an injective algebra homomorphism is
  injective on points.
* `TauCeti.AlgHom.mem_eqLocus_mapValue_iff`: a point lies in the equalizer of the two induced
  group homomorphisms exactly when all of its values lie in the equalizer subalgebra.
* `TauCeti.AlgHom.range_mapValue_val`: the points that factor through the equalizer subalgebra are
  exactly that equalizer of group homomorphisms.
* `TauCeti.AlgHom.equalizerPointsEquiv`: the group isomorphism between the points valued in the
  equalizer subalgebra and that equalizer of group homomorphisms.
* `TauCeti.AlgHom.liftEqualizerPoints`: the universal property of the equalizer, for group
  homomorphisms into the points equalized by `mapValue φ` and `mapValue ψ`.
* `TauCeti.AlgHom.mem_eqLocus_mapValue_id_iff` and `TauCeti.AlgHom.fixedPointsEquiv`: the two
  results above in the fixed-point form `ψ = AlgHom.id R A`.
* `TauCeti.AlgHom.map_eqLocus_mapValue_id_le`: an algebra homomorphism of value algebras
  intertwining two endomorphisms carries fixed points to fixed points.

## References

This completes the ReductiveGroups roadmap Layer 9 item "points over an algebraically closed field
as a group, functorially in the field, so that a field endomorphism induces a group endomorphism of
the points" by identifying the fixed subgroup of such an induced endomorphism. Its consumer is
milestone L3 of `TauCetiRoadmap/CFSGStatement/README.md`, which sets
`H_d = fixedSubgroup d.steinberg` for `fixedSubgroup F = F.eqLocus (MonoidHom.id _)`, with
`d.steinberg` the `q`-power Frobenius of L1 on the untwisted branches.
-/

public section

open WithConv

namespace TauCeti

namespace AlgHom

universe u v w

variable {R : Type u} {H : Type v} {A B C : Type w} [CommSemiring R]

section Bialgebra

variable [Semiring H] [_root_.Bialgebra R H] [CommSemiring A] [Algebra R A] [CommSemiring B]
  [Algebra R B]

/-- Post-composition with an injective homomorphism of value algebras is injective on points.
A point is determined by its values, and `mapValue φ` changes those values by `φ`. -/
theorem mapValue_injective {φ : A →ₐ[R] B} (hφ : Function.Injective φ) :
    Function.Injective (mapValue (H := H) φ) := by
  intro f g hfg
  refine WithConv.ext (_root_.AlgHom.ext fun h => hφ ?_)
  have hval := congrArg (fun x : WithConv (H →ₐ[R] B) => x.ofConv h) hfg
  simpa using hval

/-- A point factors through a subalgebra `S` of the value algebra exactly when all of its values
lie in `S`. This is the underlying map of `TauCeti.AlgHom.range_mapValue_val`, stated before the
group structure is available. -/
theorem exists_mapValue_val_eq_iff (S : Subalgebra R A) (f : WithConv (H →ₐ[R] A)) :
    (∃ g : WithConv (H →ₐ[R] S), mapValue (H := H) S.val g = f) ↔ ∀ h : H, f.ofConv h ∈ S := by
  constructor
  · rintro ⟨g, rfl⟩ h
    exact (g.ofConv h).2
  · intro hf
    exact ⟨toConv (f.ofConv.codRestrict S hf), WithConv.ext (_root_.AlgHom.ext fun _ => rfl)⟩

end Bialgebra

section Hopf

variable [Semiring H] [_root_.HopfAlgebra R H] [CommSemiring A] [Algebra R A] [CommSemiring B]
  [Algebra R B]

/-! ### The points valued in an equalizer subalgebra -/

/-- A point of `H` valued in `A` is equalized by the two group homomorphisms induced by
`φ ψ : A →ₐ[R] B` exactly when every one of its values lies in the equalizer subalgebra of `φ`
and `ψ`. -/
theorem mem_eqLocus_mapValue_iff (φ ψ : A →ₐ[R] B) (f : WithConv (H →ₐ[R] A)) :
    f ∈ MonoidHom.eqLocus (mapValue (H := H) φ) (mapValue (H := H) ψ) ↔
      ∀ h : H, f.ofConv h ∈ _root_.AlgHom.equalizer φ ψ := by
  change mapValue (H := H) φ f = mapValue (H := H) ψ f ↔ _
  rw [mapValue_apply, mapValue_apply, WithConv.toConv_injective.eq_iff, _root_.AlgHom.ext_iff]
  simp [_root_.AlgHom.mem_equalizer]

/-- The points that factor through the equalizer subalgebra of `φ` and `ψ` are exactly the points
equalized by the two induced group homomorphisms. This is the subgroup form of the equalizer
statement; `TauCeti.AlgHom.equalizerPointsEquiv` upgrades it to an isomorphism. -/
theorem range_mapValue_val (φ ψ : A →ₐ[R] B) :
    MonoidHom.range (mapValue (H := H) (_root_.AlgHom.equalizer φ ψ).val) =
      MonoidHom.eqLocus (mapValue (H := H) φ) (mapValue (H := H) ψ) := by
  ext f
  rw [MonoidHom.mem_range, mem_eqLocus_mapValue_iff]
  exact exists_mapValue_val_eq_iff (H := H) _ f

/-- The inclusion of the equalizer subalgebra is injective, so it is injective on points. -/
private theorem val_injective (φ ψ : A →ₐ[R] B) :
    Function.Injective ⇑(_root_.AlgHom.equalizer φ ψ).val :=
  fun _ _ h => Subtype.ext h

/-- Post-composition with the inclusion of the equalizer subalgebra, as a group homomorphism onto
the equalizer of the two induced group homomorphisms. It is exposed because its action on a point
is post-composition, which the computation lemmas below read off. -/
@[expose] noncomputable def equalizerPointsHom (φ ψ : A →ₐ[R] B) :
    WithConv (H →ₐ[R] _root_.AlgHom.equalizer φ ψ) →*
      MonoidHom.eqLocus (mapValue (H := H) φ) (mapValue (H := H) ψ) :=
  MonoidHom.codRestrict (mapValue (H := H) (_root_.AlgHom.equalizer φ ψ).val) _ fun g =>
    (mem_eqLocus_mapValue_iff φ ψ _).2 fun h => (g.ofConv h).2

@[simp]
theorem coe_equalizerPointsHom (φ ψ : A →ₐ[R] B)
    (g : WithConv (H →ₐ[R] _root_.AlgHom.equalizer φ ψ)) :
    (equalizerPointsHom (H := H) φ ψ g : WithConv (H →ₐ[R] A)) =
      mapValue (H := H) (_root_.AlgHom.equalizer φ ψ).val g :=
  rfl

theorem equalizerPointsHom_bijective (φ ψ : A →ₐ[R] B) :
    Function.Bijective (equalizerPointsHom (H := H) φ ψ) := by
  constructor
  · intro g g' hgg'
    exact mapValue_injective (H := H) (val_injective φ ψ) (congrArg Subtype.val hgg')
  · rintro ⟨f, hf⟩
    obtain ⟨g, hg⟩ :=
      (exists_mapValue_val_eq_iff (H := H) _ f).2 ((mem_eqLocus_mapValue_iff φ ψ f).1 hf)
    exact ⟨g, Subtype.ext hg⟩

/-- **The functor of points carries an equalizer of value algebras to an equalizer of groups.**
The group of points valued in the equalizer subalgebra of `φ ψ : A →ₐ[R] B` is the equalizer of
the two group homomorphisms `φ` and `ψ` induce on points. It is exposed for the same reason as
`TauCeti.AlgHom.equalizerPointsHom`, whose bijection it packages. -/
@[expose] noncomputable def equalizerPointsEquiv (φ ψ : A →ₐ[R] B) :
    WithConv (H →ₐ[R] _root_.AlgHom.equalizer φ ψ) ≃*
      MonoidHom.eqLocus (mapValue (H := H) φ) (mapValue (H := H) ψ) :=
  MulEquiv.ofBijective (equalizerPointsHom φ ψ) (equalizerPointsHom_bijective φ ψ)

@[simp]
theorem coe_equalizerPointsEquiv_apply (φ ψ : A →ₐ[R] B)
    (g : WithConv (H →ₐ[R] _root_.AlgHom.equalizer φ ψ)) :
    (equalizerPointsEquiv (H := H) φ ψ g : WithConv (H →ₐ[R] A)) =
      mapValue (H := H) (_root_.AlgHom.equalizer φ ψ).val g :=
  rfl

/-- The isomorphism does not move the values of a point: the value at `h` of the point over the
equalizer subalgebra is the value at `h` of its image in `A`. -/
@[simp]
theorem coe_equalizerPointsEquiv_symm_apply_apply (φ ψ : A →ₐ[R] B)
    (f : MonoidHom.eqLocus (mapValue (H := H) φ) (mapValue (H := H) ψ)) (h : H) :
    (((equalizerPointsEquiv (H := H) φ ψ).symm f).ofConv h : A) = (f : WithConv (H →ₐ[R] A)) h := by
  have hf := (equalizerPointsEquiv (H := H) φ ψ).apply_symm_apply f
  exact congrArg (fun x : WithConv (H →ₐ[R] A) => x.ofConv h) (congrArg Subtype.val hf)

/-! ### The universal property -/

variable {G : Type*} [Group G]

/-- The universal property of the equalizer, on points: a group homomorphism into the `A`-points
whose composites with `mapValue φ` and `mapValue ψ` agree factors through the points valued in the
equalizer subalgebra. It is exposed so that the factorization below reduces on a point. -/
@[expose] noncomputable def liftEqualizerPoints (φ ψ : A →ₐ[R] B) (u : G →* WithConv (H →ₐ[R] A))
    (hu : (mapValue (H := H) φ).comp u = (mapValue (H := H) ψ).comp u) :
    G →* WithConv (H →ₐ[R] _root_.AlgHom.equalizer φ ψ) :=
  (equalizerPointsEquiv (H := H) φ ψ).symm.toMonoidHom.comp
    (u.codRestrict _ fun g => DFunLike.congr_fun hu g)

/-- The lift really is a factorization: composing it with post-composition by the inclusion of the
equalizer subalgebra returns the original homomorphism. -/
@[simp]
theorem mapValue_val_comp_liftEqualizerPoints (φ ψ : A →ₐ[R] B) (u : G →* WithConv (H →ₐ[R] A))
    (hu : (mapValue (H := H) φ).comp u = (mapValue (H := H) ψ).comp u) :
    (mapValue (H := H) (_root_.AlgHom.equalizer φ ψ).val).comp
        (liftEqualizerPoints (H := H) φ ψ u hu) = u := by
  refine MonoidHom.ext fun g => WithConv.ext (_root_.AlgHom.ext fun h => ?_)
  exact coe_equalizerPointsEquiv_symm_apply_apply φ ψ ⟨u g, DFunLike.congr_fun hu g⟩ h

/-- The factorization is unique: two lifts along the inclusion of the equalizer subalgebra
agree. -/
theorem liftEqualizerPoints_unique (φ ψ : A →ₐ[R] B)
    (u v : G →* WithConv (H →ₐ[R] _root_.AlgHom.equalizer φ ψ))
    (huv : (mapValue (H := H) (_root_.AlgHom.equalizer φ ψ).val).comp u =
      (mapValue (H := H) (_root_.AlgHom.equalizer φ ψ).val).comp v) : u = v :=
  MonoidHom.ext fun g =>
    mapValue_injective (H := H) (val_injective φ ψ) (DFunLike.congr_fun huv g)

/-! ### Fixed points of an endomorphism of the value algebra -/

/-- A point is fixed by the endomorphism of points induced by `φ : A →ₐ[R] A` exactly when `φ`
fixes every value of the point. -/
theorem mem_eqLocus_mapValue_id_iff (φ : A →ₐ[R] A) (f : WithConv (H →ₐ[R] A)) :
    f ∈ MonoidHom.eqLocus (mapValue (H := H) φ) (MonoidHom.id _) ↔
      ∀ h : H, φ (f.ofConv h) = f.ofConv h := by
  rw [← mapValue_id (H := H) (A := A), mem_eqLocus_mapValue_iff]
  simp [_root_.AlgHom.mem_equalizer]

/-- **The fixed points of a Steinberg-type endomorphism.** The subgroup of points fixed by the
endomorphism that `φ : A →ₐ[R] A` induces on points is the group of points valued in the
subalgebra of `A` fixed by `φ`. For `A` an algebraic closure of `𝔽_p` and `φ` the `q`-power
Frobenius this reads `G(k)^{Frob_q} ≃* G(𝔽_q)`. It is exposed for the same reason as
`TauCeti.AlgHom.equalizerPointsEquiv`, of which it is the case `ψ = AlgHom.id R A`. -/
@[expose] noncomputable def fixedPointsEquiv (φ : A →ₐ[R] A) :
    WithConv (H →ₐ[R] _root_.AlgHom.equalizer φ (_root_.AlgHom.id R A)) ≃*
      MonoidHom.eqLocus (mapValue (H := H) φ) (MonoidHom.id _) :=
  (equalizerPointsEquiv (H := H) φ (_root_.AlgHom.id R A)).trans
    (MulEquiv.subgroupCongr (by rw [mapValue_id]))

@[simp]
theorem coe_fixedPointsEquiv_apply (φ : A →ₐ[R] A)
    (g : WithConv (H →ₐ[R] _root_.AlgHom.equalizer φ (_root_.AlgHom.id R A))) :
    (fixedPointsEquiv (H := H) φ g : WithConv (H →ₐ[R] A)) =
      mapValue (H := H) (_root_.AlgHom.equalizer φ (_root_.AlgHom.id R A)).val g :=
  rfl

/-- The identity endomorphism of the value algebra fixes every point. This is not `@[simp]`:
`mapValue_id` already rewrites the left-hand side, after which `MonoidHom.eqLocus_same` closes
the goal, so the statement below is never in simp-normal form. -/
theorem eqLocus_mapValue_id_id :
    MonoidHom.eqLocus (mapValue (H := H) (_root_.AlgHom.id R A)) (MonoidHom.id _) = ⊤ := by
  rw [mapValue_id]
  exact MonoidHom.eqLocus_same _

/-- A point fixed by two endomorphisms of the value algebra is fixed by their composite. -/
theorem inf_eqLocus_mapValue_id_le_comp (φ ψ : A →ₐ[R] A) :
    MonoidHom.eqLocus (mapValue (H := H) φ) (MonoidHom.id _) ⊓
        MonoidHom.eqLocus (mapValue (H := H) ψ) (MonoidHom.id _) ≤
      MonoidHom.eqLocus (mapValue (H := H) (φ.comp ψ)) (MonoidHom.id _) := by
  rintro f ⟨hφ, hψ⟩
  rw [SetLike.mem_coe, Subgroup.mem_toSubmonoid, mem_eqLocus_mapValue_id_iff] at hφ hψ
  rw [mem_eqLocus_mapValue_id_iff]
  intro h
  rw [_root_.AlgHom.comp_apply, hψ h, hφ h]

/-- A point fixed by an endomorphism of the value algebra is fixed by its square. This is the form
in which a Suzuki--Ree Steinberg map, whose square is a Frobenius, meets the fixed subgroup of that
Frobenius. -/
theorem eqLocus_mapValue_id_le_comp_self (φ : A →ₐ[R] A) :
    MonoidHom.eqLocus (mapValue (H := H) φ) (MonoidHom.id _) ≤
      MonoidHom.eqLocus (mapValue (H := H) (φ.comp φ)) (MonoidHom.id _) :=
  le_trans (le_inf le_rfl le_rfl) (inf_eqLocus_mapValue_id_le_comp φ φ)

/-- A homomorphism of value algebras intertwining two endomorphisms carries fixed points to fixed
points. This is the compatibility a base change of the ambient group needs: it says that the fixed
subgroup construction is functorial in the pair `(A, φ)`. -/
theorem map_eqLocus_mapValue_id_le (θ : A →ₐ[R] B) (φ : A →ₐ[R] A) (ψ : B →ₐ[R] B)
    (hθ : ψ.comp θ = θ.comp φ) :
    (MonoidHom.eqLocus (mapValue (H := H) φ) (MonoidHom.id _)).map (mapValue (H := H) θ) ≤
      MonoidHom.eqLocus (mapValue (H := H) ψ) (MonoidHom.id _) := by
  rintro _ ⟨f, hf, rfl⟩
  rw [SetLike.mem_coe, mem_eqLocus_mapValue_id_iff] at hf
  rw [mem_eqLocus_mapValue_id_iff]
  intro h
  have hval := congrArg (fun x : A →ₐ[R] B => x (f.ofConv h)) hθ
  simp only [_root_.AlgHom.comp_apply] at hval
  simpa [hf h] using hval

end Hopf

end AlgHom

end TauCeti
