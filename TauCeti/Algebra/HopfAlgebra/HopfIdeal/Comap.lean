/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Kernel

/-!
# Inverse images of Hopf ideals

This file records inverse images of Hopf ideals. Over a general commutative base, a surjective
bialgebra morphism supplies the tensor exactness needed for the construction. Over a field, the
kernel of the composite with the quotient morphism gives the inverse image along an arbitrary
bialgebra morphism.

For a surjective morphism `f : H →ₐc[R] K` and a Hopf ideal `I` of `K`, the preimage
`f ⁻¹ I` is a Hopf ideal of `H`. The construction is made by applying the existing
kernel-of-a-surjective-Hopf-map theorem to the composite `H → K → K/I`.

The surjectivity hypothesis is intentional: over a general commutative base, the tensor
exactness needed for the coideal condition is not automatic without an exactness hypothesis.

This is a Layer 3 prerequisite for the reductive-groups roadmap target "Hopf ideals ↔ closed
subgroup schemes", including kernels and pullback-style operations on closed subgroup
schemes in the affine Hopf-algebra dictionary.

## Main declarations

* `TauCeti.HopfIdeal.comap`: the inverse image along an arbitrary morphism over a field.
* `TauCeti.HopfIdeal.comapOfSurjective`: the inverse image under a surjective morphism over a
  general base.
* `TauCeti.HopfIdeal.comap_toIdeal` and `TauCeti.HopfIdeal.mem_comap`: characteristic API over a
  field.
* `TauCeti.HopfIdeal.comapOfSurjective_toIdeal` and
  `TauCeti.HopfIdeal.mem_comapOfSurjective`: characteristic API over a general base.
* `TauCeti.HopfIdeal.comapOfSurjective_eq_comap`: comparison of the two constructions over a
  field.
* `TauCeti.HopfIdeal.comapOfSurjective_le_comapOfSurjective_iff`: surjective inverse image reflects
  containment.
* `TauCeti.HopfIdeal.comapOfSurjective_bot`: the kernel of a surjective morphism is the inverse
  image of the zero Hopf ideal.
* `TauCeti.HopfIdeal.comapOfSurjective_sup`: surjective inverse image preserves binary joins.
* `TauCeti.HopfIdeal.comapOfSurjective_iSup` and
  `TauCeti.HopfIdeal.comapOfSurjective_sSup`: surjective inverse image preserves nonempty
  suprema.
* `TauCeti.HopfIdeal.comapOfSurjective_id` and
  `TauCeti.HopfIdeal.comapOfSurjective_comapOfSurjective`: identity and composition laws.
* `TauCeti.HopfIdeal.comapOfSurjective_bialgEquiv_symm_apply`: inverse-image cancellation for a
  bialgebra equivalence.

## References

The constructions are the standard inverse images of Hopf ideals, reduced here to the
quotient-kernel constructions already in `TauCeti.Algebra.HopfAlgebra.Kernel`. Over a general
base the morphism is assumed surjective; over a field it is arbitrary.
-/

public section

namespace TauCeti

universe u v w x

namespace HopfIdeal

variable {R : Type u} [CommRing R]
variable {H : Type v} {K : Type w} {L : Type x}
variable [Ring H] [Ring K] [Ring L]
variable [HopfAlgebra R H] [HopfAlgebra R K] [HopfAlgebra R L]

/-- The inverse image of a Hopf ideal along a surjective bialgebra morphism.

It is defined as the kernel of the composite `H → K → K/I`; its underlying ideal is the
ordinary ideal comap of `I.toIdeal`. -/
noncomputable def comapOfSurjective (I : HopfIdeal R K) (f : H →ₐc[R] K)
    (hf : Function.Surjective f) : HopfIdeal R H :=
  kerOfSurjective ((Bialgebra.Quotient.mkBialgHom I.toIdeal).comp f)
    (by
      rw [BialgHom.coe_comp]
      exact (Ideal.Quotient.mkₐ_surjective R I.toIdeal).comp hf)

/-- The ordinary kernel calculation shared by both inverse-image constructions. -/
private theorem ker_quotient_comp (I : HopfIdeal R K) (f : H →ₐc[R] K) :
    RingHom.ker ((Bialgebra.Quotient.mkBialgHom I.toIdeal).comp f : H →ₐ[R] K ⧸ I.toIdeal) =
      Ideal.comap (f : H →+* K) I.toIdeal := by
  ext h
  simp only [RingHom.mem_ker, Ideal.mem_comap, BialgHom.comp_apply,
    Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.eq_zero_iff_mem,
    BialgHom.coe_toAlgHom, RingHom.coe_coe]

/-- The underlying ideal of `I.comapOfSurjective f hf` is the ordinary ideal-theoretic inverse
image. -/
@[simp]
theorem comapOfSurjective_toIdeal (I : HopfIdeal R K) (f : H →ₐc[R] K)
    (hf : Function.Surjective f) :
    (I.comapOfSurjective f hf).toIdeal = Ideal.comap (f : H →+* K) I.toIdeal := by
  -- Unfold `comapOfSurjective` once, then use the hidden kernel's characteristic API.
  change (kerOfSurjective ((Bialgebra.Quotient.mkBialgHom I.toIdeal).comp f) _).toIdeal = _
  rw [kerOfSurjective_toIdeal, ker_quotient_comp]

/-- Membership in the inverse-image Hopf ideal is membership after applying the morphism. -/
@[simp]
theorem mem_comapOfSurjective {I : HopfIdeal R K} {f : H →ₐc[R] K} {hf : Function.Surjective f}
    {h : H} : h ∈ I.comapOfSurjective f hf ↔ f h ∈ I := by
  rw [← mem_toIdeal, comapOfSurjective_toIdeal, Ideal.mem_comap]
  exact mem_toIdeal

/-- The inverse image is the kernel of the composite with the quotient morphism. -/
theorem comapOfSurjective_eq_kerOfSurjective (I : HopfIdeal R K) (f : H →ₐc[R] K)
    (hf : Function.Surjective f) :
    I.comapOfSurjective f hf =
      kerOfSurjective ((Bialgebra.Quotient.mkBialgHom I.toIdeal).comp f)
        (by
          rw [BialgHom.coe_comp]
          exact (Ideal.Quotient.mkₐ_surjective R I.toIdeal).comp hf) := by
  ext h
  rw [mem_comapOfSurjective, mem_kerOfSurjective, BialgHom.comp_apply,
    Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.eq_zero_iff_mem, mem_toIdeal]

/-- Inverse image of Hopf ideals is monotone. -/
theorem comapOfSurjective_mono (f : H →ₐc[R] K) (hf : Function.Surjective f)
    {I J : HopfIdeal R K} (hIJ : I ≤ J) :
    I.comapOfSurjective f hf ≤ J.comapOfSurjective f hf := by
  intro h hh
  exact mem_comapOfSurjective.mpr (hIJ (mem_comapOfSurjective.mp hh))

/-- For a surjective morphism, inverse image of Hopf ideals reflects containment. -/
theorem le_of_comapOfSurjective_le_comapOfSurjective (f : H →ₐc[R] K)
    (hf : Function.Surjective f) {I J : HopfIdeal R K}
    (hIJ : I.comapOfSurjective f hf ≤ J.comapOfSurjective f hf) : I ≤ J := by
  intro k hk
  obtain ⟨h, rfl⟩ := hf k
  exact mem_comapOfSurjective.mp (hIJ (mem_comapOfSurjective.mpr hk))

/-- For a surjective morphism, containment after inverse image is equivalent to containment
before inverse image. -/
theorem comapOfSurjective_le_comapOfSurjective_iff (f : H →ₐc[R] K)
    (hf : Function.Surjective f) {I J : HopfIdeal R K} :
    I.comapOfSurjective f hf ≤ J.comapOfSurjective f hf ↔ I ≤ J :=
  ⟨le_of_comapOfSurjective_le_comapOfSurjective f hf, comapOfSurjective_mono f hf⟩

/-- For a surjective morphism, inverse image of Hopf ideals reflects equality. -/
@[simp]
theorem comapOfSurjective_eq_comapOfSurjective_iff (f : H →ₐc[R] K)
    (hf : Function.Surjective f) {I J : HopfIdeal R K} :
    I.comapOfSurjective f hf = J.comapOfSurjective f hf ↔ I = J := by
  constructor
  · intro h
    apply le_antisymm
    · rw [← comapOfSurjective_le_comapOfSurjective_iff f hf, h]
    · rw [← comapOfSurjective_le_comapOfSurjective_iff f hf, h]
  · intro h
    rw [h]

/-- The inverse image of the zero Hopf ideal is the kernel Hopf ideal. -/
@[simp]
theorem comapOfSurjective_bot (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (⊥ : HopfIdeal R K).comapOfSurjective f hf = kerOfSurjective f hf := by
  ext h
  rw [mem_comapOfSurjective, mem_kerOfSurjective, mem_bot]

/-- A finitely supported family over `K` lifts along a surjective bialgebra morphism to a
finitely supported family over `H` that agrees with it pointwise and has the same total sum. -/
private theorem exists_finsupp_map_eq {ι : Type*} (f : H →ₐc[R] K)
    (hf : Function.Surjective f) (s : ι →₀ K) :
    ∃ t : ι →₀ H, (∀ i, f (t i) = s i) ∧
      f (t.sum fun _ y => y) = s.sum fun _ y => y := by
  obtain ⟨t, rfl⟩ := Finsupp.mapRange_surjective (⇑f) (map_zero f) hf s
  refine ⟨t, fun i => by rw [Finsupp.mapRange_apply], ?_⟩
  rw [Finsupp.sum_mapRange_index fun _ => rfl, Finsupp.sum, Finsupp.sum, map_sum]

/-- The inverse image of a supremum of Hopf ideals is contained in the supremum of the inverse
images: the nontrivial inclusion of `comapOfSurjective_iSup`. -/
private theorem comapOfSurjective_iSup_le {ι : Type*} [Nonempty ι] (I : ι → HopfIdeal R K)
    (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (⨆ i, I i).comapOfSurjective f hf ≤ ⨆ i, (I i).comapOfSurjective f hf := by
  classical
  intro h hh
  rw [mem_comapOfSurjective, mem_iSup] at hh
  obtain ⟨s, hs, hsum⟩ := hh
  obtain ⟨t, ht, ht_sum⟩ := exists_finsupp_map_eq f hf s
  let i0 : ι := Classical.choice ‹Nonempty ι›
  -- Lift `s` to `t`, then correct the `i0` coordinate so the total sum lands on `h`.
  refine mem_iSup.mpr ⟨t + Finsupp.single i0 (h - t.sum fun _ y => y), fun i => ?_, ?_⟩
  · have hfin : f (t i) ∈ I i := by rw [ht i]; exact hs i
    rw [mem_comapOfSurjective, Finsupp.add_apply, map_add]
    rcases eq_or_ne i i0 with rfl | hi
    · rw [Finsupp.single_eq_same, map_sub, ht_sum, hsum, sub_self, add_zero]
      exact hfin
    · rw [Finsupp.single_eq_of_ne hi, map_zero, add_zero]
      exact hfin
  · rw [Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl),
      Finsupp.sum_single_index rfl]
    abel

/-- Surjective inverse image of Hopf ideals preserves nonempty suprema of families. -/
@[simp]
theorem comapOfSurjective_iSup {ι : Type*} [Nonempty ι] (I : ι → HopfIdeal R K)
    (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (⨆ i, I i).comapOfSurjective f hf = ⨆ i, (I i).comapOfSurjective f hf := by
  refine le_antisymm (comapOfSurjective_iSup_le I f hf) (sSup_le ?_)
  rintro J ⟨i, rfl⟩
  exact comapOfSurjective_mono f hf (le_sSup ⟨i, rfl⟩)

/-- Surjective inverse image of Hopf ideals preserves joins. -/
@[simp]
theorem comapOfSurjective_sup (I J : HopfIdeal R K) (f : H →ₐc[R] K)
    (hf : Function.Surjective f) :
    (I ⊔ J).comapOfSurjective f hf =
      I.comapOfSurjective f hf ⊔ J.comapOfSurjective f hf := by
  have hsup : I ⊔ J = ⨆ b : Bool, cond b I J := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · exact le_sSup ⟨true, rfl⟩
      · exact le_sSup ⟨false, rfl⟩
    · rw [iSup]
      refine sSup_le ?_
      rintro _ ⟨b, rfl⟩
      cases b <;> simp
  have hsup_comap :
      I.comapOfSurjective f hf ⊔ J.comapOfSurjective f hf =
        ⨆ b : Bool, (cond b I J).comapOfSurjective f hf := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · exact le_sSup ⟨true, rfl⟩
      · exact le_sSup ⟨false, rfl⟩
    · rw [iSup]
      refine sSup_le ?_
      rintro _ ⟨b, rfl⟩
      cases b <;> simp
  calc
    (I ⊔ J).comapOfSurjective f hf =
        (⨆ b : Bool, cond b I J).comapOfSurjective f hf := by
      exact congrArg (fun A : HopfIdeal R K => A.comapOfSurjective f hf) hsup
    _ = ⨆ b : Bool, (cond b I J).comapOfSurjective f hf :=
      comapOfSurjective_iSup (fun b : Bool => cond b I J) f hf
    _ = I.comapOfSurjective f hf ⊔ J.comapOfSurjective f hf := hsup_comap.symm

/-- Surjective inverse image of Hopf ideals preserves nonempty suprema of sets. -/
@[simp]
theorem comapOfSurjective_sSup (S : Set (HopfIdeal R K)) (hS : S.Nonempty)
    (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (sSup S).comapOfSurjective f hf =
      sSup ((fun I => I.comapOfSurjective f hf) '' S) := by
  classical
  have : Nonempty S := hS.to_subtype
  rw [sSup_eq_iSup', comapOfSurjective_iSup, sSup_image']

/-- Pulling a Hopf ideal back along the identity morphism leaves it unchanged. -/
@[simp]
theorem comapOfSurjective_id (I : HopfIdeal R H) :
    I.comapOfSurjective (BialgHom.id R H)
      (by rw [BialgHom.coe_id]; exact Function.surjective_id) = I := by
  ext h
  rw [mem_comapOfSurjective, BialgHom.coe_id]
  rfl

/-- Inverse image of Hopf ideals is compatible with composition of surjective morphisms. -/
@[simp]
theorem comapOfSurjective_comapOfSurjective (I : HopfIdeal R L) (g : K →ₐc[R] L)
    (hg : Function.Surjective g)
    (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (I.comapOfSurjective g hg).comapOfSurjective f hf =
      I.comapOfSurjective (g.comp f) (by rw [BialgHom.coe_comp]; exact hg.comp hf) := by
  ext h
  rw [mem_comapOfSurjective, mem_comapOfSurjective, mem_comapOfSurjective, BialgHom.coe_comp]
  rfl

/-- Pulling a Hopf ideal back along a bialgebra equivalence and then along its inverse recovers the
original ideal. -/
theorem comapOfSurjective_bialgEquiv_symm_apply (I : HopfIdeal R H) (e : H ≃ₐc[R] K) :
    comapOfSurjective
        (I.comapOfSurjective e.symm.toBialgHom
          (by simpa only [BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom] using
            EquivLike.surjective e.symm))
        e.toBialgHom
          (by simpa only [BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom] using
            EquivLike.surjective e) = I := by
  ext h
  rw [mem_comapOfSurjective, mem_comapOfSurjective]
  simp only [BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom,
    e.symm_apply_apply]

section Field

variable {k : Type u} [Field k]
variable [HopfAlgebra k H] [HopfAlgebra k K] [HopfAlgebra k L]

/-- The inverse image of a Hopf ideal along an arbitrary bialgebra morphism over a field.

Unlike `HopfIdeal.comapOfSurjective`, this construction needs no surjectivity hypothesis: over a
field the kernel of every bialgebra morphism is a Hopf ideal. -/
noncomputable def comap (I : HopfIdeal k K) (f : H →ₐc[k] K) : HopfIdeal k H :=
  ker ((Bialgebra.Quotient.mkBialgHom I.toIdeal).comp f)

/-- The underlying ideal of `comap` is the ordinary ideal-theoretic inverse image. -/
@[simp]
theorem comap_toIdeal (I : HopfIdeal k K) (f : H →ₐc[k] K) :
    (I.comap f).toIdeal = Ideal.comap (f : H →+* K) I.toIdeal := by
  rw [comap, ker_toIdeal, ker_quotient_comp]

/-- Membership in the inverse image over a field is membership after applying the morphism. -/
@[simp]
theorem mem_comap {I : HopfIdeal k K} {f : H →ₐc[k] K} {h : H} :
    h ∈ I.comap f ↔ f h ∈ I := by
  rw [← mem_toIdeal, comap_toIdeal, Ideal.mem_comap]
  exact mem_toIdeal

/-- Over a field, the surjective inverse image agrees with the unrestricted construction. -/
theorem comapOfSurjective_eq_comap (I : HopfIdeal k K) (f : H →ₐc[k] K)
    (hf : Function.Surjective f) :
    I.comapOfSurjective f hf = I.comap f := by
  rw [comapOfSurjective_eq_kerOfSurjective, comap, kerOfSurjective_eq_ker]

/-- Inverse image of Hopf ideals over a field is monotone. -/
theorem comap_mono (f : H →ₐc[k] K) {I J : HopfIdeal k K} (hIJ : I ≤ J) :
    I.comap f ≤ J.comap f := by
  intro h hh
  exact mem_comap.mpr (hIJ (mem_comap.mp hh))

/-- The inverse image of the zero Hopf ideal over a field is the Hopf-ideal kernel. -/
@[simp]
theorem comap_bot (f : H →ₐc[k] K) :
    (⊥ : HopfIdeal k K).comap f = ker f := by
  ext h
  rw [mem_comap, mem_ker, mem_bot]

/-- Pulling a Hopf ideal back along the identity over a field leaves it unchanged. -/
@[simp]
theorem comap_id (I : HopfIdeal k H) :
    I.comap (BialgHom.id k H) = I := by
  ext h
  rw [mem_comap, BialgHom.coe_id]
  rfl

/-- Inverse image of Hopf ideals over a field is compatible with composition. -/
@[simp]
theorem comap_comap (I : HopfIdeal k L) (g : K →ₐc[k] L)
    (f : H →ₐc[k] K) :
    (I.comap g).comap f = I.comap (g.comp f) := by
  ext h
  rw [mem_comap, mem_comap, mem_comap, BialgHom.comp_apply]

end Field

end HopfIdeal

end TauCeti
