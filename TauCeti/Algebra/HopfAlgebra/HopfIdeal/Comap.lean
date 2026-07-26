/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.HopfAlgebra.Kernel

/-!
# Inverse images of Hopf ideals along surjective Hopf algebra morphisms

This file records the inverse image of a Hopf ideal along a surjective bialgebra morphism.
For a surjective morphism `f : H →ₐc[R] K` and a Hopf ideal `I` of `K`, the preimage
`f ⁻¹ I` is a Hopf ideal of `H`. The construction is made by applying the existing
kernel-of-a-surjective-Hopf-map theorem to the composite `H → K → K/I`.

The surjectivity hypothesis is intentional: over a general commutative base, the tensor
exactness needed for the coideal condition is not automatic without an exactness hypothesis.

This is a Layer 3 prerequisite for the reductive-groups roadmap target "Hopf ideals ↔ closed
subgroup schemes", including kernels and pullback-style operations on closed subgroup
schemes in the affine Hopf-algebra dictionary.

## Main declarations

* `TauCeti.HopfIdeal.comap`: the inverse image of a Hopf ideal under a surjective morphism.
* `TauCeti.HopfIdeal.comap_toIdeal` and `TauCeti.HopfIdeal.mem_comap`: characteristic API.
* `TauCeti.HopfIdeal.comap_le_comap_iff_of_surjective`: surjective inverse image reflects
  containment.
* `TauCeti.HopfIdeal.comap_bot`: the kernel of a surjective morphism is the inverse image of
  the zero Hopf ideal.
* `TauCeti.HopfIdeal.comap_sup_of_surjective`: surjective inverse image preserves binary joins.
* `TauCeti.HopfIdeal.comap_iSup_of_surjective` and
  `TauCeti.HopfIdeal.comap_sSup_of_surjective`: surjective inverse image preserves nonempty
  suprema.
* `TauCeti.HopfIdeal.comap_id` and `TauCeti.HopfIdeal.comap_comap`: identity and composition
  laws.

## References

The construction is the standard inverse image of a Hopf ideal along a surjective Hopf algebra
morphism, reduced here to the quotient-kernel construction already in
`TauCeti.Algebra.HopfAlgebra.Kernel`.
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
noncomputable def comap (I : HopfIdeal R K) (f : H →ₐc[R] K)
    (hf : Function.Surjective f) : HopfIdeal R H :=
  ker ((Bialgebra.Quotient.mkBialgHom I.toIdeal).comp f)
    ((Ideal.Quotient.mkₐ_surjective R I.toIdeal).comp hf)

/-- The underlying ideal of `I.comap f hf` is the ordinary ideal-theoretic inverse image. -/
@[simp]
theorem comap_toIdeal (I : HopfIdeal R K) (f : H →ₐc[R] K)
    (hf : Function.Surjective f) :
    (I.comap f hf).toIdeal = Ideal.comap (f : H →+* K) I.toIdeal := by
  ext h
  rw [mem_toIdeal, comap, mem_ker, Ideal.mem_comap, BialgHom.coe_comp,
    Function.comp_apply, Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact mem_toIdeal.symm

/-- Membership in the inverse-image Hopf ideal is membership after applying the morphism. -/
@[simp]
theorem mem_comap {I : HopfIdeal R K} {f : H →ₐc[R] K} {hf : Function.Surjective f}
    {h : H} : h ∈ I.comap f hf ↔ f h ∈ I := by
  rw [← mem_toIdeal, comap_toIdeal, Ideal.mem_comap]
  exact mem_toIdeal

/-- Inverse image of Hopf ideals is monotone. -/
theorem comap_mono (f : H →ₐc[R] K) (hf : Function.Surjective f)
    {I J : HopfIdeal R K} (hIJ : I ≤ J) : I.comap f hf ≤ J.comap f hf := by
  intro h hh
  exact mem_comap.mpr (hIJ (mem_comap.mp hh))

/-- For a surjective morphism, inverse image of Hopf ideals reflects containment. -/
theorem le_of_comap_le_comap_of_surjective (f : H →ₐc[R] K)
    (hf : Function.Surjective f) {I J : HopfIdeal R K}
    (hIJ : I.comap f hf ≤ J.comap f hf) : I ≤ J := by
  intro k hk
  obtain ⟨h, rfl⟩ := hf k
  exact mem_comap.mp (hIJ (mem_comap.mpr hk))

/-- For a surjective morphism, containment after inverse image is equivalent to containment
before inverse image. -/
theorem comap_le_comap_iff_of_surjective (f : H →ₐc[R] K)
    (hf : Function.Surjective f) {I J : HopfIdeal R K} :
    I.comap f hf ≤ J.comap f hf ↔ I ≤ J :=
  ⟨le_of_comap_le_comap_of_surjective f hf, comap_mono f hf⟩

/-- For a surjective morphism, inverse image of Hopf ideals reflects equality. -/
@[simp]
theorem comap_eq_comap_iff_of_surjective (f : H →ₐc[R] K)
    (hf : Function.Surjective f) {I J : HopfIdeal R K} :
    I.comap f hf = J.comap f hf ↔ I = J := by
  constructor
  · intro h
    apply le_antisymm
    · rw [← comap_le_comap_iff_of_surjective f hf, h]
    · rw [← comap_le_comap_iff_of_surjective f hf, h]
  · intro h
    rw [h]

/-- The inverse image of the zero Hopf ideal is the kernel Hopf ideal. -/
@[simp]
theorem comap_bot (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (⊥ : HopfIdeal R K).comap f hf = ker f hf := by
  ext h
  rw [mem_comap, mem_ker, mem_bot]

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
images: the nontrivial inclusion of `comap_iSup_of_surjective`. -/
private theorem comap_iSup_le {ι : Type*} [Nonempty ι] (I : ι → HopfIdeal R K)
    (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (⨆ i, I i).comap f hf ≤ ⨆ i, (I i).comap f hf := by
  classical
  intro h hh
  rw [mem_comap, mem_iSup] at hh
  obtain ⟨s, hs, hsum⟩ := hh
  obtain ⟨t, ht, ht_sum⟩ := exists_finsupp_map_eq f hf s
  let i0 : ι := Classical.choice ‹Nonempty ι›
  -- Lift `s` to `t`, then correct the `i0` coordinate so the total sum lands on `h`.
  refine mem_iSup.mpr ⟨t + Finsupp.single i0 (h - t.sum fun _ y => y), fun i => ?_, ?_⟩
  · have hfin : f (t i) ∈ I i := by rw [ht i]; exact hs i
    rw [mem_comap, Finsupp.add_apply, map_add]
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
theorem comap_iSup_of_surjective {ι : Type*} [Nonempty ι] (I : ι → HopfIdeal R K)
    (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (⨆ i, I i).comap f hf = ⨆ i, (I i).comap f hf := by
  refine le_antisymm (comap_iSup_le I f hf) (sSup_le ?_)
  rintro J ⟨i, rfl⟩
  exact comap_mono f hf (le_sSup ⟨i, rfl⟩)

/-- Surjective inverse image of Hopf ideals preserves joins. -/
@[simp]
theorem comap_sup_of_surjective (I J : HopfIdeal R K) (f : H →ₐc[R] K)
    (hf : Function.Surjective f) :
    (I ⊔ J).comap f hf = I.comap f hf ⊔ J.comap f hf := by
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
      I.comap f hf ⊔ J.comap f hf = ⨆ b : Bool, (cond b I J).comap f hf := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · exact le_sSup ⟨true, rfl⟩
      · exact le_sSup ⟨false, rfl⟩
    · rw [iSup]
      refine sSup_le ?_
      rintro _ ⟨b, rfl⟩
      cases b <;> simp
  calc
    (I ⊔ J).comap f hf = (⨆ b : Bool, cond b I J).comap f hf := by
      exact congrArg (fun A : HopfIdeal R K => A.comap f hf) hsup
    _ = ⨆ b : Bool, (cond b I J).comap f hf :=
      comap_iSup_of_surjective (fun b : Bool => cond b I J) f hf
    _ = I.comap f hf ⊔ J.comap f hf := hsup_comap.symm

/-- Surjective inverse image of Hopf ideals preserves nonempty suprema of sets. -/
@[simp]
theorem comap_sSup_of_surjective (S : Set (HopfIdeal R K)) (hS : S.Nonempty)
    (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (sSup S).comap f hf = sSup ((fun I => I.comap f hf) '' S) := by
  classical
  haveI : Nonempty S := hS.to_subtype
  rw [sSup_eq_iSup', comap_iSup_of_surjective, sSup_image']

/-- Pulling a Hopf ideal back along the identity morphism leaves it unchanged. -/
@[simp]
theorem comap_id (I : HopfIdeal R H) :
    I.comap (BialgHom.id R H) (fun h => ⟨h, rfl⟩) = I := by
  ext h
  rw [mem_comap, BialgHom.coe_id]
  rfl

/-- Inverse image of Hopf ideals is compatible with composition of surjective morphisms. -/
@[simp]
theorem comap_comap (I : HopfIdeal R L) (g : K →ₐc[R] L) (hg : Function.Surjective g)
    (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (I.comap g hg).comap f hf = I.comap (g.comp f) (hg.comp hf) := by
  ext h
  rw [mem_comap, mem_comap, mem_comap, BialgHom.coe_comp]
  rfl

end HopfIdeal

end TauCeti
