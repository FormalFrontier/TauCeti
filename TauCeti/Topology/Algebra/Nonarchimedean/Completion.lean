/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Algebra.Nonarchimedean.Completion
public import Mathlib.Topology.Algebra.Ring.Ideal
public import TauCeti.RingTheory.IntegralClosure.PowRelation
public import TauCeti.Topology.Algebra.Ring.Subring

/-!
# Completions of nonarchimedean groups and rings

Three facts about the Hausdorff completion that need only the additive, resp. ring, structure:
the closure of the image of an open additive subgroup is open, the kernel of the completion map
is the closure of the zero ideal, and integral closedness of an open subring survives completion.

They are stated here rather than alongside the Huber-ring theory that uses them, since none
mentions a pair of definition or an adic topology, and they live in the `UniformSpace.Completion`
namespace of the construction they describe rather than in a `TauCeti` one.

The last of the three is Huber's Lemma 2.4.3(iv), Wedhorn's Lemma 7.47(4): if `G` is *open*
and integrally closed in `A`, the closure `Ĝ` of its image in `Â` is integrally closed in `Â`.
The proof below is Huber's. The integral closure `H` of `Ĝ` in `Â` contains the open subring
`Ĝ`, hence is open, so every neighbourhood of a point of `H` meets the image of `A` inside `H`.
For such an image `i b`, an integral relation over `Ĝ` is perturbed one coefficient at a time
into a relation whose coefficients come from `G`; openness of `Ĝ` keeps the value of the
perturbed relation at `i b` inside `Ĝ`, and an open `G` is closed, hence exactly the preimage of
`Ĝ`, so that value is the image of an element of `G`. Subtracting it from the constant term
leaves an integral relation for `b` over `G`, so `b ∈ G`, and `i b` therefore lies in the image
of `G`.

## Main results

* `UniformSpace.Completion.isOpen_closure_image_coe`: the closure in `Â` of the image of an open
  additive subgroup of `A` is open, and
  `UniformSpace.Completion.isOpen_topologicalClosure_map_coeRingHom` says the same of an open
  subring.
* `UniformSpace.Completion.ker_coeRingHom`: the kernel of `A → Â` is the closure of `⊥`.
* `UniformSpace.Completion.isIntegrallyClosedIn_topologicalClosure_map_coeRingHom`:
  Huber's Lemma 2.4.3(iv), the closure in `Â` of the image of an open subring of `A` integrally
  closed in `A` is integrally closed in `Â`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition and Definition 5.32 and Example 5.33, for
  the completion of a topological group and ring; `ker_coeRingHom` is the statement there that
  the completion map has kernel `closure {0}`. Lemma 7.47(4) there is the statement that integral
  closedness of an open subring survives completion.
* R. Huber, *Bewertungsspektrum und rigide Geometrie*, Regensburger Mathematische Schriften 23,
  Universität Regensburg, 1993, Lemma 2.4.3(iv), whose proof
  `UniformSpace.Completion.isIntegrallyClosedIn_topologicalClosure_map_coeRingHom` follows.
* Mathlib's `Mathlib/Topology/Algebra/Nonarchimedean/Completion.lean`, whose openness proof runs
  the same `closure_image_mem_nhds`-then-`isOpen_of_mem_nhds` argument these proofs follow.
-/

public section

open UniformSpace

namespace UniformSpace.Completion

section AddGroup

variable {A : Type*} [AddCommGroup A] [UniformSpace A] [IsUniformAddGroup A]

/-- The closure in the completion of the image of an open additive subgroup is open. Only the
additive structure is involved. -/
theorem isOpen_closure_image_coe {G : AddSubgroup A} (hG : IsOpen (G : Set A)) :
    IsOpen (closure (((↑) : A → Completion A) '' (G : Set A))) := by
  have hmem := Completion.isDenseInducing_coe.closure_image_mem_nhds (hG.mem_nhds G.zero_mem)
  rw [Completion.coe_zero] at hmem
  exact AddSubgroup.isOpen_of_mem_nhds ((G.map Completion.toCompl).topologicalClosure) hmem

end AddGroup

section Ring

variable {A : Type*} [Ring A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]

/-- The completion map `A →+* Â`, read as a function, is the coercion `A → Â`. Mathlib's
`Filter.Germ.coe_coeRingHom` is the same statement for germs. -/
@[simp]
theorem coe_coeRingHom :
    ⇑(Completion.coeRingHom : A →+* Completion A) = ((↑) : A → Completion A) := (rfl)

/-- The kernel of the completion map `A → Â` is the closure of the zero ideal. -/
theorem ker_coeRingHom :
    RingHom.ker (Completion.coeRingHom : A →+* Completion A) = (⊥ : Ideal A).closure := by
  ext x
  rw [RingHom.mem_ker, ← SetLike.mem_coe, Ideal.coe_closure]
  calc (Completion.coeRingHom x = 0)
      ↔ ((x : Completion A) = ((0 : A) : Completion A)) := by rw [Completion.coe_zero]; rfl
    _ ↔ Inseparable ((x : Completion A)) (((0 : A) : Completion A)) := inseparable_iff_eq.symm
    _ ↔ Inseparable x (0 : A) := Completion.isDenseInducing_coe.isInducing.inseparable_iff
    _ ↔ x - 0 ∈ closure ({0} : Set A) := addGroup_inseparable_iff
    _ ↔ x ∈ closure ((⊥ : Ideal A) : Set A) := by rw [sub_zero]; simp

/-- The closure `Ĝ` in `Â` of the image of a subring `G` of `A` is, as a set, the closure of the
image of `G` under the completion coercion. This unfolds `Subring.topologicalClosure` and
`Subring.map` in one step; it is how every argument below passes between `Ĝ` and that closure. -/
theorem coe_topologicalClosure_map_coeRingHom (G : Subring A) :
    ((G.map Completion.coeRingHom).topologicalClosure : Set (Completion A))
      = closure (((↑) : A → Completion A) '' (G : Set A)) := by
  rw [Subring.topologicalClosure_coe, Subring.coe_map, coe_coeRingHom]

/-- Membership in the closure `Ĝ` in `Â` of the image of a subring `G` of `A`, in the form the
`closure` API consumes. This is the `mem_`-half of the pair whose `coe_` half is above; the
proofs below pass between the two forms at three separate sites. -/
@[simp]
theorem mem_topologicalClosure_map_coeRingHom_iff {G : Subring A} {x : Completion A} :
    x ∈ (G.map Completion.coeRingHom).topologicalClosure
      ↔ x ∈ closure (((↑) : A → Completion A) '' (G : Set A)) := by
  rw [← SetLike.mem_coe, coe_topologicalClosure_map_coeRingHom]

/-- The closure in `Â` of the image of an open subring of `A` is open: the subring form of
`isOpen_closure_image_coe`. -/
theorem isOpen_topologicalClosure_map_coeRingHom {G : Subring A} (hG : IsOpen (G : Set A)) :
    IsOpen ((G.map Completion.coeRingHom).topologicalClosure : Set (Completion A)) := by
  rw [coe_topologicalClosure_map_coeRingHom, ← Subring.coe_toAddSubgroup]
  exact isOpen_closure_image_coe (G := G.toAddSubgroup) (by rwa [Subring.coe_toAddSubgroup])

end Ring

section IntegrallyClosed

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]

/-- The one analytic step of Huber's Lemma 2.4.3(iv): an element `y` of the closure `Ĝ` of the
image of an *open* subring `G` can be replaced by the image of an element of `G` so closely that
`Ĝ` still absorbs the error after it is multiplied by an arbitrary `z`.

Openness is exactly what is used: it makes `Ĝ` a neighbourhood of zero, so multiplication by `z`
carries a small enough neighbourhood of `y` back into `Ĝ`, and `y` lies in the closure of the
image of `G`, which supplies a point of that neighbourhood. -/
private theorem exists_mem_coe_sub_mul_mem_topologicalClosure {G : Subring A}
    (hG : IsOpen (G : Set A)) {y : Completion A}
    (hy : y ∈ (G.map Completion.coeRingHom).topologicalClosure) (z : Completion A) :
    ∃ d ∈ G, ((d : Completion A) - y) * z ∈ (G.map Completion.coeRingHom).topologicalClosure := by
  have hVopen : IsOpen ((fun w : Completion A ↦ (w - y) * z) ⁻¹'
      ((G.map Completion.coeRingHom).topologicalClosure : Set (Completion A))) :=
    (isOpen_topologicalClosure_map_coeRingHom hG).preimage (by fun_prop)
  have hyV : y ∈ (fun w : Completion A ↦ (w - y) * z) ⁻¹'
      ((G.map Completion.coeRingHom).topologicalClosure : Set (Completion A)) := by
    simp only [Set.mem_preimage, sub_self, zero_mul, SetLike.mem_coe]
    exact Subring.zero_mem _
  obtain ⟨_, hw, d, hdG, rfl⟩ :=
    mem_closure_iff.mp
      (mem_topologicalClosure_map_coeRingHom_iff.mp hy) _ hVopen hyV
  exact ⟨d, hdG, hw⟩

/-- Huber's Lemma 2.4.3(iv) for a single element of `A`: if the image in `Â` of `b : A` is integral
over the closure `Ĝ` of the image of an open subring `G`, then `b` is already integral over `G`.

An integral relation for the image of `b` over `Ĝ` is perturbed one coefficient at a time by
`exists_mem_coe_sub_mul_mem_topologicalClosure`, which leaves the value of the relation at the
image of `b` inside `Ĝ`. Being open, `G` is closed, hence exactly the preimage of `Ĝ`
(`IsInducing.closure_eq_preimage_closure_image`), so that value is the image of an element of
`G`; subtracting it from the constant term turns the perturbed relation into one over `G`. -/
private theorem isIntegral_of_isIntegral_topologicalClosure_coe {G : Subring A}
    (hG : IsOpen (G : Set A)) {b : A}
    (hb : IsIntegral ((G.map Completion.coeRingHom).topologicalClosure) (b : Completion A)) :
    IsIntegral G b := by
  -- the pointwise form of `coe_coeRingHom`, which is what exposes `map_sum` and friends
  have hcoe (y : A) : (y : Completion A) = Completion.coeRingHom y :=
    congrFun coe_coeRingHom.symm y
  -- an open subring is closed, and the completion map is inducing, so the closure of the image
  -- pulls back to `G` itself
  have hpre : ((↑) : A → Completion A) ⁻¹'
      ((G.map Completion.coeRingHom).topologicalClosure : Set (Completion A)) = (G : Set A) := by
    rw [coe_topologicalClosure_map_coeRingHom,
      ← Completion.isDenseInducing_coe.isInducing.closure_eq_preimage_closure_image,
      ← Subring.coe_toAddSubgroup, (G.toAddSubgroup.isClosed_of_isOpen hG).closure_eq]
  obtain ⟨n, c, hcmem, hc⟩ := TauCeti.exists_pow_add_sum_eq_zero_of_isIntegral hb
  choose! d hdG hd using fun (i : ℕ) (hi : i < n + 1) ↦
    exists_mem_coe_sub_mul_mem_topologicalClosure hG (hcmem i hi) ((b : Completion A) ^ i)
  obtain ⟨e, hedef⟩ : ∃ e : A, e = b ^ (n + 1) + ∑ i ∈ Finset.range (n + 1), d i * b ^ i := ⟨_, rfl⟩
  -- the perturbed relation evaluates inside `Ĝ`, so its value comes from `G`
  have hecoe : (e : Completion A)
      = ∑ i ∈ Finset.range (n + 1), ((d i : Completion A) - c i) * (b : Completion A) ^ i := by
    simp only [hedef, hcoe, map_add, map_pow, map_sum, map_mul, sub_mul,
      Finset.sum_sub_distrib] at hc ⊢
    linear_combination hc
  have heG : e ∈ G := by
    rw [← SetLike.mem_coe, ← hpre, Set.mem_preimage, SetLike.mem_coe, hecoe]
    exact Subring.sum_mem _ fun i hi ↦ hd i (Finset.mem_range.mp hi)
  -- subtracting that value from the constant term leaves a relation for `b` over `G`
  have harith : b ^ (n + 1)
      + ((∑ i ∈ Finset.range n, d (i + 1) * b ^ (i + 1)) + (d 0 - e) * b ^ 0) = 0 := by
    rw [hedef, Finset.sum_range_succ']
    ring
  refine TauCeti.isIntegral_of_pow_add_sum_eq_zero (n := n)
    (c := fun i ↦ Nat.casesOn i (d 0 - e) fun j ↦ d (j + 1)) ?_ ?_
  · rintro (_ | j) hi
    · exact sub_mem (hdG 0 hi) heG
    · exact hdG (j + 1) hi
  · rwa [Finset.sum_range_succ']

/-- **Huber's Lemma 2.4.3(iv)**: the closure in `Â` of the image of an open subring `G` of `A` that
is integrally closed in `A` is integrally closed in `Â`. -/
theorem isIntegrallyClosedIn_topologicalClosure_map_coeRingHom {G : Subring A}
    (hG : IsOpen (G : Set A)) [IsIntegrallyClosedIn G A] :
    IsIntegrallyClosedIn ((G.map Completion.coeRingHom).topologicalClosure) (Completion A) := by
  refine Subring.isIntegrallyClosedIn_iff.mpr fun a ha ↦ ?_
  -- the integral closure `H` of `Ĝ` is a subring containing the open `Ĝ`, hence is itself open
  have hHopen := isOpen_integralClosure_toSubring (isOpen_topologicalClosure_map_coeRingHom hG)
  -- so it is enough to meet the image of `G` in every neighbourhood `t` of `a`
  rw [mem_topologicalClosure_map_coeRingHom_iff]
  refine mem_closure_iff_nhds.mpr fun t ht ↦ ?_
  -- density supplies a `b : A` whose image lies in `t` and, being in the open `H`, is integral
  obtain ⟨b, hb⟩ := Completion.denseRange_coe.mem_nhds (Filter.inter_mem ht
    (hHopen.mem_nhds (Subalgebra.mem_toSubring.mpr ((mem_integralClosure_iff _ _).mpr ha))))
  exact ⟨(b : Completion A), hb.1, b, Subring.isIntegrallyClosedIn_iff.mp ‹_›
    (isIntegral_of_isIntegral_topologicalClosure_coe hG
      ((mem_integralClosure_iff _ _).mp (Subalgebra.mem_toSubring.mp hb.2))), rfl⟩

end IntegrallyClosed

end UniformSpace.Completion
