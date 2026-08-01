/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ClusterSet.Basic

/-!
# Cluster sets of inverse maps

Cluster-set membership is reciprocal for maps that are inverse on their domains. If `f` maps `U`
into `V`, `g` is a left inverse to `f` there, and `v` is approached by `f z` as `z` approaches
`w` through `U`, then `w` is approached by `g y` as `y` approaches `v` through `V`. When `f` and
`g` are mutual inverses this gives the equivalence

`v ∈ clusterSetOn f U w ↔ w ∈ clusterSetOn g V v`.

No continuity is needed: the assertion only exchanges the same nearby pairs `(z, f z)` using the
inverse identities. The proof is therefore stated for arbitrary topological spaces, at the same
generality as `TauCeti.clusterSetOn` itself. The specialisation to `Function.invFunOn` is the form
used by a bijection presented through `Set.BijOn`.

The intended consumer is layer **L5** of the conformal-mapping roadmap, the Carathéodory boundary
correspondence. For a conformal bijection and its set-level inverse, reciprocity turns uniqueness of
the inverse boundary cluster set into injectivity of a continuous extension of the forward map.
That conformal consequence is in `TauCeti/Analysis/Complex/Conformal/Reciprocity.lean`.

## Main results

* `TauCeti.mem_clusterSetOn_of_leftInvOn` — one direction, requiring only a left inverse and a
  mapping property.
* `TauCeti.mem_clusterSetOn_invOn_iff` — reciprocity for mutual inverses.
* `TauCeti.clusterSetOn_invOn` — the inverse cluster set as the set of source points whose forward
  cluster set contains the given value.
* `TauCeti.injOn_of_clusterSetOn_inverse_subsingleton` — a continuous extension is injective on a
  set if the corresponding inverse cluster sets are subsingletons.
* `TauCeti.mem_clusterSetOn_invFunOn_iff` and `TauCeti.clusterSetOn_invFunOn` — the corresponding
  forms for `Function.invFunOn` of a `Set.BijOn` map.

## References

* E. F. Collingwood and A. J. Lohwater, *The Theory of Cluster Sets*, Ch. 1.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Filter Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {U : Set X} {V : Set Y} {f : X → Y} {g : Y → X} {w : X} {v : Y}

/-- **Cluster-set membership transfers to a left inverse.** Suppose `f` maps `U` into `V` and
`g (f z) = z` on `U`. If `f z` approaches `v` along points `z ∈ U` approaching `w`, then those
same pairs, read in reverse, show that `g y` approaches `w` along points `y ∈ V` approaching `v`.

Neither map is assumed continuous. -/
theorem mem_clusterSetOn_of_leftInvOn (hgf : LeftInvOn g f U) (hf : MapsTo f U V)
    (hv : v ∈ clusterSetOn f U w) : w ∈ clusterSetOn g V v := by
  rw [mem_clusterSetOn_iff_frequently]
  intro s hs
  rw [Filter.frequently_iff]
  intro q hq
  obtain ⟨t, ht, htq⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hq
  have hfreq : ∃ᶠ z in 𝓝[U] w, f z ∈ t :=
    mem_clusterSetOn_iff_frequently.mp hv t ht
  obtain ⟨z, hzt, hzU, hzs⟩ :=
    (hfreq.and_eventually (inter_mem_nhdsWithin U hs)).exists
  exact ⟨f z, htq ⟨hzt, hf hzU⟩, by simpa only [hgf hzU] using hzs⟩

/-- **Cluster-set reciprocity for inverse maps.** If `f : U → V` and `g : V → U` are inverse,
then `v` is a cluster value of `f` at `w` exactly when `w` is a cluster value of `g` at `v`.

The two `MapsTo` hypotheses record that the inverse identities are being used between the stated
sets; `InvOn` itself contains only the two pointwise identities. -/
theorem mem_clusterSetOn_invOn_iff (hinv : InvOn g f U V) (hf : MapsTo f U V)
    (hg : MapsTo g V U) :
    v ∈ clusterSetOn f U w ↔ w ∈ clusterSetOn g V v :=
  ⟨mem_clusterSetOn_of_leftInvOn hinv.1 hf,
    mem_clusterSetOn_of_leftInvOn hinv.2 hg⟩

/-- The cluster set of an inverse map at `v` consists exactly of the source points `w` whose
forward cluster set contains `v`. -/
theorem clusterSetOn_invOn (hinv : InvOn g f U V) (hf : MapsTo f U V)
    (hg : MapsTo g V U) :
    clusterSetOn g V v = {w | v ∈ clusterSetOn f U w} := by
  ext x
  exact (mem_clusterSetOn_invOn_iff hinv hf hg).symm

/-- **Inverse cluster sets detect injectivity of a continuous extension.** Let `F` be a continuous
extension of `f` from `U` to `closure U`, and let `A ⊆ closure U`. Suppose `F` maps `A` into a set
`B` at whose points the cluster sets of an inverse `g : V → U` are subsingletons. Then `F` is
injective on `A`.

Indeed, `F x` belongs to the forward cluster set at each `x ∈ A`, because `F` is a continuous
extension. Reciprocity puts `x` in the inverse cluster set at `F x`; hence two points of `A` with
the same `F`-value lie in one subsingleton inverse cluster set. No separation hypothesis is
needed. -/
theorem injOn_of_clusterSetOn_inverse_subsingleton {A : Set X} {B : Set Y}
    {F : X → Y} (hA : A ⊆ closure U) (hFB : MapsTo F A B)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U)
    (hinv : InvOn g f U V) (hf : MapsTo f U V) (hg : MapsTo g V U)
    (hsub : ∀ y ∈ B, (clusterSetOn g V y).Subsingleton) :
    InjOn F A := by
  intro x hx y hy hxy
  have hxmem : F x ∈ clusterSetOn f U x :=
    mem_clusterSetOn_of_continuousOn_extension (hA hx) hFc hFf
  have hymem : F y ∈ clusterSetOn f U y :=
    mem_clusterSetOn_of_continuousOn_extension (hA hy) hFc hFf
  have hxinv : x ∈ clusterSetOn g V (F x) :=
    (mem_clusterSetOn_invOn_iff hinv hf hg).mp hxmem
  have hyinv : y ∈ clusterSetOn g V (F x) := by
    simpa only [hxy] using (mem_clusterSetOn_invOn_iff hinv hf hg).mp hymem
  exact hsub (F x) (hFB hx) hxinv hyinv

section InvFunOn

variable [Nonempty X]

/-- **Cluster-set reciprocity for `Function.invFunOn`.** For a bijection `f : U → V`, a value `v`
is in the forward cluster set at `w` exactly when `w` is in the cluster set of the canonical
set-level inverse at `v`. -/
theorem mem_clusterSetOn_invFunOn_iff (hbij : BijOn f U V) :
    v ∈ clusterSetOn f U w ↔
      w ∈ clusterSetOn (Function.invFunOn f U) V v :=
  mem_clusterSetOn_invOn_iff hbij.invOn_invFunOn hbij.mapsTo
    hbij.surjOn.mapsTo_invFunOn

/-- The cluster set of `Function.invFunOn f U` at `v`, expressed entirely through the forward
cluster sets of a bijection `f : U → V`. -/
theorem clusterSetOn_invFunOn (hbij : BijOn f U V) :
    clusterSetOn (Function.invFunOn f U) V v =
      {w | v ∈ clusterSetOn f U w} :=
  clusterSetOn_invOn hbij.invOn_invFunOn hbij.mapsTo hbij.surjOn.mapsTo_invFunOn

end InvFunOn

end TauCeti
