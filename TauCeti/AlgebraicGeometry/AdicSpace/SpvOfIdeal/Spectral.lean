/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Spectral.Hom
public import TauCeti.AlgebraicGeometry.AdicSpace.RestrictToIdeal
public import TauCeti.AlgebraicGeometry.AdicSpace.PatchPresentation
public import TauCeti.Topology.Spectral.SpectralMap
import TauCeti.Topology.Spectral.PatchCriterion

/-!
# `Spv (A, I)` is a spectral space

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Lemma 7.5(1).**

Wedhorn gives `Spv (A, I)` the subspace topology of `Spv A` (§7.1, after (7.1.1)) and proves it
spectral with the sets

```text
Spv (A, I)(T/s) = { v ∈ Spv (A, I) ; v(t) ≤ v(s) ≠ 0 for all t ∈ T },   I ⊆ √(T · A)
```

as a generating family. (Wedhorn states them as a basis of quasi-compact opens, and that is what
is proved: they generate the topology, which is what the patch criterion consumes; each is
quasi-compact; and the family is stable under intersection — Wedhorn's step (i) — which upgrades
generation to `isTopologicalBasis_rationalFamily`.)
No second topology on the subtype is introduced here: the
`Subtype` instance *is* that topology, which is the content of
`instTopologicalSpace_spvOfIdeal_eq_generateFrom`.

The proof is Wedhorn's, via the patch criterion `TauCeti.spectralSpace_of_isClopen_generateFrom`
(his Proposition 3.31). The compact witness topology it consumes is the one **coinduced along
the retraction** `r_I : Spv A → Spv (A, I)` from the patch topology of `Spv A`. That choice is
what makes the proof short: continuity of `r_I` holds by construction, and compactness is then
the image of the compact `(Spv A)_cons` under a surjection. Wedhorn's step (iii) is still
needed, but only as `restrictToIdealCodRestrict_preimage`, which turns clopen-ness of
`Spv(A)(T/s)` in the patch of `Spv A` into clopen-ness of `Spv(A,I)(T/s)` in the witness
topology.

Wedhorn's step (i) — stability of the family under intersection — is **not** needed for
spectrality: the subspace topology is `induced` of a `generateFrom`, so `induced_generateFrom_eq`
reduces the basis condition to single subbasic opens, and the patch criterion absorbs finite
intersections itself. It is needed for the *basis* claim, and later for the spectral-map half of
Lemma 7.5(2), so it is proved here all the same: `basicOpenFinset_inter` supplies the identity in
`Spv A`, `IsAdmissible.mul` keeps the product pair admissible, and `inter_mem_rationalFamily`
closes the family.

Note that `Spv (A, I)` is *not* pro-constructible in `Spv A` in general, so
`TauCeti.IsProConstructible.spectralSpace` cannot be used: that would give a spectral inclusion
(`TauCeti.IsProConstructible.isSpectralMap_subtypeVal`), which Wedhorn's Remark 7.6 denies.

## Main definitions

* `TauCeti.ValuationSpectrum.basicOpenFinset` : Wedhorn's `Spv(A)(T/s)` for finite `T`.
* `TauCeti.ValuationSpectrum.IsAdmissible` : his condition `I ⊆ √(T · A)` on a numerator set.
* `TauCeti.ValuationSpectrum.rationalFamily` : Wedhorn's family `R`, which generates the
  topology of `Spv (A, I)`.
(Two things used in the proof are deliberately private: the compact witness topology coinduced
along `r_I`, a device for the patch criterion rather than API, and the two branch lemmas of step
(ii), whose statements are specific to the case split. `exists_isAdmissible_basicOpenFinset`
below is the public neighbourhood interface that merges them.)

## Main results

* `TauCeti.ValuationSpectrum.spectralSpace_spvOfIdeal` : **Lemma 7.5(1)**.
* `TauCeti.ValuationSpectrum.instTopologicalSpace_spvOfIdeal_eq_generateFrom` : **step (ii)**,
  that `R` generates the subspace topology.
* `TauCeti.ValuationSpectrum.isTopologicalBasis_rationalFamily` : **step (i)**, that `R` is
  moreover a *basis* — it is closed under intersection, through `IsAdmissible.mul` and
  `inter_mem_rationalFamily`.
* `TauCeti.ValuationSpectrum.restrictToIdealCodRestrict_preimage` : **step (iii)**,
  `r_I⁻¹(Spv(A,I)(T/s)) = Spv(A)(T/s)`.
* `TauCeti.ValuationSpectrum.isCompact_of_mem_rationalFamily` : the members of `R` are
  quasi-compact, the other half of what Lemma 7.5(1) asserts about them.
* `TauCeti.ValuationSpectrum.continuous_restrictToIdealCodRestrict` : **Lemma 7.5(2)**, the
  continuity half — steps (ii) and (iii) give it at once.
* `TauCeti.ValuationSpectrum.isSpectralMap_restrictToIdealCodRestrict` : **Lemma 7.5(2)**, the
  spectral-map half, closing out Lemma 7.5: spectrality is tested on the basis `R`, whose
  preimages step (iii) computes and `isCompact_basicOpenFinset` bounds.
* `TauCeti.ValuationSpectrum.isProConstructible_val_preimage_setOfPred_forall_vle_one` : the
  sub-unit locus of a set of ring elements is pro-constructible in `Spv (A, I)` — the form
  Wedhorn's Theorem 7.35 consumes, proved from the rational family since the inclusion into
  `Spv A` is not spectral.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Lemma 7.5 and Proposition 3.31.

## Provenance

The corresponding development in AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), project
`projects/AdicSpaces/`, file `Adic spaces/SpvAITopology.lean`, was consulted rather than copied,
and this file departs from it in two ways. Two revisions are cited below, each for what was
checked against it: branch `dev/adic-spaces` at `37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`, the
revision the spectrality material here was written against, and
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, the revision re-checked when Lemma 7.5(2) was added.

First, AINTLIB equips `Spv (A, I)` with a *separate* topology, `SpvAI.topology`, described there
as strictly finer than the subspace topology. That reading of Remark 7.6 is not Wedhorn's:
Remark 7.6 says the inclusion is not a spectral *map*, whereas Wedhorn's step (ii) proves `R` to
be a basis of the subspace topology itself. AINTLIB proves only the trivial half,
`SpvAI.topology_le_induced`; the converse is `instTopologicalSpace_spvOfIdeal_eq_generateFrom`
here, and the two topologies therefore agree.

Second, AINTLIB's route to compactness and quasi-soberness goes through
`SpvAI.retraction_continuous`. At `2baa76f742bdb4fb8ee323fabba41203bd390e08` that theorem carries
a proof, but it rests on `Spv.restrictIdeal_preimage_basicOpen_isOpen` — openness of
`r_I⁻¹(Spv(A)(f/s))` for an *arbitrary* pair `(f, s)` — which is a `sorry` there, as is
`SpvAI.retraction_preimage_rationalSubset`. Taking the witness topology coinduced along the
retraction removes the need for continuity in the proof of 7.5(1), and quasi-soberness then comes
from the patch criterion rather than from a transfer along the retraction. Continuity is proved
below all the same, as Lemma 7.5(2) in its own right, and by a route that needs only the
*admissible* preimages already computed for 7.5(1) — never the general-`(f, s)` statement.

The two branches of step (ii) below follow AINTLIB's `SpvAI.exists_rationalSubset_microbial` and
`SpvAI.exists_rationalSubset_cofinality`, which are proved there; they are restated against
`characteristicSubgroup … = ⊤` and `CofinalValue` rather than `IsMicrobial`, and the cofinal
branch takes one exponent per generator instead of a uniform one.
-/

public section

namespace TauCeti.ValuationSpectrum

open Set Topology TopologicalSpace TauCeti Valuation MonoidWithZeroHom

variable {A : Type*} [CommRing A]

/-! ### Admissible numerator sets -/

/-- **Wedhorn's condition `I ⊆ √(T · A)`** on a numerator set, in the form that also absorbs the
denominator — harmless because `Spv(A,I)(T/s) = Spv(A,I)((T ∪ {s})/s)`, and it is what step
(iii) actually uses. -/
def IsAdmissible (I : Ideal A) (T : Finset A) (u : A) : Prop :=
  I ≤ (Ideal.span (insert u (T : Set A))).radical

/-- Admissibility, unfolded: `I` lies in the radical of the span of the numerators together
with the denominator. -/
@[simp]
theorem isAdmissible_iff {I : Ideal A} {T : Finset A} {u : A} :
    IsAdmissible I T u ↔ I ≤ (Ideal.span (insert u (T : Set A))).radical := Iff.rfl

/-- **A numerator set containing `1` is admissible for every ideal.** The span is then already
everything, so its radical is `⊤` and the containment defining admissibility is vacuous — for
any `I` and any denominator `u`. This is what discharges admissibility in the `Γ_v = cΓ_v`
branch of 7.5(ii), where Wedhorn's witness `Spv(A,I)((g₁d, …, gₙd, 1)/g₀d)` carries `1` among
its numerators; the cofinal branch instead needs
`isAdmissible_of_forall_exists_pow_mem`. -/
lemma isAdmissible_of_one_mem {I : Ideal A} {T : Finset A} {u : A} (h : (1 : A) ∈ T) :
    IsAdmissible I T u := by
  have hspan : Ideal.span (insert u (T : Set A)) = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span (mem_insert_of_mem _ h))
  simp [hspan, Ideal.radical_top]

/-- If `I` sits inside the radical of a span whose every generator has a power in `T`, then `T`
is admissible for `I`. Only that containment is needed — no auxiliary ideal, and no equality of
spans or radicals. -/
lemma isAdmissible_of_forall_exists_pow_mem {I : Ideal A} {S T : Finset A} {u : A}
    (hI : I ≤ (Ideal.span (S : Set A)).radical)
    (h : ∀ σ ∈ S, ∃ k : ℕ, σ ^ k ∈ T) : IsAdmissible I T u := by
  have hle : Ideal.span (S : Set A) ≤ (Ideal.span (insert u (T : Set A))).radical := by
    rw [Ideal.span_le]
    intro σ hσ
    obtain ⟨k, hk⟩ := h σ hσ
    exact Ideal.mem_radical_iff.mpr ⟨k, Ideal.subset_span (mem_insert_of_mem _ hk)⟩
  calc I ≤ (Ideal.span (S : Set A)).radical := hI
    _ ≤ ((Ideal.span (insert u (T : Set A))).radical).radical := Ideal.radical_mono hle
    _ = (Ideal.span (insert u (T : Set A))).radical := Ideal.radical_idem _

open scoped Classical Pointwise in
/-- **Admissibility is stable under the product of pairs.** The numerator sets multiply
pointwise, each augmented by its own denominator — the same shape `basicOpenFinset_inter`
produces — and the product pair is admissible for the same `I`: the radical of the span of a
product of sets is the meet of the radicals. -/
theorem IsAdmissible.mul {I : Ideal A} {T₁ T₂ : Finset A} {u₁ u₂ : A}
    (h₁ : IsAdmissible I T₁ u₁) (h₂ : IsAdmissible I T₂ u₂) :
    IsAdmissible I (insert u₁ T₁ * insert u₂ T₂) (u₁ * u₂) := by
  rw [isAdmissible_iff, Set.insert_eq_self.mpr (Finset.mem_coe.mpr
      (Finset.mul_mem_mul (Finset.mem_insert_self u₁ T₁) (Finset.mem_insert_self u₂ T₂))),
    Finset.coe_mul, ← Ideal.span_mul_span', Ideal.radical_mul]
  exact le_inf (by simpa using h₁) (by simpa using h₂)

/-! ### Wedhorn 7.5(ii): the rational subsets are a basis -/

/-- **Scaling a denominator into the unit ball.** When `Γ_v = cΓ_v`, an `s` outside the support
has a multiple `d * s` whose value is at least `1` and which is still outside the support. This
is the witness Wedhorn takes at the start of the `Γ_v = cΓ_v` branch of 7.5(ii): full
characteristic group means `(v s)⁻¹` is dominated by an attained value. -/
private theorem exists_vle_one_mul_of_characteristicSubgroup_eq_top {v : Spv A}
    (htop : characteristicSubgroup v.valuation = ⊤) {s : A}
    (hs0 : ¬ v.toValuativeRel.vle s 0) :
    ∃ d : A, v.toValuativeRel.vle 1 (d * s) ∧ ¬ v.toValuativeRel.vle (d * s) 0 := by
  set w := v.valuation with hw
  have hs0' : w s ≠ 0 := fun h ↦
    hs0 ((valuation_le_iff v s 0).mp (by rw [← hw]; simp [h]))
  have hrs : w.restrict s ≠ 0 := fun h ↦ hs0' (w.restrict_eq_zero_iff.mp h)
  obtain ⟨d, _, hd⟩ := hasFullCharacteristicGroup_iff.mp
    (hasFullCharacteristicGroup_iff_characteristicSubgroup_eq_top.mpr htop) _
    (inv_pos.mpr (zero_lt_iff.mpr hrs))
  have hone : (1 : ValueGroup₀ (.ofClass w)) ≤ w.restrict (d * s) := by
    rw [map_mul]
    have h := mul_le_mul_left hd (w.restrict s)
    rwa [inv_mul_cancel₀ hrs] at h
  refine ⟨d, ?_, fun h ↦ ?_⟩
  · rw [← valuation_le_iff]
    exact (Valuation.restrict_le_iff w).mp (by simpa using hone)
  · have hle := (valuation_le_iff v (d * s) 0).mpr h
    rw [← hw, map_zero] at hle
    rw [w.restrict_eq_zero_iff.mpr (le_antisymm hle zero_le)] at hone
    exact absurd hone (by simp)

/-- **Wedhorn 7.5(ii), the branch `Γ_v = cΓ_v`.** A witness `d` with `v(ds) ≥ 1` turns the basic
open `Spv(A)(f/s)` into `Spv(A)({df, 1}/ds)`, whose numerator set contains `1` and is therefore
admissible for every `I`. -/
private theorem exists_basicOpenFinset_of_characteristicSubgroup_eq_top {v : Spv A}
    (htop : characteristicSubgroup v.valuation = ⊤) {f s : A} (hv : v ∈ basicOpen f s) :
    ∃ (T : Finset A) (u : A), (1 : A) ∈ T ∧ v ∈ basicOpenFinset T u ∧
      basicOpenFinset T u ⊆ basicOpen f s := by
  classical
  rw [mem_basicOpen_iff] at hv
  obtain ⟨hfs, hs0⟩ := hv
  obtain ⟨d, hvle_one, hds0⟩ := exists_vle_one_mul_of_characteristicSubgroup_eq_top htop hs0
  have hdfs : v.toValuativeRel.vle (d * f) (d * s) := by
    have h := v.toValuativeRel.mul_vle_mul_left hfs d
    rwa [mul_comm f d, mul_comm s d] at h
  refine ⟨{d * f, 1}, d * s, by simp, (mem_basicOpenFinset_iff _ _ _).mpr ⟨?_, hds0⟩, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hdfs
    · exact hvle_one
  · exact fun x hx ↦ basicOpen_mul_subset d f s
      (basicOpenFinset_subset_basicOpen (by simp) hx)

/-- **Wedhorn 7.5(ii), the cofinal branch.** Cofinality of each generator below `v(s)` supplies
an exponent per generator; adjoining those powers to `{f}` gives an admissible numerator set
inside `Spv(A)(f/s)`. Wedhorn instead takes a single exponent for all generators, which is
equally available here: cofinality already forces each generator's value below `1`
(`cofinalValueFor_top_iff` with `CofinalValueFor.lt_one`), so the largest of the individual
exponents would serve. Nothing downstream needs the exponents to agree, so they are chosen
separately. -/
private theorem exists_basicOpenFinset_of_forall_cofinalValue {v : Spv A} (S : Finset A)
    (hcof : ∀ σ ∈ S, CofinalValue v.valuation σ) {f s : A} (hv : v ∈ basicOpen f s) :
    ∃ T : Finset A, f ∈ T ∧ (∀ σ ∈ S, ∃ k : ℕ, σ ^ k ∈ T) ∧ v ∈ basicOpenFinset T s := by
  classical
  rw [mem_basicOpen_iff] at hv
  obtain ⟨hfs, hs0⟩ := hv
  set w := v.valuation with hw
  have hs0' : w s ≠ 0 := fun h ↦
    hs0 ((valuation_le_iff v s 0).mp (by rw [← hw]; simp [h]))
  have hrs : (0 : ValueGroup₀ (.ofClass w)) < w.restrict s :=
    zero_lt_iff.mpr fun h ↦ hs0' (w.restrict_eq_zero_iff.mp h)
  have key : ∀ σ ∈ S, ∃ n : ℕ, w.restrict σ ^ n < w.restrict s := fun σ hσ ↦
    cofinalValue_iff.mp (hcof σ hσ) _ hrs
  choose n hn using key
  refine ⟨insert f (S.attach.image fun σ ↦ σ.1 ^ n σ.1 σ.2), Finset.mem_insert_self _ _,
    fun σ hσ ↦ ⟨n σ hσ, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨σ, hσ⟩,
      Finset.mem_attach _ _, rfl⟩)⟩, (mem_basicOpenFinset_iff _ _ _).mpr ⟨?_, hs0⟩⟩
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact hfs
  · obtain ⟨⟨σ, hσ⟩, -, rfl⟩ := Finset.mem_image.mp ht
    rw [← valuation_le_iff]
    exact (Valuation.restrict_le_iff w).mp (by rw [map_pow]; exact (hn σ hσ).le)

/-- **Wedhorn 7.5(ii).** Around a point of `Spv (A, I)`, every basic open of `Spv A` contains an
admissible `Spv(A)(T/u)` containing the point. The case split is Lemma 7.4(iii), taken at a
finite generating set of the finitely generated ideal supplied by `hfg`. -/
theorem exists_isAdmissible_basicOpenFinset {I : Ideal A}
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {v : Spv A}
    (hvI : v ∈ spvOfIdeal I hfg) {f s : A} (hv : v ∈ basicOpen f s) :
    ∃ (T : Finset A) (u : A), IsAdmissible I T u ∧ v ∈ basicOpenFinset T u ∧
      basicOpenFinset T u ⊆ basicOpen f s := by
  obtain ⟨J, hJfg, hrad⟩ := hfg
  obtain ⟨S, hS⟩ := hJfg
  have hI : I ≤ (Ideal.span (S : Set A)).radical := by
    rw [hS, ← hrad]; exact Ideal.le_radical
  rcases (characteristicSubgroupOfIdeal_eq_top_iff_forall_span _ hS hrad).mp
      (mem_spvOfIdeal_iff.mp hvI) with hcof | htop
  · obtain ⟨T, hfT, hpow, hvT⟩ :=
      exists_basicOpenFinset_of_forall_cofinalValue S (fun σ hσ ↦ hcof σ hσ) hv
    exact ⟨T, s, isAdmissible_of_forall_exists_pow_mem hI hpow, hvT,
      basicOpenFinset_subset_basicOpen hfT⟩
  · obtain ⟨T, u, h1, hvT, hsub⟩ :=
      exists_basicOpenFinset_of_characteristicSubgroup_eq_top htop hv
    exact ⟨T, u, isAdmissible_of_one_mem h1, hvT, hsub⟩

/-! ### The basis `R` and the topology it generates -/

/-- **Wedhorn's family `R`** for `Spv (A, I)`: the traces of the admissible `Spv(A)(T/u)`.
It generates the subspace topology — see `instTopologicalSpace_spvOfIdeal_eq_generateFrom`. -/
def rationalFamily (I : Ideal A) (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    Set (Set (spvOfIdeal I hfg)) :=
  {U | ∃ (T : Finset A) (u : A), IsAdmissible I T u ∧ U = Subtype.val ⁻¹' basicOpenFinset T u}

/-- Membership in the generating family: a set belongs exactly when it is the trace of some
admissible `Spv(A)(T/u)`. -/
@[simp]
theorem mem_rationalFamily_iff {I : Ideal A} {hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical}
    {U : Set (spvOfIdeal I hfg)} :
    U ∈ rationalFamily I hfg ↔
      ∃ (T : Finset A) (u : A), IsAdmissible I T u ∧
        U = Subtype.val ⁻¹' basicOpenFinset T u := Iff.rfl

/-- **Wedhorn 7.5(1), step (ii)**: the subspace topology of `Spv (A, I)` is generated by the
admissible rational subsets. One direction is that each of them is the trace of an open
of `Spv A`; the other is step (ii), applied to the subbasis of `Spv A`. -/
theorem instTopologicalSpace_spvOfIdeal_eq_generateFrom (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    (inferInstance : TopologicalSpace (spvOfIdeal I hfg))
      = TopologicalSpace.generateFrom (rationalFamily I hfg) := by
  refine le_antisymm (le_generateFrom ?_) ?_
  · rintro _ ⟨T, u, -, rfl⟩
    exact (isOpen_basicOpenFinset T u).preimage continuous_subtype_val
  · -- the subtype instance is by definition the induced topology; naming that as an equation
    -- lets `induced_generateFrom_eq` fire without a goal-shaping tactic
    have hind : (inferInstance : TopologicalSpace (spvOfIdeal I hfg))
        = TopologicalSpace.induced (Subtype.val : spvOfIdeal I hfg → Spv A) inferInstance := rfl
    rw [hind, instTopologicalSpace_eq_generateFrom, induced_generateFrom_eq]
    refine le_generateFrom ?_
    rintro _ ⟨_, ⟨f, s, rfl⟩, rfl⟩
    refine (@isOpen_iff_forall_mem_open _ (generateFrom (rationalFamily I hfg)) _).mpr ?_
    rintro ⟨v, hvI⟩ hv
    obtain ⟨T, u, hadm, hvT, hsub⟩ := exists_isAdmissible_basicOpenFinset hfg hvI hv
    exact ⟨Subtype.val ⁻¹' basicOpenFinset T u, fun _ hw ↦ hsub hw,
      isOpen_generateFrom_of_mem ⟨T, u, hadm, rfl⟩, hvT⟩

/-- **The whole space is a member of `R`**: it is the trace of `Spv(A)({1}/1)`, whose defining
conditions hold at every point and whose numerator set contains `1` and is therefore admissible
for every ideal.

Deliberately not `@[simp]`: family membership already has a simp normal form through
`mem_rationalFamily_iff`, which rewrites this left-hand side first, so the tag would be dead
weight — and `simpNF` rejects it. -/
theorem univ_mem_rationalFamily (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    Set.univ ∈ rationalFamily I hfg :=
  ⟨{1}, 1, isAdmissible_of_one_mem (Finset.mem_singleton_self 1), by
    rw [basicOpenFinset_eq_biInter]
    simp⟩

/-- **Wedhorn's step (i) in the proof of Lemma 7.5, on `Spv (A, I)`**: the family `R` is stable
under intersection. The traces intersect along the trace of the intersection, which
`basicOpenFinset_inter` computes as another rational subset, and `IsAdmissible.mul` keeps its
pair admissible. -/
theorem inter_mem_rationalFamily {I : Ideal A}
    {hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical} {U V : Set (spvOfIdeal I hfg)}
    (hU : U ∈ rationalFamily I hfg) (hV : V ∈ rationalFamily I hfg) :
    U ∩ V ∈ rationalFamily I hfg := by
  obtain ⟨T₁, u₁, hadm₁, rfl⟩ := hU
  obtain ⟨T₂, u₂, hadm₂, rfl⟩ := hV
  exact ⟨_, _, IsAdmissible.mul hadm₁ hadm₂,
    by rw [← Set.preimage_inter, basicOpenFinset_inter]⟩

/-- **The basis half of Wedhorn Lemma 7.5(1)**: the family `R` is a topological basis of
`Spv (A, I)`, not merely a generating family. Generation is
`instTopologicalSpace_spvOfIdeal_eq_generateFrom`; this upgrades it with the two closure
properties a basis needs, `univ_mem_rationalFamily` and `inter_mem_rationalFamily`. Together
with `isCompact_of_mem_rationalFamily` below, this is Wedhorn's full claim: a basis of
quasi-compact opens. -/
theorem isTopologicalBasis_rationalFamily (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    IsTopologicalBasis (rationalFamily I hfg) :=
  isTopologicalBasis_of_subbasis_of_finiteInter
    (instTopologicalSpace_spvOfIdeal_eq_generateFrom I hfg)
    ⟨univ_mem_rationalFamily I hfg, fun _ hU _ hV ↦ inter_mem_rationalFamily hU hV⟩

/-! ### The compact witness topology -/

/-- `r_I` is surjective: it fixes `Spv (A, I)` pointwise. -/
private lemma restrictToIdealCodRestrict_surjective (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    Function.Surjective (restrictToIdealCodRestrict I hfg) :=
  fun v ↦ ⟨(v : Spv A), restrictToIdealCodRestrict_coe I hfg v⟩

/-- **The compact witness topology on `Spv (A, I)`**, coinduced along `r_I` from the patch
topology of `Spv A`. It is a proof device for the patch criterion, deliberately not an
instance: the topology of `Spv (A, I)` is the subspace one. -/
@[instance_reducible]
private noncomputable def patchTopologyOfIdeal (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    TopologicalSpace (spvOfIdeal I hfg) :=
  TopologicalSpace.coinduced (restrictToIdealCodRestrict I hfg) (patchTopology A)

/-- The defining equation of the witness topology. -/
private lemma patchTopologyOfIdeal_eq (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    patchTopologyOfIdeal I hfg =
      TopologicalSpace.coinduced (restrictToIdealCodRestrict I hfg) (patchTopology A) := rfl

/-- **The witness topology is compact** — Wedhorn's step (iv): the continuous image of the
compact `(Spv A)_cons` under the surjection `r_I`. -/
private lemma compactSpace_patchTopologyOfIdeal (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    @CompactSpace _ (patchTopologyOfIdeal I hfg) := by
  exact @Function.Surjective.compactSpace _ _ (patchTopology A) (patchTopologyOfIdeal I hfg) _
    (by rw [patchTopologyOfIdeal_eq]; exact continuous_coinduced_rng) compactSpace_patchTopology
    (restrictToIdealCodRestrict_surjective I hfg)

/-- A set is clopen for the witness topology as soon as its `r_I`-preimage is patch-clopen in
`Spv A`; that is what a coinduced topology means. -/
private lemma isClopen_patchTopologyOfIdeal_of_preimage (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {V : Set (spvOfIdeal I hfg)}
    (h : @IsClopen (Spv A) (patchTopology A) (restrictToIdealCodRestrict I hfg ⁻¹' V)) :
    @IsClopen _ (patchTopologyOfIdeal I hfg) V := by
  rw [patchTopologyOfIdeal_eq]
  refine ⟨?_, (@isOpen_coinduced _ _ (patchTopology A) _ _).2 h.2⟩
  rw [← @isOpen_compl_iff _ _ (TopologicalSpace.coinduced _ (patchTopology A))]
  exact (@isOpen_coinduced _ _ (patchTopology A) _ _).2
    (by rw [Set.preimage_compl]; exact h.1.isOpen_compl)

/-! ### Wedhorn 7.5(iii) -/

/-- A value the restriction keeps lies outside the support, since the restriction vanishes
wherever `v` does. -/
private theorem not_vle_zero_of_restrictToIdeal_ne_zero {w : Spv A} (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {u : A}
    (hu : w.valuation.restrictToIdeal I hfg u ≠ 0) : ¬ w.toValuativeRel.vle u 0 := by
  intro h
  refine hu (Valuation.restrictToIdeal_apply_of_eq_zero w.valuation I hfg ?_)
  have hle := (valuation_le_iff w u 0).mpr h
  rw [map_zero] at hle
  exact le_antisymm hle zero_le

/-- **Wedhorn 7.5(iii)**: `r_I⁻¹(Spv(A,I)(T/u)) = Spv(A)(T/u)` for admissible `(T, u)`.

The inclusion `⊆` is Wedhorn's remark that a point of the preimage is a horizontal generization
of its image, which here is the monotonicity `restrictToIdeal_ne_zero_of_le`. The inclusion `⊇`
is his contradiction argument, `restrictToIdeal_ne_zero_of_isAdmissible`. -/
theorem restrictToIdealCodRestrict_preimage (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {T : Finset A} {u : A}
    (hadm : IsAdmissible I T u) :
    restrictToIdealCodRestrict I hfg ⁻¹' (Subtype.val ⁻¹' basicOpenFinset T u)
      = basicOpenFinset T u := by
  ext w
  simp only [Set.mem_preimage, coe_restrictToIdealCodRestrict, mem_basicOpenFinset_iff,
    vle_restrictToIdeal, map_zero, ne_eq, not_true_eq_false, false_and, or_false]
  constructor
  · rintro ⟨hT, hu⟩
    have hu0 := not_vle_zero_of_restrictToIdeal_ne_zero I hfg hu
    refine ⟨fun t ht ↦ ?_, hu0⟩
    rcases hT t ht with h | ⟨-, h⟩
    · by_contra hlt
      exact restrictToIdeal_ne_zero_of_le _ I hfg hu ((valuation_lt_iff w u t).mpr hlt).le h
    · exact h
  · rintro ⟨hT, hu0⟩
    have hu : w.valuation.restrictToIdeal I hfg u ≠ 0 :=
      restrictToIdeal_ne_zero_of_isAdmissible w.valuation I hfg hadm
        (fun h ↦ hu0 ((valuation_le_iff w u 0).mp (by simp [h])))
        (fun t ht ↦ (valuation_le_iff w t u).mpr (hT t ht))
    exact ⟨fun t ht ↦ Or.inr ⟨hu, hT t ht⟩, hu⟩

/-! ### Wedhorn Lemma 7.5(1) -/

/-- Every member of `R` is clopen for the witness topology: step (iii) computes its `r_I`-preimage
to be `Spv(A)(T/u)`, which is patch-clopen in `Spv A`. -/
private lemma isClopen_patchTopologyOfIdeal_of_mem_rationalFamily (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    ∀ V ∈ rationalFamily I hfg, @IsClopen _ (patchTopologyOfIdeal I hfg) V := by
  rintro _ ⟨T, u, hadm, rfl⟩
  exact isClopen_patchTopologyOfIdeal_of_preimage I hfg
    (by rw [restrictToIdealCodRestrict_preimage I hfg hadm]
        exact isClopen_patchTopology_basicOpenFinset T u)

/-- **Wedhorn, Lemma 7.5(1)**: `Spv (A, I)` is a spectral space.

The patch criterion is applied with the subspace topology as the generated one — the admissible
rational subsets generate it by `instTopologicalSpace_spvOfIdeal_eq_generateFrom` — and with the
coinduced `patchTopologyOfIdeal` as the compact witness, in which those subsets are clopen by
step (iii). `T0Space` comes from `Spv A` through the subtype instance. -/
theorem spectralSpace_spvOfIdeal (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    SpectralSpace (spvOfIdeal I hfg) :=
  spectralSpace_of_isClopen_generateFrom (instTopologicalSpace_spvOfIdeal_eq_generateFrom I hfg)
    (compactSpace_patchTopologyOfIdeal I hfg)
    (isClopen_patchTopologyOfIdeal_of_mem_rationalFamily I hfg)

/-- **Wedhorn Lemma 7.5(1), the quasi-compactness half.** Every member of `R` is a quasi-compact
open of `Spv (A, I)` — the property Wedhorn states alongside "basis", and the one that
quasi-compactness in `Spv A` does *not* supply, since `Spv (A, I)` is not closed there.

Same witness topology as the spectrality proof, so the patch criterion's
`isCompact_of_isClopen_generateFrom` applies directly. -/
theorem isCompact_of_mem_rationalFamily (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {V : Set (spvOfIdeal I hfg)}
    (hV : V ∈ rationalFamily I hfg) : IsCompact V :=
  isCompact_of_isClopen_generateFrom (t' := patchTopologyOfIdeal I hfg)
    (instTopologicalSpace_spvOfIdeal_eq_generateFrom I hfg)
    (compactSpace_patchTopologyOfIdeal I hfg)
    (isClopen_patchTopologyOfIdeal_of_mem_rationalFamily I hfg) hV

/-! ### Wedhorn Lemma 7.5(2) -/

/-- **Wedhorn Lemma 7.5(2)**, the continuity half: the retraction `r_I : Spv A → Spv (A, I)`
is continuous.

The spectral-map half is `isSpectralMap_restrictToIdealCodRestrict` below. -/
@[fun_prop]
theorem continuous_restrictToIdealCodRestrict (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    Continuous (restrictToIdealCodRestrict I hfg) := by
  have h : Continuous[_, generateFrom (rationalFamily I hfg)]
      (restrictToIdealCodRestrict I hfg) := by
    refine continuous_generateFrom_iff.mpr ?_
    rintro _ ⟨T, u, hadm, rfl⟩
    rw [restrictToIdealCodRestrict_preimage I hfg hadm]
    exact isOpen_basicOpenFinset T u
  rwa [← instTopologicalSpace_spvOfIdeal_eq_generateFrom I hfg] at h

/-- **Wedhorn Lemma 7.5(2)**, the spectral-map half: the retraction `r_I : Spv A → Spv (A, I)`
is a spectral map. This closes out Lemma 7.5.

Spectrality is tested on the basis `R` (`isSpectralMap_of_isTopologicalBasis` with
`isTopologicalBasis_rationalFamily`), where the preimage of a rational subset is computed by
step (iii) and is quasi-compact in `Spv A` unconditionally. -/
theorem isSpectralMap_restrictToIdealCodRestrict (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    IsSpectralMap (restrictToIdealCodRestrict I hfg) := by
  refine isSpectralMap_of_isTopologicalBasis (isTopologicalBasis_rationalFamily I hfg)
    (continuous_restrictToIdealCodRestrict I hfg) ?_
  rintro _ ⟨T, u, hadm, rfl⟩
  rw [restrictToIdealCodRestrict_preimage I hfg hadm]
  exact isCompact_basicOpenFinset T u

/-! ### The sub-unit locus is pro-constructible in `Spv (A, I)` -/

/-- **The locus `v ≤ 1` on a set of ring elements is pro-constructible in `Spv (A, I)`.** Its
trace is the intersection over `a ∈ S` of the rational subsets `Spv(A,I)({a,1}/1)`, each a
quasi-compact open of the subspace by `isCompact_of_mem_rationalFamily` — carrying `1` among
the numerators makes the pair admissible for any `I` (`isAdmissible_of_one_mem`).

This is the form Wedhorn's Theorem 7.35 consumes at `S = A⁺`. It does not follow from the
corresponding `Spv A` statement by restriction — the inclusion `Spv (A, I) → Spv A` is not
spectral — which is why it is proved here from the rational family instead. -/
theorem isProConstructible_val_preimage_setOfPred_forall_vle_one (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) (S : Set A) :
    IsProConstructible (Subtype.val ⁻¹' {v : Spv A | ∀ a ∈ S, v.toValuativeRel.vle a 1} :
      Set (spvOfIdeal I hfg)) := by
  classical
  have hsingle : ∀ a : A, basicOpenFinset ({a, 1} : Finset A) 1 = basicOpen a 1 := fun a ↦ by
    rw [basicOpenFinset_eq_biInter]
    simp
  have h : (Subtype.val ⁻¹' {v : Spv A | ∀ a ∈ S, v.toValuativeRel.vle a 1} :
      Set (spvOfIdeal I hfg)) = ⋂ a ∈ S, Subtype.val ⁻¹' basicOpenFinset {a, 1} 1 := by
    ext w
    simp [hsingle]
  rw [h]
  exact IsProConstructible.biInter fun a _ ↦ IsCompact.isProConstructible
    (isCompact_of_mem_rationalFamily I hfg ⟨{a, 1}, 1, isAdmissible_of_one_mem (by simp), rfl⟩)
    ((isOpen_basicOpenFinset _ _).preimage continuous_subtype_val)

end TauCeti.ValuationSpectrum
