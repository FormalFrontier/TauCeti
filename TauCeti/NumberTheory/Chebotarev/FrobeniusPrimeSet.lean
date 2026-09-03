/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.RamifiedPrimes
public import TauCeti.NumberTheory.NumberField.ArtinSymbol
import TauCeti.NumberTheory.NumberField.AlgEquiv

/-!
# The unramified primes carrying a prescribed Artin class

Let `L / K` be a finite Galois extension of number fields and let `C` be a conjugacy class in
`Gal(L/K)`. This file defines the set

`frobeniusPrimeSet K L C : Set (HeightOneSpectrum (𝓞 K))`

of height-one primes `𝔭` of `𝓞 K` that are unramified in `L` and whose Artin class is `C`. It is
the set whose density the Chebotarev density theorem computes.

## The dependent membership condition

`artinSymbol` is a *partial* construction: it takes an unramifiedness proof as an argument and has
no value at a ramified prime. So membership cannot be an equation between two total functions;
it is stated as

`∃ hur : (𝔭 is unramified in L), artinSymbol 𝔭.asIdeal hur = C`,

an existential over a proof. Membership is nonetheless unambiguous: it does not depend on which
unramifiedness proof witnesses it, and `mem_frobeniusPrimeSet_iff_artinSymbol_eq` turns the
existential into the plain equation `artinSymbol 𝔭.asIdeal hur = C` for whichever unramifiedness
proof `hur` the caller has in hand.

The alternative — a total `Gal(L/K)`-valued or `ConjClasses`-valued function taking a junk value
at the ramified primes — is worse for this set: the junk value carries no arithmetic content, yet
the ramified primes would sit inside the fibre of whichever class it names, so the fibres would
neither cover the unramified primes exactly nor be pinned down by a Frobenius element there. The
existential is what keeps the fibres free of them.

## Main definitions

* `NumberField.Chebotarev.frobeniusPrimeSet`: the primes of `𝓞 K` unramified in `L` whose Artin
  class is `C`.

## Main results

* `NumberField.Chebotarev.mem_frobeniusPrimeSet_iff_artinSymbol_eq`: proof-independence — with
  any unramifiedness proof in hand, membership is the equation `artinSymbol 𝔭.asIdeal hur = C`.
* `NumberField.Chebotarev.mem_frobeniusPrimeSet_mk_iff_exists_isArithFrobAt`: for an unramified
  `𝔭` and an element `σ`, membership in the fibre of `[σ]` says exactly that `σ` is an arithmetic
  Frobenius at *some* prime of `𝓞 L` above `𝔭`.
* `NumberField.Chebotarev.frobeniusPrimeSet_map_autCongr`: equivariance — an isomorphism
  `e : L ≃ₐ[K] L'` of extensions of `K` matches the fibre of `C` in `L` with the fibre in `L'` of
  the image of `C` under the induced isomorphism `AlgEquiv.autCongr e` of Galois groups.
* `NumberField.Chebotarev.disjoint_frobeniusPrimeSet`: distinct classes have disjoint fibres.
* `NumberField.Chebotarev.iUnion_frobeniusPrimeSet`: the fibres cover exactly the complement of
  `ramifiedPrimes K L`, so `existsUnique_mem_frobeniusPrimeSet` partitions the unramified primes
  and `finite_compl_iUnion_frobeniusPrimeSet` records that the discarded remainder is finite.

The last two are what let the density arguments discard a finite exceptional set and then work
one class at a time: a lower density bound for each class can be squeezed against a partition of
a cofinite set, which is how the crossing argument produces exact densities.
-/

public section

open Ideal
open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

variable (K L) in
/-- **The primes of `K` with Artin class `C` in `L`.** A height-one prime `𝔭` of `𝓞 K` belongs to
`frobeniusPrimeSet K L C` when `𝔭` is unramified in `L` — so that `artinSymbol` is applicable —
and its Artin class is `C`.

The unramifiedness proof is packaged existentially rather than assumed, because `artinSymbol`
takes it as an argument and no value is assigned at a ramified prime. See
`mem_frobeniusPrimeSet_iff_artinSymbol_eq` for the form used once such a proof is available.

The carrier and this membership condition are taken from
`TauCetiRoadmap/Chebotarev/Suggested.lean`, lines 64–76, described in the section
`Frobenius prime sets and finite exceptional sets` of `TauCetiRoadmap/Chebotarev/README.md`. -/
def frobeniusPrimeSet (C : ConjClasses (L ≃ₐ[K] L)) : Set (HeightOneSpectrum (𝓞 K)) :=
  {𝔭 | ∃ hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
    Algebra.IsUnramifiedAt (𝓞 K) Q, artinSymbol 𝔭.asIdeal hur = C}

/-- Membership in `frobeniusPrimeSet`, unfolded. Downstream files should open the definition
through this lemma rather than through defeq. -/
@[simp]
theorem mem_frobeniusPrimeSet_iff {𝔭 : HeightOneSpectrum (𝓞 K)}
    {C : ConjClasses (L ≃ₐ[K] L)} :
    𝔭 ∈ frobeniusPrimeSet K L C ↔
      ∃ hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
        Algebra.IsUnramifiedAt (𝓞 K) Q, artinSymbol 𝔭.asIdeal hur = C :=
  Iff.rfl

/-- **Proof-independence.** Once an unramifiedness proof `hur` is available, membership in
`frobeniusPrimeSet K L C` is the plain equation `artinSymbol 𝔭.asIdeal hur = C`: the existential
in the definition may be instantiated at `hur`, whatever proof it was introduced with.

Membership in `frobeniusPrimeSet K L C` is therefore independent of the unramifiedness proof used
to test it. -/
theorem mem_frobeniusPrimeSet_iff_artinSymbol_eq {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) (C : ConjClasses (L ≃ₐ[K] L)) :
    𝔭 ∈ frobeniusPrimeSet K L C ↔ artinSymbol 𝔭.asIdeal hur = C :=
  ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hur, h⟩⟩

/-- An unramified prime lies in the fibre of its own Artin class. -/
theorem mem_frobeniusPrimeSet_artinSymbol {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    𝔭 ∈ frobeniusPrimeSet K L (artinSymbol 𝔭.asIdeal hur) :=
  ⟨hur, rfl⟩

/-- A member of `frobeniusPrimeSet K L C` is unramified in `L`. -/
theorem isUnramifiedAt_of_mem_frobeniusPrimeSet {𝔭 : HeightOneSpectrum (𝓞 K)}
    {C : ConjClasses (L ≃ₐ[K] L)} (h : 𝔭 ∈ frobeniusPrimeSet K L C)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 K) Q :=
  (mem_frobeniusPrimeSet_iff.mp h).elim fun hur _ ↦ hur Q

/-- No ramified prime carries an Artin class: the fibres avoid `ramifiedPrimes K L`. -/
theorem frobeniusPrimeSet_subset_compl_ramifiedPrimes (C : ConjClasses (L ≃ₐ[K] L)) :
    frobeniusPrimeSet K L C ⊆ (↑(ramifiedPrimes K L))ᶜ := fun 𝔭 h hmem ↦
  (mem_ramifiedPrimes_iff 𝔭).mp (Finset.mem_coe.mp hmem) fun Q _ _ ↦
    isUnramifiedAt_of_mem_frobeniusPrimeSet h Q

/-- **A Frobenius witnesses membership.** If `σ` is an arithmetic Frobenius at a prime `Q` of
`𝓞 L` above an unramified `𝔭`, then `𝔭` lies in the fibre of the class of `σ`. -/
theorem mem_frobeniusPrimeSet_mk_of_isArithFrobAt {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    𝔭 ∈ frobeniusPrimeSet K L (ConjClasses.mk σ) :=
  ⟨hur, artinSymbol_eq_mk_of_isArithFrobAt 𝔭.asIdeal hur Q σ hσ⟩

/-- **Every representative is realized.** If `𝔭` lies in the fibre of the class of `σ`, then `σ`
itself — not merely some conjugate of it — is an arithmetic Frobenius at some prime of `𝓞 L`
above `𝔭`. -/
theorem exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk {𝔭 : HeightOneSpectrum (𝓞 K)}
    {σ : L ≃ₐ[K] L} (h : 𝔭 ∈ frobeniusPrimeSet K L (ConjClasses.mk σ)) :
    ∃ Q : 𝔭.asIdeal.primesOver (𝓞 L), IsArithFrobAt (𝓞 K) σ Q.1 := by
  obtain ⟨hur, hC⟩ := mem_frobeniusPrimeSet_iff.mp h
  exact exists_isArithFrobAt_of_artinSymbol_eq_mk 𝔭.asIdeal hur hC

/-- **The fibre of a class, read off from any one representative.** For `𝔭` unramified in `L`,
membership in the fibre of `[σ]` says exactly that `σ` is an arithmetic Frobenius at some prime
of `𝓞 L` above `𝔭`. -/
theorem mem_frobeniusPrimeSet_mk_iff_exists_isArithFrobAt {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) (σ : L ≃ₐ[K] L) :
    𝔭 ∈ frobeniusPrimeSet K L (ConjClasses.mk σ) ↔
      ∃ Q : 𝔭.asIdeal.primesOver (𝓞 L), IsArithFrobAt (𝓞 K) σ Q.1 :=
  ⟨exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk, fun ⟨Q, hσ⟩ ↦
    mem_frobeniusPrimeSet_mk_of_isArithFrobAt hur Q.1 hσ⟩

section IsoOfExtensions

variable {L' : Type*} [Field L'] [NumberField L'] [Algebra K L'] [IsGalois K L']

/-- **Equivariance under an isomorphism of extensions.** An isomorphism `e : L ≃ₐ[K] L'` carries
the fibre of `C` over `L` onto the fibre over `L'` of the image of `C` under the induced
isomorphism `AlgEquiv.autCongr e` of Galois groups.

So the fibres depend only on the extension `L / K` up to isomorphism, not on the model of `L`
chosen to compute the Artin symbol. -/
theorem frobeniusPrimeSet_map_autCongr (C : ConjClasses (L ≃ₐ[K] L)) (e : L ≃ₐ[K] L') :
    frobeniusPrimeSet K L' (ConjClasses.map (AlgEquiv.autCongr e).toMonoidHom C) =
      frobeniusPrimeSet K L C := by
  -- The two induced maps on conjugacy classes are inverse to one another.
  have hcomp : ∀ D : ConjClasses (L ≃ₐ[K] L),
      ConjClasses.map (AlgEquiv.autCongr e.symm).toMonoidHom
        (ConjClasses.map (AlgEquiv.autCongr e).toMonoidHom D) = D := by
    intro D
    obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective D
    refine congrArg ConjClasses.mk ?_
    rw [← AlgEquiv.autCongr_symm]
    exact (AlgEquiv.autCongr e).symm_apply_apply σ
  ext 𝔭
  simp only [mem_frobeniusPrimeSet_iff]
  constructor
  · rintro ⟨hur', hC⟩
    have hur := (e.forall_isUnramifiedAt_iff 𝔭.asIdeal).mpr hur'
    exact ⟨hur, by rw [artinSymbol_eq_map_autCongr 𝔭.asIdeal e.symm hur' hur, hC, hcomp]⟩
  · rintro ⟨hur, hC⟩
    have hur' := (e.forall_isUnramifiedAt_iff 𝔭.asIdeal).mp hur
    exact ⟨hur', by rw [artinSymbol_eq_map_autCongr 𝔭.asIdeal e hur hur', hC]⟩

end IsoOfExtensions

/-- **Distinct classes have disjoint fibres.** A prime unramified in `L` has one Artin class. -/
theorem disjoint_frobeniusPrimeSet {C D : ConjClasses (L ≃ₐ[K] L)} (h : C ≠ D) :
    Disjoint (frobeniusPrimeSet K L C) (frobeniusPrimeSet K L D) := by
  rw [Set.disjoint_left]
  intro 𝔭 h𝔭C h𝔭D
  obtain ⟨hur, hC⟩ := mem_frobeniusPrimeSet_iff.mp h𝔭C
  exact h (hC.symm.trans ((mem_frobeniusPrimeSet_iff_artinSymbol_eq hur D).mp h𝔭D))

variable (K L) in
/-- The fibres of the Artin class are pairwise disjoint. -/
theorem pairwise_disjoint_frobeniusPrimeSet :
    Pairwise (Function.onFun Disjoint (frobeniusPrimeSet K L)) :=
  fun _ _ h ↦ disjoint_frobeniusPrimeSet h

variable (K L) in
/-- **The fibres cover the unramified primes.** The union of the Artin fibres over all conjugacy
classes of `Gal(L/K)` is exactly the complement of the finite set `ramifiedPrimes K L`.

Together with `disjoint_frobeniusPrimeSet` this is the partition that the density arguments run
on: everything outside a finite exceptional set is accounted for exactly once. -/
@[simp]
theorem iUnion_frobeniusPrimeSet :
    ⋃ C : ConjClasses (L ≃ₐ[K] L), frobeniusPrimeSet K L C = (↑(ramifiedPrimes K L))ᶜ := by
  refine Set.Subset.antisymm (Set.iUnion_subset frobeniusPrimeSet_subset_compl_ramifiedPrimes)
    fun 𝔭 h𝔭 ↦ ?_
  rw [Set.mem_compl_iff, Finset.mem_coe, mem_ramifiedPrimes_iff, not_not] at h𝔭
  exact Set.mem_iUnion.mpr ⟨_, mem_frobeniusPrimeSet_artinSymbol h𝔭⟩

/-- **The Artin class partitions the unramified primes.** A prime of `𝓞 K` outside
`ramifiedPrimes K L` lies in the fibre of exactly one conjugacy class of `Gal(L/K)`. -/
theorem existsUnique_mem_frobeniusPrimeSet {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h𝔭 : 𝔭 ∉ ramifiedPrimes K L) :
    ∃! C : ConjClasses (L ≃ₐ[K] L), 𝔭 ∈ frobeniusPrimeSet K L C := by
  obtain ⟨C, hC⟩ := Set.mem_iUnion.mp
    ((iUnion_frobeniusPrimeSet K L).symm.subset (by simpa using h𝔭))
  exact ⟨C, hC, fun D hD ↦ by
    by_contra hne
    exact Set.disjoint_left.mp (disjoint_frobeniusPrimeSet hne) hD hC⟩

variable (K L) in
/-- **The uncovered set is finite.** Only finitely many primes of `𝓞 K` fail to lie in some Artin
fibre, so a density statement may discard them. -/
theorem finite_compl_iUnion_frobeniusPrimeSet :
    (⋃ C : ConjClasses (L ≃ₐ[K] L), frobeniusPrimeSet K L C)ᶜ.Finite := by
  rw [iUnion_frobeniusPrimeSet, compl_compl]
  exact (ramifiedPrimes K L).finite_toSet

end NumberField.Chebotarev
