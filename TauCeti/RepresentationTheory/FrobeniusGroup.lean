/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Mathlib.Analysis.Complex.Polynomial.Basic` supplies the `IsAlgClosed ℂ` instance that the
-- exceptional-character correspondence asks for.
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.GroupTheory.FrobeniusKernel
public import TauCeti.RepresentationTheory.CharacterTable.Completeness
public import TauCeti.RepresentationTheory.CharacterTable.Kernel
public import TauCeti.RepresentationTheory.Induction.ExceptionalCharacter

/-!
# Frobenius's theorem: the Frobenius kernel is a normal subgroup

Let `H` be a trivial-intersection subgroup of a finite group `G` (`TauCeti.IsTISubgroup`), as a
Frobenius complement is.  The **Frobenius kernel** `TauCeti.frobeniusKernel H` — the identity
together with the elements of `G` lying in no conjugate of `H` — is available as a *set* for any
`H`, and for a trivial-intersection `H` it is already known to have `|G : H|` elements
(`TauCeti.IsTISubgroup.ncard_frobeniusKernel`) and to meet each conjugate of `H` only in the
identity.  What is *not* elementary, and is proved here, is that it is a **subgroup**: closure
under multiplication is Frobenius's theorem, and no proof avoiding character theory is known.

This file supplies the character theory.  Over `ℂ`, induction from a trivial-intersection subgroup
is an isometry on the class functions vanishing at the identity, and the correction
`φ* = Ind_H^G (φ - φ(1) · 1_H) + φ(1) · 1_G` turns an irreducible character of `H` into an
irreducible character of `G` restricting back to `φ`
(`TauCeti.ClassFunction.indExtend_mem_irreducibleCharacters`, the exceptional-character
correspondence).  Choosing a representation `σ_φ` affording each `φ*`, the **common kernel**
`N = ⨅_φ ker σ_φ` is a normal subgroup, and it *is* the Frobenius kernel:

* a *nonidentity* element `g` of the Frobenius kernel lies in no conjugate of `H`, so every summand
  of the induced class function vanishes at `g` and `φ*(g) = φ(1) = φ*(1)` — that is, `g ∈ N`; the
  identity, the one other element of the kernel, lies in `N` outright;
* conversely `N` is normal and `N ∩ H = 1`, because `Res_H φ* = φ` means an element of `N ∩ H`
  has the same value as the identity under every irreducible character of `H`, and the irreducible
  characters of a finite group detect the identity; so a nonidentity element of `N` can lie in no
  conjugate of `H`.

Both inclusions are equalities of *sets*, so the Frobenius kernel inherits the subgroup structure
of `N`.  The bundled subgroup is `TauCeti.frobeniusKernelSubgroup`, and with the counting already
available it is a complement to `H`, so `G` is the semidirect product of the kernel by the
complement.

## Main statements

* `TauCeti.frobeniusKernelSubgroup`: **Frobenius's theorem** — the Frobenius kernel, bundled as a
  subgroup, with `TauCeti.coe_frobeniusKernelSubgroup` and `TauCeti.mem_frobeniusKernelSubgroup`
  its carrier and membership, and `TauCeti.frobeniusKernelSubgroup_normal` its normality.
* `TauCeti.frobeniusKernel_isComplement'`: the kernel is a **complement** to `H`, so `G = N ⋊ H`.
* `TauCeti.frobeniusKernelSubgroup_ne_bot` and `TauCeti.frobeniusKernelSubgroup_ne_top`: when `H`
  is proper the kernel is nontrivial, and when `H` is nontrivial the kernel is proper — so for a
  Frobenius complement (`TauCeti.IsFrobeniusComplement`, which is both) the kernel is a **proper
  nontrivial** normal subgroup.

## Implementation notes

Everything here needs only `TauCeti.IsTISubgroup H`, not the full
`TauCeti.IsFrobeniusComplement H`: properness and nontriviality of `H` play no part in the
character argument, and the degenerate cases are true as stated (`frobeniusKernel ⊤ = {1}` is the
carrier of `⊥`, and `frobeniusKernel ⊥ = Set.univ` that of `⊤`).  They are exactly what makes the
kernel itself nontrivial and proper, so the last two statements take `H ≠ ⊤` and `H ≠ ⊥` as plain
hypotheses.

The bundled subgroup is read off a private existence statement with `Exists.choose`.  That keeps
the choice of affording representations — which is genuinely arbitrary — inside a single proof,
rather than spread over an auxiliary definition whose `Invertible (Nat.card G : ℂ)` instance would
then have to be produced identically at every use site.  Nothing downstream depends on which
subgroup the choice returns: `TauCeti.coe_frobeniusKernelSubgroup` pins its carrier, and a subgroup
is determined by its carrier.

The separation input — that a nonidentity element of a finite group is moved by some irreducible
character — is the private `TauCeti.eq_one_of_forall_irreducibleCharacter_eq` below.  It is the
completeness theorem `TauCeti.ClassFunction.le_span_irreducibleCharacters` applied to the indicator
class function of the identity class, which is `1` at the identity and `0` elsewhere.

## References

* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 7, Theorem 7.2.
* J.-P. Serre, *Linear Representations of Finite Groups*, Section 7.2.
* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 8 (`frobeniusKernelSubgroup`, `coe_frobeniusKernelSubgroup`,
  `frobeniusKernelSubgroup_normal`, `frobeniusKernel_isComplement'`).
-/

public section

namespace TauCeti

open ClassFunction

universe u v

/-! ### The irreducible characters detect the identity -/

/-- **A nonidentity element of a finite group is moved by some irreducible character.**

The irreducible characters span the class functions, so if they all take at `g` the value they take
at the identity, then so does every class function; the indicator of the identity conjugacy class
does not, unless `g = 1`. -/
private theorem eq_one_of_forall_irreducibleCharacter_eq (k : Type u) {G : Type v} [Field k]
    [Group G] [Finite G] [IsAlgClosed k] [Invertible (Nat.card G : k)] {g : G}
    (hg : ∀ f ∈ irreducibleCharacters k G, f g = f 1) : g = 1 := by
  classical
  by_contra hne
  -- the functions taking the same value at `g` and at `1` form a submodule containing every
  -- irreducible character, hence the whole span, hence every class function
  set E : Submodule k (G → k) := LinearMap.ker
    (LinearMap.proj (R := k) (φ := fun _ : G => k) g -
      LinearMap.proj (R := k) (φ := fun _ : G => k) (1 : G)) with hE
  have hsub : Submodule.span k
      {f : G → k | ∃ (n : ℕ) (ρ : Representation k G (Fin n → k)), ρ.IsIrreducible ∧
        ρ.character = f} ≤ E := by
    refine Submodule.span_le.mpr fun f hf => ?_
    simp only [hE, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.proj_apply,
      sub_eq_zero]
    exact hg f (mem_irreducibleCharacters_iff.mpr hf)
  have hmem : ((classIndicator (k := k) (1 : G) : ClassFunction k G) : G → k) ∈ E :=
    hsub (ClassFunction.le_span_irreducibleCharacters k G (classIndicator (k := k) (1 : G)).2)
  -- but the indicator of the identity class does distinguish `g` from the identity
  have hmk : ConjClasses.mk g ≠ ConjClasses.mk (1 : G) :=
    fun h => hne (isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h))
  simp only [hE, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.proj_apply, sub_eq_zero] at hmem
  simp [classIndicator_apply, hmk] at hmem

/-! ### Frobenius's theorem -/

variable {G : Type u} [Group G] [Finite G] {H : Subgroup G}

/-- **Frobenius's theorem.**  For a trivial-intersection subgroup `H` of a finite group `G` — a
Frobenius complement, in the nondegenerate case — the Frobenius kernel is the carrier of a normal
subgroup of `G`.

The proof is the exceptional-character correspondence.  Each irreducible character `φ` of `H`
extends to an irreducible character `φ*` of `G` with `φ*(1) = φ(1)` and `Res_H φ* = φ`; choose a
representation `σ_φ` affording `φ*` and let `N` be the common kernel of the `σ_φ`, a normal
subgroup.  A *nonidentity* element of the Frobenius kernel lies in no conjugate of `H`, so every
summand of the induced class function `Ind_H^G (φ - φ(1) · 1_H)` vanishes there and `φ*` takes its
value at the identity, while the identity lies in `N` outright: the Frobenius kernel is contained
in `N`.  Conversely a nonidentity element of `N` lying in a conjugate of `H` may be conjugated into
`H` — `N` being normal — where `Res_H φ* = φ` makes every irreducible character of `H` take its
identity value, forcing it to *be* the identity.

The two inclusions are of sets, so the Frobenius kernel is the carrier of `N`.  This is the
implementation step behind `TauCeti.frobeniusKernelSubgroup`; the statement to use is that
subgroup together with `TauCeti.coe_frobeniusKernelSubgroup` and
`TauCeti.frobeniusKernelSubgroup_normal`. -/
private theorem exists_normal_coe_eq_frobeniusKernel (hH : IsTISubgroup H) :
    ∃ N : Subgroup G, N.Normal ∧ (N : Set G) = frobeniusKernel H := by
  classical
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- the irreducible characters of `H`, as class functions
  set φ : Fin (Nat.card (ConjClasses H)) → ClassFunction ℂ H :=
    fun j => ofCharacter (irreducibleRepresentation ℂ j) with hφdef
  have hφcoe : ∀ j, ((φ j : ClassFunction ℂ H) : H → ℂ) = irreducibleCharacter ℂ j := fun j =>
    funext fun y => by
      simp only [hφdef, ofCharacter_apply, character_irreducibleRepresentation]
  -- each extends to an irreducible character of `G`, afforded by some representation `σ j`
  have hstar : ∀ j, ∃ (n : ℕ) (σ : Representation ℂ G (Fin n → ℂ)),
      ∀ x : G, σ.character x = (indExtend H (φ j)).1 x := by
    intro j
    obtain ⟨n, σ, -, hσ⟩ := mem_irreducibleCharacters_iff.mp
      (indExtend_mem_irreducibleCharacters hH (by rw [hφcoe j]; exact irreducibleCharacter_mem ℂ j))
    exact ⟨n, σ, congrFun hσ⟩
  choose n σ hσ using hstar
  refine ⟨⨅ j, (σ j).ker, Subgroup.normal_iInf_normal fun _ => inferInstance, ?_⟩
  have hker : ∀ (j : Fin (Nat.card (ConjClasses H))) (x : G),
      x ∈ (σ j).ker ↔ (indExtend H (φ j)).1 x = (φ j).1 1 := by
    intro j x
    rw [Representation.mem_ker_iff_char_eq (σ j) (isOfFinOrder_of_finite x), hσ j x, hσ j 1,
      indExtend_apply_one]
  ext g
  simp only [SetLike.mem_coe, Subgroup.mem_iInf, hker]
  constructor
  · -- an element of the common kernel lies in no conjugate of `H`, unless it is the identity
    intro hgN
    by_contra hcon
    obtain ⟨hg1, x, hx⟩ := notMem_frobeniusKernel_iff.mp hcon
    have hyN : ∀ j, (x⁻¹ * g * x) ∈ (σ j).ker := fun j =>
      (MonoidHom.normal_ker (σ j)).conj_mem' g ((hker j g).mpr (hgN j)) x
    -- on `H` the extension restricts back to `φ`, so every irreducible character of `H` is
    -- unmoved at the conjugated element, which therefore is the identity
    have hone : (⟨x⁻¹ * g * x, hx⟩ : H) = 1 := by
      refine eq_one_of_forall_irreducibleCharacter_eq ℂ fun f hf => ?_
      obtain ⟨j, rfl⟩ := exists_irreducibleCharacter_eq (k := ℂ) hf
      rw [← hφcoe j]
      calc (φ j).1 (⟨x⁻¹ * g * x, hx⟩ : H)
          = (indExtend H (φ j)).1 (x⁻¹ * g * x) := by
            simpa only [comap_apply, Subgroup.coe_subtype] using
              (congrArg (fun F : ClassFunction ℂ H => F.1 (⟨x⁻¹ * g * x, hx⟩ : H))
                (comap_subtype_indExtend hH
                  (isUnit_natCard_subgroup H (isUnit_of_invertible _)) (φ j))).symm
        _ = (φ j).1 1 := (hker j _).mp (hyN j)
    refine hg1 ?_
    have hy : x⁻¹ * g * x = 1 := congrArg Subtype.val hone
    have hgx : g = x * (x⁻¹ * g * x) * x⁻¹ := by group
    rw [hgx, hy, mul_one, mul_inv_cancel]
  · -- an element of the Frobenius kernel is in no conjugate of `H`, so the induced part vanishes
    intro hg j
    rcases mem_frobeniusKernel.mp hg with rfl | hgc
    · rw [indExtend_apply_one]
    -- no conjugate of `H` contains `g`, so *every* class function induced from `H` vanishes there
    have hindzero : ∀ f : H → ℂ, indClassFun H f g = 0 := fun f => by
      rw [indClassFun_apply]
      exact Finset.sum_eq_zero fun t _ => dite_eq_right (hgc _)
    simp [indExtend_def, hindzero]

/-- **The Frobenius kernel of a trivial-intersection subgroup, as a subgroup.**

Its carrier is the Frobenius kernel (`TauCeti.coe_frobeniusKernelSubgroup`) and it is normal
(`TauCeti.frobeniusKernelSubgroup_normal`), which is Frobenius's theorem.  A subgroup is determined
by its carrier, so nothing depends on the choice made inside that proof. -/
noncomputable def frobeniusKernelSubgroup (hH : IsTISubgroup H) : Subgroup G :=
  (exists_normal_coe_eq_frobeniusKernel hH).choose

/-- **The carrier of `TauCeti.frobeniusKernelSubgroup` is the Frobenius kernel.** -/
@[simp]
theorem coe_frobeniusKernelSubgroup (hH : IsTISubgroup H) :
    (frobeniusKernelSubgroup hH : Set G) = frobeniusKernel H :=
  (exists_normal_coe_eq_frobeniusKernel hH).choose_spec.2

/-- **Frobenius's theorem: the Frobenius kernel is normal.** -/
theorem frobeniusKernelSubgroup_normal (hH : IsTISubgroup H) :
    (frobeniusKernelSubgroup hH).Normal :=
  (exists_normal_coe_eq_frobeniusKernel hH).choose_spec.1

/-- Membership in the Frobenius kernel subgroup is membership in the Frobenius kernel. -/
@[simp]
theorem mem_frobeniusKernelSubgroup (hH : IsTISubgroup H) {g : G} :
    g ∈ frobeniusKernelSubgroup hH ↔ g = 1 ∨ ∀ x : G, x⁻¹ * g * x ∉ H := by
  rw [← mem_frobeniusKernel (H := H), ← coe_frobeniusKernelSubgroup hH, SetLike.mem_coe]

/-- **The Frobenius kernel is a complement to the complement**: `G = N ⋊ H`.  The kernel has
`|G : H|` elements and meets `H` only in the identity, which is all that
`TauCeti.IsTISubgroup.isComplement'_of_coe_eq_frobeniusKernel` needs. -/
theorem frobeniusKernel_isComplement' (hH : IsTISubgroup H) :
    (frobeniusKernelSubgroup hH).IsComplement' H :=
  hH.isComplement'_of_coe_eq_frobeniusKernel (coe_frobeniusKernelSubgroup hH)

/-- **The Frobenius kernel of a nontrivial trivial-intersection subgroup is proper**: it is
disjoint from `H`, which is not `⊥`. -/
theorem frobeniusKernelSubgroup_ne_top (hH : IsTISubgroup H) (hne : H ≠ ⊥) :
    frobeniusKernelSubgroup hH ≠ ⊤ := by
  intro htop
  refine hne (top_disjoint.mp ?_)
  rw [← htop]
  exact (frobeniusKernel_isComplement' hH).disjoint

/-- **The Frobenius kernel of a proper trivial-intersection subgroup is nontrivial**: it has
`|G : H|` elements, and `H ≠ ⊤` says that index is not `1`. -/
theorem frobeniusKernelSubgroup_ne_bot (hH : IsTISubgroup H) (hne : H ≠ ⊤) :
    frobeniusKernelSubgroup hH ≠ ⊥ := by
  intro hbot
  have hcard := (frobeniusKernel_isComplement' hH).index_eq_card
  rw [hbot, Subgroup.card_bot] at hcard
  exact hne (Subgroup.index_eq_one.mp hcard)

end TauCeti
