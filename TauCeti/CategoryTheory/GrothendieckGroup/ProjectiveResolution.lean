/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Projective
public import TauCeti.CategoryTheory.GrothendieckGroup.Resolution

/-!
# The Euler class of a finite projective resolution, and the resolution theorem

Let `E` be an exact structure on an additive category `C` and let `P` be a property of objects
consisting of `E`-projectives, containing a zero object and closed under binary biproducts. Then
`P` is extension closed, so the full subcategory on `P` carries an induced exact structure — in
fact the split one — and every finite `P`-resolution

```text
Kₙ ↪ Qₙ₋₁ ↠ Kₙ₋₁,   …,   K₁ ↪ Q₀ ↠ X
```

has an alternating class `[Q₀] - [Q₁] + ⋯ + (-1)ⁿ [Kₙ]` in the exact `K₀` of that subcategory.
Unlike the ambient class of `TauCeti/CategoryTheory/GrothendieckGroup/Resolution.lean`, which
telescopes to `[X]` and is therefore independent of every choice for trivial reasons, this class
is not visibly determined by `X`: nothing in the subcategory relates `[Q₀] - [K₁]` to `X`.

That it *is* determined by `X` is the content of this file. Schanuel's lemma turns two first
steps `K ↪ Q ↠ X` and `K' ↪ Q' ↠ X` into an isomorphism `K ⊞ Q' ≅ K' ⊞ Q`, and an induction on
the sum of the two lengths does the rest. The horseshoe lemma then makes the resulting invariant
additive on conflations, so it factors through the exact `K₀` of the objects of finite
`P`-dimension and inverts the map induced by the inclusion: this is Weibel's **resolution
theorem** in the projective case.

## Main definitions

* `TauCeti.ExactStructure.FiniteResolution.eulerClassFullSubcategory`: the alternating class of a
  finite `P`-resolution, in the exact `K₀` of the exact structure induced on the full subcategory
  on `P`. On top of the additivity hypotheses assumed throughout, its definition needs only
  extension closure of `P`, not projectivity.
* `TauCeti.ExactStructure.eulerClassOf`: the Euler class of an object admitting a finite
  `P`-resolution.
* `TauCeti.ExactStructure.resolutionEquiv`: the isomorphism of the resolution theorem.

## Main results

* `TauCeti.ExactStructure.FiniteResolution.eulerClassFullSubcategory_eq_eulerClassFullSubcategory`:
  **the Euler class depends only on the resolved object**, by Schanuel's lemma.
* `TauCeti.ExactStructure.eulerClassOf_eq_sub_of_conflation` and
  `TauCeti.ExactStructure.eulerClassOf_eq_add_of_conflation`: the Euler class drops by one step
  along a conflation with resolving middle term, and is additive on conflations. The second is
  the horseshoe lemma, iterated.
* `TauCeti.ExactStructure.map_eulerClassFullSubcategory_eq_of`: in the exact `K₀` of the objects
  of finite `P`-dimension the alternating class of a resolution of `X` is `[X]`.
* `TauCeti.ExactStructure.resolutionEquiv`, `TauCeti.ExactStructure.resolutionEquiv_of` and
  `TauCeti.ExactStructure.resolutionEquiv_symm_of`: **the resolution theorem**. The inclusion of
  the full subcategory on `P` into the objects admitting a finite `P`-resolution induces an
  isomorphism on exact `K₀`, whose inverse is the Euler class.

## Implementation notes

The well-definedness, conflation-additivity, and resolution-theorem results here carry
`P ≤ E.isProjective` as an explicit hypothesis. On top of `ContainsZero` and
`IsClosedUnderBinaryProducts`, which are assumed throughout, the underlying Euler-class definitions
and formal computation lemmas need only extension closure. None of the substantive results is
asserted for a general resolving subcategory. The resolution theorem is true in that generality —
for a replete, additive, extension-closed `P` closed under kernels of deflations between its own
objects — but its proof replaces Schanuel's lemma and the horseshoe by Weibel's common-refinement
argument, and is not carried out here. The projective case is the one that Layer 4's Cartan
comparison consumes.

The class of an object, as opposed to that of a resolution, is defined by choosing a resolution
with `Nonempty.some`; `TauCeti.ExactStructure.eulerClassOf_eq` immediately removes the choice, so
no result below depends on it.

Two inductions are carried out on a numerical bound rather than on the resolutions themselves:
the well-definedness induction consumes the sum of the two lengths, because Schanuel's lemma
replaces both chains at once, and the additivity induction consumes a common bound for the two
outer lengths, because the horseshoe replaces both at once. Both are stated as `private`
auxiliaries over an explicit `n`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Theorem 7.6
  and Lemma 7.6.1: the resolution theorem and the independence of the Euler class.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69, Sections
  11--12, for Schanuel's lemma and the horseshoe lemma in a Quillen exact category.
* [The Tau Ceti Grothendieck groups, Cartan maps, and Euler forms roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/GrothendieckEulerForms/README.md),
  Layer 3, whose Euler-class and resolution-theorem bullets are the targets proved here in the
  projective case, and whose Layer 4 Cartan comparison consumes them.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [LocallySmall.{w} C] {E : ExactStructure C} {P : ObjectProperty C}
  [ObjectProperty.EssentiallySmall.{w} P]

namespace ExactStructure

section

variable [P.ContainsZero] [P.IsClosedUnderBinaryProducts]

/-- A property containing a zero object and closed under binary products is automatically
replete, by `CategoryTheory.ObjectProperty.isClosedUnderIsomorphisms_of_containsZero`. -/
local instance : P.IsClosedUnderIsomorphisms :=
  ObjectProperty.isClosedUnderIsomorphisms_of_containsZero P

namespace FiniteResolution

section Projective

variable (hproj : P ≤ E.isProjective)

local notation "hP" => E.isExtensionClosed_of_le_isProjective hproj

/-- The inductive core of
`TauCeti.ExactStructure.FiniteResolution.eulerClassFullSubcategory_eq_eulerClassFullSubcategory`,
on the sum of the two lengths. Schanuel's lemma compares the two first steps, and the induction
hypothesis then compares the two remaining chains, each enlarged by the other's resolving term. -/
private theorem eulerClassFullSubcategory_eq_aux (n : ℕ) :
    ∀ {X : C} (r s : E.FiniteResolution P X), r.length + s.length ≤ n →
      r.eulerClassFullSubcategory hP = s.eulerClassFullSubcategory hP := by
  induction n with
  | zero =>
      intro X r s h
      cases r with
      | @base X hX =>
          cases s with
          | @base _ hX' => rfl
          | @step K Q _ hQ i p zero hp s => simp only [length_base, length_step] at h; omega
      | @step K Q X hQ i p zero hp r => simp only [length_step] at h; omega
  | succ n ih =>
      -- The mixed case: a resolution of length zero against one that begins with a conflation.
      have key : ∀ {X K Q : C} (hX : P X) (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X)
          (zero : i ≫ p = 0) (hp : E.Conflation (ShortComplex.mk i p zero))
          (s : E.FiniteResolution P K), s.length ≤ n →
          (base (E := E) hX).eulerClassFullSubcategory hP =
            (step hQ i p zero hp s).eulerClassFullSubcategory hP := by
        intro X K Q hX hQ i p zero hp s hs
        obtain ⟨e⟩ := E.nonempty_iso_biprod_of_projective hp (hproj _ hQ)
          (E.conflation_zero_id X) (hproj _ hX)
        have hcmp := ih ((s.biprod (base hX)).ofIso e)
          ((base (E := E) hQ).ofIso (isoZeroBiprod (isZero_zero C)))
          (by simp only [length_ofIso, length_biprod, length_base]; omega)
        rw [eulerClassFullSubcategory_ofIso, eulerClassFullSubcategory_ofIso,
          eulerClassFullSubcategory_biprod, eulerClassFullSubcategory_base,
          eulerClassFullSubcategory_base] at hcmp
        rw [eulerClassFullSubcategory_base, eulerClassFullSubcategory_step, ← hcmp]
        abel
      intro X r s h
      cases r with
      | @base X hX =>
          cases s with
          | @base _ hX' => rfl
          | @step K Q _ hQ i p zero hp s =>
              refine key hX hQ i p zero hp s ?_
              simp only [length_base, length_step] at h; omega
      | @step K Q X hQ i p zero hp r =>
          cases s with
          | @base _ hX' =>
              refine (key hX' hQ i p zero hp r ?_).symm
              simp only [length_base, length_step] at h; omega
          | @step K' Q' _ hQ' i' p' zero' hp' s =>
              simp only [length_step] at h
              obtain ⟨e⟩ := E.nonempty_iso_biprod_of_projective hp (hproj _ hQ) hp' (hproj _ hQ')
              have hcmp := ih ((r.biprod (base hQ')).ofIso e) (s.biprod (base hQ))
                (by simp only [length_ofIso, length_biprod, length_base]; omega)
              rw [eulerClassFullSubcategory_ofIso, eulerClassFullSubcategory_biprod,
                eulerClassFullSubcategory_biprod, eulerClassFullSubcategory_base,
                eulerClassFullSubcategory_base] at hcmp
              rw [eulerClassFullSubcategory_step, eulerClassFullSubcategory_step,
                sub_eq_sub_iff_add_eq_add]
              exact (add_comm _ _).trans (hcmp.symm.trans (add_comm _ _))

/-- **The Euler class in the `K₀` of the full subcategory on `P` depends only on the resolved
object.** Any two finite `P`-resolutions of the same object have the same alternating class in the
exact `K₀` of the canonically induced structure on `P`, as soon as every object satisfying `P` is
`E`-projective.

The proof is an induction on the sum of the two lengths whose only geometric input is Schanuel's
lemma `TauCeti.ExactStructure.nonempty_iso_biprod_of_projective`: it turns the two first steps
`K ↪ Q ↠ X` and `K' ↪ Q' ↠ X` into an isomorphism `K ⊞ Q' ≅ K' ⊞ Q`, and the two remaining
chains, each enlarged by the other's resolving term, resolve the two sides. -/
theorem eulerClassFullSubcategory_eq_eulerClassFullSubcategory
    {X : C} (r s : E.FiniteResolution P X) :
    r.eulerClassFullSubcategory hP = s.eulerClassFullSubcategory hP :=
  eulerClassFullSubcategory_eq_aux hproj _ r s le_rfl

end Projective

end FiniteResolution


section EulerClassOf

section General

variable (hP : E.IsExtensionClosed P)

/-- **The Euler class of an object of finite `P`-dimension**, in the exact `K₀` of the structure
induced on the full subcategory on `P`: the alternating class of some, hence when `P` consists of
`E`-projectives, by `TauCeti.ExactStructure.eulerClassOf_eq` of any, finite `P`-resolution of it. -/
noncomputable def eulerClassOf {X : C} (hX : E.admitsFiniteResolution P X) :
    ExactK0 (E.fullSubcategory P hP) :=
  ((E.admitsFiniteResolution_iff P).mp hX).some.eulerClassFullSubcategory hP

end General

variable (hproj : P ≤ E.isProjective)

local notation "hP" => E.isExtensionClosed_of_le_isProjective hproj

include hproj in
/-- Every finite `P`-resolution of `X` computes `TauCeti.ExactStructure.eulerClassOf`. -/
theorem eulerClassOf_eq {X : C} (hX : E.admitsFiniteResolution P X)
    (r : E.FiniteResolution P X) :
    E.eulerClassOf hP hX = r.eulerClassFullSubcategory hP :=
  FiniteResolution.eulerClassFullSubcategory_eq_eulerClassFullSubcategory hproj _ r

include hproj in
/-- On an object satisfying `P` the Euler class is the class of that object. -/
@[simp]
theorem eulerClassOf_of_prop {X : C} (hX : P X) :
    E.eulerClassOf hP (E.le_admitsFiniteResolution P X hX) =
      ExactK0.of (⟨X, hX⟩ : P.FullSubcategory) := by
  rw [E.eulerClassOf_eq hproj _ (.base hX),
    FiniteResolution.eulerClassFullSubcategory_base]

include hproj in
/-- **The Euler class drops by one step along a conflation with resolving middle term**:
`χ(X) = [Q] - χ(K)` for a conflation `K ↪ Q ↠ X` with `P Q`. -/
theorem eulerClassOf_eq_sub_of_conflation {K Q X : C} (hQ : P Q) {i : K ⟶ Q} {p : Q ⟶ X}
    {zero : i ≫ p = 0} (hp : E.Conflation (ShortComplex.mk i p zero))
    (hK : E.admitsFiniteResolution P K) :
    E.eulerClassOf hP (E.admitsFiniteResolution_of_conflation P hQ hp hK) =
      ExactK0.of (⟨Q, hQ⟩ : P.FullSubcategory) - E.eulerClassOf hP hK := by
  rw [E.eulerClassOf_eq hproj _ (.step hQ i p zero hp
      ((E.admitsFiniteResolution_iff P).mp hK).some),
    FiniteResolution.eulerClassFullSubcategory_step,
    E.eulerClassOf_eq hproj hK ((E.admitsFiniteResolution_iff P).mp hK).some]

include hproj in
/-- The inductive core of `TauCeti.ExactStructure.eulerClassOf_eq_add_of_conflation`, on a common
bound for the lengths of resolutions of the two outer terms. Its inductive step is the horseshoe
lemma: the resolving terms add, and the new syzygy is an extension of the two old ones. -/
private theorem eulerClassOf_add_aux (n : ℕ) :
    ∀ {S : ShortComplex C}, E.Conflation S →
      ∀ (h₁ : E.admitsFiniteResolution P S.X₁) (h₃ : E.admitsFiniteResolution P S.X₃)
        (h₂ : E.admitsFiniteResolution P S.X₂),
        (∃ r : E.FiniteResolution P S.X₁, r.length ≤ n) →
        (∃ t : E.FiniteResolution P S.X₃, t.length ≤ n) →
        E.eulerClassOf hP h₂ = E.eulerClassOf hP h₁ + E.eulerClassOf hP h₃ := by
  induction n with
  | zero =>
      intro S hS h₁ h₃ h₂ hr ht
      obtain ⟨r, hrl⟩ := hr
      obtain ⟨t, htl⟩ := ht
      have hX₁ : P S.X₁ := by simpa using r.prop_syzygy hrl
      have hX₃ : P S.X₃ := by simpa using t.prop_syzygy htl
      rw [E.eulerClassOf_eq hproj h₂
          (.base ((E.isExtensionClosed_of_le_isProjective hproj).prop_X₂ hS hX₁ hX₃)),
        E.eulerClassOf_eq hproj h₁ (.base hX₁),
        E.eulerClassOf_eq hproj h₃ (.base hX₃),
        FiniteResolution.eulerClassFullSubcategory_base,
        FiniteResolution.eulerClassFullSubcategory_base,
        FiniteResolution.eulerClassFullSubcategory_base]
      exact ExactK0.of_conflation_fullSubcategory hP hS hX₁ hX₃
  | succ n ih =>
      intro S hS h₁ h₃ h₂ hr ht
      obtain ⟨KX, QX, mX, aX, hmX, hQX, hcX, hKX⟩ :=
        E.exists_conflation_of_exists_finiteResolution_length_le_succ hr
      obtain ⟨KZ, QZ, mZ, aZ, hmZ, hQZ, hcZ, hKZ⟩ :=
        E.exists_conflation_of_exists_finiteResolution_length_le_succ ht
      obtain ⟨K, u, a, hu, v, w, hv, hKu, hKv, -, -, -, -⟩ :=
        E.exists_conflation_biprod_of_conflation_of_projective hS hcX hcZ (hproj _ hQZ)
      have haX : E.admitsFiniteResolution P KX :=
        (E.admitsFiniteResolution_iff P).mpr ⟨hKX.choose⟩
      have haZ : E.admitsFiniteResolution P KZ :=
        (E.admitsFiniteResolution_iff P).mpr ⟨hKZ.choose⟩
      have haK : E.admitsFiniteResolution P K :=
        (E.isExtensionClosed_admitsFiniteResolution hproj).prop_X₂ hKv haX haZ
      have e₂ : E.eulerClassOf hP h₂ =
          ExactK0.of (⟨QX ⊞ QZ,
            (E.isExtensionClosed_of_le_isProjective hproj).prop_biprod hQX hQZ⟩ :
              P.FullSubcategory) - E.eulerClassOf hP haK :=
        E.eulerClassOf_eq_sub_of_conflation hproj
          ((E.isExtensionClosed_of_le_isProjective hproj).prop_biprod hQX hQZ) hKu haK
      have e₁ : E.eulerClassOf hP h₁ =
          ExactK0.of (⟨QX, hQX⟩ : P.FullSubcategory) - E.eulerClassOf hP haX :=
        E.eulerClassOf_eq_sub_of_conflation hproj hQX hcX haX
      have e₃ : E.eulerClassOf hP h₃ =
          ExactK0.of (⟨QZ, hQZ⟩ : P.FullSubcategory) - E.eulerClassOf hP haZ :=
        E.eulerClassOf_eq_sub_of_conflation hproj hQZ hcZ haZ
      have eK : E.eulerClassOf hP haK =
          E.eulerClassOf hP haX + E.eulerClassOf hP haZ := ih hKv haX haZ haK hKX hKZ
      rw [e₁, e₂, e₃, eK, ExactK0.of_biprod_fullSubcategory hP hQX hQZ]
      abel

/-- **The Euler class is additive on conflations.** This is the second half of the Euler-class
package: together with `TauCeti.ExactStructure.eulerClassOf_eq` it makes the alternating class of
a finite projective resolution a conflation-additive invariant of the objects of finite
`P`-dimension. -/
theorem eulerClassOf_eq_add_of_conflation {S : ShortComplex C} (hS : E.Conflation S)
    (h₁ : E.admitsFiniteResolution P S.X₁) (h₃ : E.admitsFiniteResolution P S.X₃) :
    E.eulerClassOf hP ((E.isExtensionClosed_admitsFiniteResolution hproj).prop_X₂ hS h₁ h₃) =
      E.eulerClassOf hP h₁ + E.eulerClassOf hP h₃ :=
  E.eulerClassOf_add_aux hproj
    (max ((E.admitsFiniteResolution_iff P).mp h₁).some.length
      ((E.admitsFiniteResolution_iff P).mp h₃).some.length) hS h₁ h₃ _
    ⟨_, le_max_left _ _⟩ ⟨_, le_max_right _ _⟩

include hproj in
/-- The Euler class is invariant under isomorphism of the resolved object. -/
theorem eulerClassOf_congr {X Y : C} (e : X ≅ Y) (hX : E.admitsFiniteResolution P X)
    (hY : E.admitsFiniteResolution P Y) : E.eulerClassOf hP hX = E.eulerClassOf hP hY := by
  rw [E.eulerClassOf_eq hproj hY
      (((E.admitsFiniteResolution_iff P).mp hX).some.ofIso e),
    FiniteResolution.eulerClassFullSubcategory_ofIso]
  exact E.eulerClassOf_eq hproj hX _

section ResolutionTheorem

variable [ObjectProperty.EssentiallySmall.{w} (E.admitsFiniteResolution P)]

/-- **The class of an object of finite `P`-dimension is the alternating class of any of its
finite `P`-resolutions**, after pushing the latter forward along the inclusion. This is the
telescoping computation of `TauCeti.ExactStructure.FiniteResolution.eulerClass_eq_of`, carried
out in the exact `K₀` of the objects of finite `P`-dimension rather than in that of the whole
ambient category. -/
@[simp]
theorem map_eulerClassFullSubcategory_eq_of {X : C} (r : E.FiniteResolution P X) :
    ExactK0.map _ (E.isConflationExact_ιOfLE hP
      (E.isExtensionClosed_admitsFiniteResolution hproj) (E.le_admitsFiniteResolution P))
        (r.eulerClassFullSubcategory hP) =
      ExactK0.of (⟨X, (E.admitsFiniteResolution_iff P).mpr ⟨r⟩⟩ :
        (E.admitsFiniteResolution P).FullSubcategory) := by
  induction r with
  | @base X hX =>
      rw [FiniteResolution.eulerClassFullSubcategory_base, ExactK0.map_of]
      rfl
  | @step K Q X hQ i p zero hp r ih =>
      have hK : E.admitsFiniteResolution P K := (E.admitsFiniteResolution_iff P).mpr ⟨r⟩
      have hX : E.admitsFiniteResolution P X :=
        E.admitsFiniteResolution_of_conflation P hQ hp hK
      have hsum : ExactK0.of ((ObjectProperty.ιOfLE (E.le_admitsFiniteResolution P)).obj
            (⟨Q, hQ⟩ : P.FullSubcategory)) =
          ExactK0.of (⟨K, hK⟩ : (E.admitsFiniteResolution P).FullSubcategory) +
            ExactK0.of (⟨X, hX⟩ : (E.admitsFiniteResolution P).FullSubcategory) :=
        ExactK0.of_conflation_fullSubcategory
          (E.isExtensionClosed_admitsFiniteResolution hproj) hp hK hX
      rw [FiniteResolution.eulerClassFullSubcategory_step, map_sub, ExactK0.map_of, ih, hsum]
      abel

/-- The Euler class of the objects of finite `P`-dimension, as a conflation-additive invariant
with values in the exact `K₀` of the full subcategory on `P`. -/
private noncomputable def eulerInvariant :
    ExactK0.AdditiveInvariant
      (E.fullSubcategory (E.admitsFiniteResolution P)
        (E.isExtensionClosed_admitsFiniteResolution hproj))
      (ExactK0 (E.fullSubcategory P hP)) where
  obj X := E.eulerClassOf hP X.property
  map_iso _ _ e := E.eulerClassOf_congr hproj ((E.admitsFiniteResolution P).ι.mapIso e) _ _
  map_conflation S hS := by
    rw [fullSubcategory_conflation_iff] at hS
    exact E.eulerClassOf_eq_add_of_conflation hproj hS _ _

/-- **The inverse of the comparison map of the resolution theorem**: the homomorphism sending the
class of an object of finite `P`-dimension to the alternating class of any of its finite
`P`-resolutions. -/
noncomputable def eulerHom :
    ExactK0 (E.fullSubcategory (E.admitsFiniteResolution P)
        (E.isExtensionClosed_admitsFiniteResolution hproj)) →+
      ExactK0 (E.fullSubcategory P hP) :=
  ExactK0.lift (E.eulerInvariant hproj)

@[simp] theorem eulerHom_of {X : C} (hX : E.admitsFiniteResolution P X) :
    E.eulerHom hproj (ExactK0.of ⟨X, hX⟩) = E.eulerClassOf hP hX :=
  ExactK0.lift_of _ _

/-- **The resolution theorem for finite projective resolutions.** When every object satisfying
`P` is `E`-projective, the inclusion of the full subcategory on `P` into the full subcategory of
objects admitting a finite `P`-resolution induces an isomorphism of exact Grothendieck groups.
Its inverse sends the class of an object to the alternating class of any finite `P`-resolution of
it, by `TauCeti.ExactStructure.resolutionEquiv_symm_of`. -/
noncomputable def resolutionEquiv :
    ExactK0 (E.fullSubcategory P hP) ≃+
      ExactK0 (E.fullSubcategory (E.admitsFiniteResolution P)
        (E.isExtensionClosed_admitsFiniteResolution hproj)) where
  toFun := ExactK0.map _ (E.isConflationExact_ιOfLE hP
    (E.isExtensionClosed_admitsFiniteResolution hproj) (E.le_admitsFiniteResolution P))
  invFun := E.eulerHom hproj
  map_add' _ _ := map_add _ _ _
  left_inv x := by
    refine DFunLike.congr_fun (ExactK0.hom_ext (f := (E.eulerHom hproj).comp
      (ExactK0.map _ (E.isConflationExact_ιOfLE hP
        (E.isExtensionClosed_admitsFiniteResolution hproj) (E.le_admitsFiniteResolution P))))
      (g := AddMonoidHom.id _)
      fun Y => ?_) x
    rw [AddMonoidHom.coe_comp, Function.comp_apply, ExactK0.map_of, E.eulerHom_of,
      E.eulerClassOf_of_prop hproj Y.property, AddMonoidHom.id_apply]
  right_inv x := by
    refine DFunLike.congr_fun (ExactK0.hom_ext
      (f := (ExactK0.map _ (E.isConflationExact_ιOfLE hP
        (E.isExtensionClosed_admitsFiniteResolution hproj) (E.le_admitsFiniteResolution P))).comp
          (E.eulerHom hproj))
      (g := AddMonoidHom.id _) fun Y => ?_) x
    rw [AddMonoidHom.coe_comp, Function.comp_apply, E.eulerHom_of, AddMonoidHom.id_apply,
      E.eulerClassOf_eq hproj Y.property ((E.admitsFiniteResolution_iff P).mp Y.property).some,
      E.map_eulerClassFullSubcategory_eq_of hproj]

/-- The forward map of the resolution equivalence sends a `P`-object to its class in the full
subcategory of objects admitting a finite `P`-resolution. -/
@[simp] theorem resolutionEquiv_of (X : P.FullSubcategory) :
    E.resolutionEquiv hproj (ExactK0.of X) =
      ExactK0.of ⟨X.obj, E.le_admitsFiniteResolution P X.obj X.property⟩ :=
  ExactK0.map_of _ _ _

/-- The inverse map of the resolution equivalence sends an object class to its Euler class. -/
@[simp] theorem resolutionEquiv_symm_of {X : C} (hX : E.admitsFiniteResolution P X) :
    (E.resolutionEquiv hproj).symm (ExactK0.of ⟨X, hX⟩) = E.eulerClassOf hP hX :=
  E.eulerHom_of hproj hX

end ResolutionTheorem

end EulerClassOf

end

end ExactStructure

end TauCeti
