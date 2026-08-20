/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.Functor
public import TauCeti.CategoryTheory.GrothendieckGroup.Exact

/-!
# Abelian `K₀` of an essentially small abelian category

The abelian Grothendieck group `TauCeti.AbelianK0 C` of an essentially small abelian category `C`
is the free abelian group on the isomorphism classes of objects modulo the relations
`[X₂] = [X₁] + [X₃]`, one for each short exact sequence `X₁ ⟶ X₂ ⟶ X₃`.

It is *not* a second presentation: it is defined as the exact `K₀` of the canonical exact
structure `TauCeti.ExactStructure.abelian C`, whose conflations are exactly the short exact short
complexes. The whole exact-`K₀` API therefore applies verbatim, along the identification
`TauCeti.AbelianK0.toExactK0`; what this file adds is the same API phrased in terms of
`CategoryTheory.ShortComplex.ShortExact` instead of conflations, functoriality under the exactness
hypothesis appropriate to abelian categories, and the calculus of kernels and cokernels which is
available here but not in a general exact category.

The last point is the substance of the file. Because an abelian category factors every morphism,
an arbitrary `f : X ⟶ Y` — with no monomorphism or epimorphism hypothesis whatsoever — satisfies
`[X] - [Y] = [ker f] - [coker f]` in `AbelianK0 C`; see
`TauCeti.AbelianK0.of_sub_of_eq_of_kernel_sub_of_cokernel`. The proof splits `f` through its
coimage and its image and uses that the two agree.

## Main definitions

* `TauCeti.AbelianK0 C`: abelian `K₀`, with class map `TauCeti.AbelianK0.of`, defined as the exact
  `K₀` of `TauCeti.ExactStructure.abelian C`.
* `TauCeti.AbelianK0.toExactK0`: the identification of abelian `K₀` with that exact `K₀`, along
  which the exact-`K₀` API transfers.
* `TauCeti.AbelianK0.AdditiveInvariant C G`: an isomorphism-invariant function on objects which is
  additive on short exact sequences, and `TauCeti.AbelianK0.lift` the homomorphism it induces.
* `TauCeti.AbelianK0.map` and `TauCeti.AbelianK0.mapEquiv`: functoriality for an additive functor
  preserving finite limits and finite colimits, and invariance under an additive equivalence.
* `TauCeti.AbelianK0.fromSplit`: the canonical comparison out of split `K₀`.

## Main results

* `TauCeti.AbelianK0.of_shortExact`: the defining relation, with
  `TauCeti.AbelianK0.of_eq_add_of_cokernel` and `TauCeti.AbelianK0.of_eq_of_kernel_add` its
  consequences for a monomorphism and for an epimorphism.
* `TauCeti.AbelianK0.of_sub_of_eq_of_kernel_sub_of_cokernel`: for *every* morphism `f : X ⟶ Y`,
  `[X] - [Y] = [ker f] - [coker f]`.
* `TauCeti.AbelianK0.liftEquiv`: the universal property. Invariants additive on short exact
  sequences correspond bijectively to homomorphisms `AbelianK0 C →+ G`.
* `TauCeti.AbelianK0.map_comp_fromSplit`: naturality of the comparison out of split `K₀` in an
  exact functor.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Section 6.1.2, where `K₀` of an abelian category and its universal property for invariants
  additive on short exact sequences are stated.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69, Section 13.2,
  for the canonical exact structure whose exact `K₀` this is.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w w' w'' v v' v'' u u' u''

variable (C : Type u) [Category.{v} C] [Abelian C] [EssentiallySmall.{w} C]

/-- The Grothendieck group of an essentially small abelian category: the free abelian group on the
isomorphism classes of objects, modulo `[X₂] = [X₁] + [X₃]` for every short exact sequence
`X₁ ⟶ X₂ ⟶ X₃`. It is the exact `K₀` of the canonical exact structure. -/
def AbelianK0 : Type w := ExactK0 (ExactStructure.abelian C)

noncomputable instance : AddCommGroup (AbelianK0 C) :=
  inferInstanceAs (AddCommGroup (ExactK0 (ExactStructure.abelian C)))

namespace AbelianK0

/-- Abelian `K₀` is the exact `K₀` of the canonical exact structure, by definition. This
identification is the bridge along which the exact-`K₀` API applies to abelian `K₀`. -/
noncomputable def toExactK0 : AbelianK0 C ≃+ ExactK0 (ExactStructure.abelian C) :=
  AddEquiv.refl _

variable {C}

/-- The class of an object in abelian `K₀`. -/
noncomputable def of (X : C) : AbelianK0 C := ExactK0.of X

@[simp]
lemma toExactK0_of (X : C) : toExactK0 C (of X) = ExactK0.of X := (rfl)

@[simp]
lemma toExactK0_symm_of (X : C) :
    (toExactK0 C).symm (ExactK0.of X) = (of X : AbelianK0 C) := (rfl)

lemma of_congr {X Y : C} (e : X ≅ Y) : (of X : AbelianK0 C) = of Y :=
  ExactK0.of_congr e

/-- **The defining relation of abelian `K₀`**: the class of the middle term of a short exact
sequence is the sum of the classes of its outer terms. -/
theorem of_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    (of S.X₂ : AbelianK0 C) = of S.X₁ + of S.X₃ :=
  ExactK0.of_conflation ((ExactStructure.abelian_conflation S).mpr hS)

/-- The defining relation of abelian `K₀`, stated for a short exact sequence presented by its two
maps. -/
theorem of_eq_add_of_shortExact {X Y Z : C} {i : X ⟶ Y} {p : Y ⟶ Z} (zero : i ≫ p = 0)
    (hS : (ShortComplex.mk i p zero).ShortExact) : (of Y : AbelianK0 C) = of X + of Z :=
  of_shortExact hS

/-- The class of the subobject of a short exact sequence is the difference of the other two
classes. -/
theorem of_eq_sub_of_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    (of S.X₁ : AbelianK0 C) = of S.X₂ - of S.X₃ := by
  rw [of_shortExact hS]
  abel

/-- The class of a biproduct is the sum of the classes. -/
@[simp]
theorem of_biprod (X Y : C) : (of (X ⊞ Y) : AbelianK0 C) = of X + of Y :=
  ExactK0.of_biprod X Y

/-- The class of an object which is zero vanishes. -/
@[simp]
theorem of_eq_zero_of_isZero {X : C} (hX : IsZero X) : (of X : AbelianK0 C) = 0 :=
  ExactK0.of_eq_zero_of_isZero hX

/-- The class of the zero object vanishes. -/
@[simp]
theorem of_zero : (of (0 : C) : AbelianK0 C) = 0 :=
  ExactK0.of_zero

/-- The image of the class map generates abelian `K₀`. -/
theorem closure_range_of : AddSubgroup.closure (Set.range (of : C → AbelianK0 C)) = ⊤ :=
  ExactK0.closure_range_of

/-- Induction on the classes of objects of `C`: no skeleton representative is ever mentioned. -/
@[elab_as_elim]
theorem induction_on {motive : AbelianK0 C → Prop} (x : AbelianK0 C) (zero : motive 0)
    (of : ∀ X : C, motive (AbelianK0.of X)) (add : ∀ a b, motive a → motive b → motive (a + b))
    (neg : ∀ a, motive a → motive (-a)) : motive x :=
  ExactK0.induction_on x zero of add neg

variable {G : Type*} [AddCommGroup G]

/-- Two homomorphisms out of abelian `K₀` agreeing on the classes of objects are equal. -/
@[ext]
theorem hom_ext {f g : AbelianK0 C →+ G} (h : ∀ X : C, f (of X) = g (of X)) : f = g :=
  ExactK0.hom_ext h

section KernelCokernel

variable {X Y Z : C}

/-- A monomorphism `i : X ⟶ Y` gives `[Y] = [X] + [coker i]`. -/
theorem of_eq_add_of_cokernel (i : X ⟶ Y) [Mono i] :
    (of Y : AbelianK0 C) = of X + of (cokernel i) :=
  ExactK0.of_conflation (ExactStructure.abelian_conflation_of_mono i)

/-- An epimorphism `p : Y ⟶ Z` gives `[Y] = [ker p] + [Z]`. -/
theorem of_eq_of_kernel_add (p : Y ⟶ Z) [Epi p] :
    (of Y : AbelianK0 C) = of (kernel p) + of Z :=
  ExactK0.of_conflation (ExactStructure.abelian_conflation_of_epi p)

/-- The class of the coimage of a morphism: `[X] = [ker f] + [coim f]`, because `X` surjects onto
its coimage with kernel `ker f`. -/
theorem of_eq_of_kernel_add_of_coimage (f : X ⟶ Y) :
    (of X : AbelianK0 C) = of (kernel f) + of (Abelian.coimage f) :=
  of_eq_add_of_cokernel (kernel.ι f)

/-- The class of the image of a morphism: `[Y] = [im f] + [coker f]`, because the image of `f` is
the kernel of the cokernel projection of `f`. -/
theorem of_eq_of_image_add_of_cokernel (f : X ⟶ Y) :
    (of Y : AbelianK0 C) = of (Abelian.image f) + of (cokernel f) :=
  of_eq_of_kernel_add (cokernel.π f)

/-- **The kernel–cokernel identity in abelian `K₀`**: an arbitrary morphism `f : X ⟶ Y`, with no
monomorphism or epimorphism hypothesis, satisfies `[X] - [Y] = [ker f] - [coker f]`.

The two sides measure the same defect: `X` and `Y` differ, in `K₀`, only through the kernel and
cokernel of `f`, because `f` factors as an epimorphism onto its coimage followed by a
monomorphism out of its image, and coimage and image agree in an abelian category. -/
theorem of_sub_of_eq_of_kernel_sub_of_cokernel (f : X ⟶ Y) :
    (of X : AbelianK0 C) - of Y = of (kernel f) - of (cokernel f) := by
  rw [of_eq_of_kernel_add_of_coimage f, of_eq_of_image_add_of_cokernel f,
    of_congr (Abelian.coimageIsoImage f)]
  abel

end KernelCokernel

variable (C) in
/-- An additive invariant for abelian `K₀`: a function on objects of `C`, constant on isomorphism
classes and additive on short exact sequences. These are exactly the data that factor through
`TauCeti.AbelianK0 C`; see `TauCeti.AbelianK0.liftEquiv`. -/
@[ext]
structure AdditiveInvariant (G : Type*) [AddCommGroup G] where
  /-- The value of the invariant on an object. -/
  obj : C → G
  /-- Isomorphic objects receive equal values. -/
  map_iso : ∀ ⦃X Y : C⦄, (X ≅ Y) → obj X = obj Y
  /-- The value on the middle term of a short exact sequence is the sum of the outer values. -/
  map_shortExact : ∀ ⦃S : ShortComplex C⦄, S.ShortExact → obj S.X₂ = obj S.X₁ + obj S.X₃

/-- An invariant additive on short exact sequences is an invariant additive on the conflations of
the canonical exact structure. -/
private def AdditiveInvariant.toExact (a : AdditiveInvariant C G) :
    ExactK0.AdditiveInvariant (ExactStructure.abelian C) G where
  obj := a.obj
  map_iso := a.map_iso
  map_conflation _ hS := a.map_shortExact ((ExactStructure.abelian_conflation _).mp hS)

omit [EssentiallySmall.{w} C] in
@[simp] private lemma AdditiveInvariant.toExact_obj (a : AdditiveInvariant C G) :
    a.toExact.obj = a.obj :=
  (rfl)

/-- The homomorphism out of abelian `K₀` induced by an invariant additive on short exact
sequences. -/
noncomputable def lift (a : AdditiveInvariant C G) : AbelianK0 C →+ G :=
  ExactK0.lift a.toExact

@[simp]
lemma lift_of (a : AdditiveInvariant C G) (X : C) : lift a (of X) = a.obj X :=
  ExactK0.lift_of a.toExact X

/-- Any homomorphism agreeing with an additive invariant on object classes is its induced lift. -/
theorem lift_unique (a : AdditiveInvariant C G) (f : AbelianK0 C →+ G)
    (hf : ∀ X : C, f (of X) = a.obj X) : f = lift a :=
  hom_ext fun X => by rw [hf, lift_of]

/-- **The universal property of abelian `K₀`**: invariants additive on short exact sequences with
values in `G` correspond bijectively to additive homomorphisms `AbelianK0 C →+ G`. -/
noncomputable def liftEquiv : AdditiveInvariant C G ≃ (AbelianK0 C →+ G) where
  toFun := lift
  invFun f :=
    { obj := fun X => f (of X)
      map_iso := fun _ _ e => by rw [of_congr e]
      map_shortExact := fun _ hS => by rw [of_shortExact hS, map_add] }
  left_inv a := by ext X; exact lift_of a X
  right_inv f := (lift_unique _ f fun _ => rfl).symm

@[simp]
lemma liftEquiv_apply (a : AdditiveInvariant C G) : liftEquiv a = lift a := (rfl)

@[simp]
lemma liftEquiv_symm_apply_obj (f : AbelianK0 C →+ G) (X : C) :
    ((liftEquiv (C := C) (G := G)).symm f).obj X = f (of X) := (rfl)

section Functoriality

variable {D : Type u'} [Category.{v'} D] [Abelian D] [EssentiallySmall.{w'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **Functoriality of abelian `K₀`**: an additive functor preserving finite limits and finite
colimits — that is, an exact functor — induces a homomorphism of abelian Grothendieck groups.

Exactness is the right hypothesis and cannot be weakened to additivity: an additive functor need
not send a short exact sequence to a short exact one, so it need not respect the defining
relations. -/
noncomputable def map : AbelianK0 C →+ AbelianK0 D :=
  ExactK0.map F (ExactStructure.isConflationExact_abelian F)

@[simp]
lemma map_of (X : C) : map F (of X) = (of (F.obj X) : AbelianK0 D) :=
  ExactK0.map_of F _ X

/-- Any homomorphism sending object classes to the classes of their images is the induced map. -/
theorem map_unique (f : AbelianK0 C →+ AbelianK0 D)
    (hf : ∀ X : C, f (of X) = (of (F.obj X) : AbelianK0 D)) : f = map F :=
  hom_ext fun X => by rw [hf, map_of]

variable (C) in
/-- The identity functor induces the identity of abelian `K₀`. -/
@[simp]
theorem map_id : map (𝟭 C) = AddMonoidHom.id (AbelianK0 C) :=
  hom_ext fun X => by rw [map_of, AddMonoidHom.id_apply, Functor.id_obj]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits in
/-- The induced maps of a composite of exact functors compose. -/
theorem map_comp {K : Type u''} [Category.{v''} K] [Abelian K] [EssentiallySmall.{w''} K]
    (H : D ⥤ K) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    map (F ⋙ H) = (map H).comp (map F) :=
  hom_ext fun X => by rw [map_of, AddMonoidHom.comp_apply, map_of, map_of, Functor.comp_obj]

/-- Naturally isomorphic exact functors induce the same map. -/
theorem map_congr {F' : C ⥤ D} [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (e : F ≅ F') : map F = map F' :=
  hom_ext fun X => by rw [map_of, map_of, of_congr (e.app X)]

/-- **Equivalence invariance of abelian `K₀`**: an additive equivalence of abelian categories
induces an isomorphism of abelian Grothendieck groups. No exactness hypothesis is needed, since an
equivalence preserves all limits and colimits. -/
noncomputable def mapEquiv (e : C ≌ D) [e.functor.Additive] : AbelianK0 C ≃+ AbelianK0 D :=
  ExactK0.mapEquiv e (ExactStructure.isConflationExact_abelian e.functor)
    (ExactStructure.isConflationExact_abelian e.inverse)

@[simp]
lemma mapEquiv_of (e : C ≌ D) [e.functor.Additive] (X : C) :
    mapEquiv e (of X) = (of (e.functor.obj X) : AbelianK0 D) :=
  ExactK0.mapEquiv_of e _ _ X

@[simp]
lemma mapEquiv_symm_of (e : C ≌ D) [e.functor.Additive] (Y : D) :
    (mapEquiv e).symm (of Y) = (of (e.inverse.obj Y) : AbelianK0 C) :=
  ExactK0.mapEquiv_symm_of e _ _ Y

end Functoriality

section Comparison

variable (C)

/-- **The canonical comparison from split `K₀` to abelian `K₀`.** It is induced by the class map,
which respects the biproduct relations because the biproduct sequences are short exact. -/
noncomputable def fromSplit : SplitK0 C →+ AbelianK0 C :=
  ExactK0.fromSplit (ExactStructure.abelian C)

@[simp]
lemma fromSplit_of (X : C) : fromSplit C (SplitK0.of X) = (of X : AbelianK0 C) :=
  ExactK0.fromSplit_of X

/-- The canonical comparison out of split `K₀` is the unique homomorphism preserving the classes
of objects. -/
theorem fromSplit_unique (f : SplitK0 C →+ AbelianK0 C)
    (hf : ∀ X : C, f (SplitK0.of X) = (of X : AbelianK0 C)) : f = fromSplit C :=
  SplitK0.hom_ext fun X => by rw [hf, fromSplit_of]

/-- The canonical comparison out of split `K₀` is surjective: abelian `K₀` is a quotient of split
`K₀`, since imposing the short exact relations only adds relations. -/
theorem fromSplit_surjective : Function.Surjective (fromSplit C) :=
  ExactK0.fromSplit_surjective

variable {C}

/-- **Naturality of the comparison out of split `K₀`** in an exact functor. -/
theorem map_comp_fromSplit {D : Type u'} [Category.{v'} D] [Abelian D] [EssentiallySmall.{w'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (map F).comp (fromSplit C) = (fromSplit D).comp (SplitK0.map F) :=
  SplitK0.hom_ext fun X => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, fromSplit_of, map_of, SplitK0.map_of,
      fromSplit_of]

end Comparison

end AbelianK0

end TauCeti
