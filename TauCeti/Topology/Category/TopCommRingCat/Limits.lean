/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Category.TopCommRingCat
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Products and equalizers of topological commutative rings

Mathlib's `TopCommRingCat` carries no limit constructions at all. This file provides the two
shapes the sheaf condition consumes — products and equalizers — by exhibiting the explicit
cones: the pointwise ring with the product topology, and the agreement subring with the
subspace topology.

The forgetful functor to `CommRingCat` does not *create* these limits in the technical sense:
it does not reflect them, since the topology on a cone apex is not determined by the
underlying ring — the same reason `TopCat`'s own forgetful functor does not create products
or arbitrary limits (it does create some shapes, such as terminal objects). What is true, and
what later files use, is that the constructions below have the expected underlying rings,
which is plain from their statements.

## Main definitions

* `TauCeti.TopCommRingCat.piFan` and `TauCeti.TopCommRingCat.piFanIsLimit` : the product of a
  family, as the pointwise ring under the product topology.
* `TauCeti.TopCommRingCat.equalizerFork` and `TauCeti.TopCommRingCat.equalizerForkIsLimit` :
  the equalizer of a parallel pair, as the agreement subring under the subspace topology.
* The resulting `HasProducts` and `HasEqualizers` instances.

The equalizer fork's inclusion is, as a function, the subtype coercion of the agreement subring,
and by `rfl`; consumers state closedness of its range against the coercion and let that
definitional equality carry it to the categorical morphism, rather than going through a named
lemma here.

The closedness of the agreement subring over a Hausdorff codomain — what will keep equalizers
of complete separated rings complete — is Mathlib's `isClosed_eq` applied to the two morphisms'
continuity fields; consumers use it directly rather than through a named specialization here.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1 — the sheaf condition of §8.2 is stated in
  complete Hausdorff topological rings, whose products and equalizers this file prepares.
* The constructions adapt Mathlib's to continuous ring homomorphisms: `piFan`/`piFanIsLimit`
  follow `TopCat.piFan`/`TopCat.piFanIsLimit`
  (`Mathlib/Topology/Category/TopCat/Limits/Products.lean`) on the topological side and
  `CommRingCat.piFan`/`CommRingCat.piFanIsLimit` on the algebraic side, and
  `equalizerFork`/`equalizerForkIsLimit` follow `CommRingCat.equalizerFork`/
  `CommRingCat.equalizerForkIsLimit` (`Mathlib/Algebra/Category/Ring/Constructions.lean`),
  with the topology carried through each construction.
-/

public section

namespace TauCeti.TopCommRingCat

open CategoryTheory Limits

universe v u

/-- The explicit product fan of a family of topological commutative rings: the pointwise ring
under the product topology, with the evaluation projections. -/
@[expose, simps! pt π_app]
def piFan {β : Type v} (f : β → TopCommRingCat.{max u v}) : Fan f :=
  Fan.mk (TopCommRingCat.of (∀ b, f b)) fun b => ⟨Pi.evalRingHom _ b, continuous_apply b⟩

/-- The pointwise ring under the product topology is the product in `TopCommRingCat`. -/
def piFanIsLimit {β : Type v} (f : β → TopCommRingCat.{max u v}) : IsLimit (piFan f) where
  lift s := ⟨RingHom.pi fun b => (s.π.app ⟨b⟩).val, continuous_pi fun b => (s.π.app ⟨b⟩).2⟩
  fac _ _ := rfl
  uniq s m h := by
    apply Subtype.ext
    refine RingHom.ext fun x => funext fun b => ?_
    exact congrArg (fun g => (g : _ →+* _) x) (congrArg Subtype.val (h ⟨b⟩))

instance {β : Type v} (f : β → TopCommRingCat.{max u v}) : HasProduct f :=
  HasLimit.mk ⟨piFan f, piFanIsLimit f⟩

instance : HasProducts.{v} TopCommRingCat.{max u v} := fun _ =>
  ⟨fun _ => hasLimit_of_iso Discrete.natIsoFunctor.symm⟩

variable {R S : TopCommRingCat.{u}} (f g : R ⟶ S)

/-- The explicit equalizer fork of a parallel pair: the agreement subring
`RingHom.eqLocus` under the subspace topology. -/
@[expose, simps! pt π_app]
def equalizerFork : Fork f g :=
  Fork.ofι (P := TopCommRingCat.of (RingHom.eqLocus f.val g.val))
    ⟨(RingHom.eqLocus f.val g.val).subtype, continuous_subtype_val⟩
    (by exact Subtype.ext (RingHom.ext fun x => x.2))

/-- The agreement subring under the subspace topology is the equalizer in
`TopCommRingCat`. -/
def equalizerForkIsLimit : IsLimit (equalizerFork f g) :=
  Fork.IsLimit.mk _
    (fun s =>
      ⟨(s.ι.val).codRestrict _ fun x =>
          congrArg (fun (h : _ →+* _) => h x) (congrArg Subtype.val s.condition),
        s.ι.2.subtype_mk _⟩)
    (fun _ => rfl)
    (fun s m h => by
      apply Subtype.ext
      refine RingHom.ext fun x => Subtype.ext ?_
      exact congrArg (fun (g : _ →+* _) => g x) (congrArg Subtype.val h))

instance : HasLimit (parallelPair f g) :=
  HasLimit.mk ⟨equalizerFork f g, equalizerForkIsLimit f g⟩

instance : HasEqualizers TopCommRingCat.{u} :=
  ⟨fun F => hasLimit_of_iso (diagramIsoParallelPair F).symm⟩

end TauCeti.TopCommRingCat

end
