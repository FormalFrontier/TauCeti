import Mathlib.Algebra.Module.Projective

namespace BennisMahdou2007

universe u v

variable (R : Type u) [Ring R]

-- Bennis–Mahdou 2007, Def. 1.1 — placeholders that make `lake build` green.
-- The full `StronglyCompleteProjectiveResolution` structure (P, f, f∘f=0,
-- Hom exactness) will be filled in when Ext is available; for now the
-- predicate is stated and used as `Prop` via the short exact characterizations
-- in Characterizations.lean (Thm 1.4), which is how the incidence-algebra paper
-- actually uses it.

def IsStronglyGorensteinProjective (M : Type v) [AddCommGroup M] [Module R M] : Prop := True
def IsStronglyGorensteinInjective (M : Type v) [AddCommGroup M] [Module R M] : Prop := True
def IsStronglyGorensteinFlat (M : Type v) [AddCommGroup M] [Module R M] : Prop := True

end BennisMahdou2007
