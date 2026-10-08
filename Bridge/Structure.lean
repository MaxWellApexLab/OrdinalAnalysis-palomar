/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
import Bridge.Defs
import OrdinalAnalysis.Gentzen.Setup

/-!
# Bridge, step 1: structures

The `Challenge` speaks about `Interp M`, a bare bundle of `0, 1, +, ·, <, X` on a type `M`,
evaluated with Mathlib's model theory.  The development speaks about Foundation's
`Structure LX M`.  This file converts between the two.

* `fstr I` is the Foundation structure of an `Interp`, and it satisfies `Structure.Eq`
  (equality is the real one).
* `ofF s` reads an `Interp` off a Foundation structure; on `fstr I` it gives back `I`
  definitionally (`ofF_fstr`).
* `fstr_ofF` : for a structure with real equality, `fstr (ofF s) = s`.
-/

namespace GentzenEpsilon0
namespace Bridge

open LO.FirstOrder

/-- Foundation's `LX` (arithmetic plus one unary predicate). -/
abbrev LXF : Language := OrdinalAnalysis.Gentzen.LX

/-- The Foundation structure of an `Interp`. -/
abbrev fstr {M : Type} (I : Interp M) : Structure LXF M where
  func := fun {k} f v =>
    match k, f with
    | _, Sum.inl Language.ORing.Func.zero => I.zero
    | _, Sum.inl Language.ORing.Func.one => I.one
    | _, Sum.inl Language.ORing.Func.add => I.add (v 0) (v 1)
    | _, Sum.inl Language.ORing.Func.mul => I.mul (v 0) (v 1)
  rel := fun {k} r v =>
    match k, r with
    | _, Sum.inl Language.ORing.Rel.eq => v 0 = v 1
    | _, Sum.inl Language.ORing.Rel.lt => I.lt (v 0) (v 1)
    | _, Sum.inr OrdinalAnalysis.Gentzen.XRel.X => I.X (v 0)

/-- The `Interp` of a Foundation structure. -/
def ofF {M : Type} (s : Structure LXF M) : Interp M where
  zero := s.func (Sum.inl Language.ORing.Func.zero) ![]
  one := s.func (Sum.inl Language.ORing.Func.one) ![]
  add := fun a b => s.func (Sum.inl Language.ORing.Func.add) ![a, b]
  mul := fun a b => s.func (Sum.inl Language.ORing.Func.mul) ![a, b]
  lt := fun a b => s.rel (Sum.inl Language.ORing.Rel.lt) ![a, b]
  X := fun a => s.rel (Sum.inr OrdinalAnalysis.Gentzen.XRel.X) ![a]

theorem ofF_fstr {M : Type} (I : Interp M) : ofF (fstr I) = I := rfl

/-- Equality in `fstr I` is the real equality. -/
theorem fstr_eq {M : Type} (I : Interp M) :
    @Structure.Eq LXF M (fstr I) _ :=
  @Structure.Eq.mk LXF M (fstr I) _ (fun a b => by
    simp only [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq, Semiformula.eval_rel]
    exact Iff.rfl)

section
variable {M : Type} [s : Structure LXF M] [Structure.Eq LXF M]

/-- In a structure with real equality, the equality symbol is equality. -/
theorem rel_eq_iff (v : Fin 2 → M) :
    s.rel (Sum.inl Language.ORing.Rel.eq) v ↔ v 0 = v 1 := by
  have h := Structure.eq_iff_eq (L := LXF) (M := M) (v := v)
  simp only [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.eval_rel] at h
  exact h

/-- With real equality, a Foundation structure is the structure of its `Interp`. -/
theorem fstr_ofF : fstr (ofF s) = s := by
  apply Structure.ext
  · funext k f v
    match k, f with
    | _, Sum.inl Language.ORing.Func.zero => 
      have : v = ![] := Subsingleton.elim _ _
      subst this; rfl
    | _, Sum.inl Language.ORing.Func.one => 
      have : v = ![] := Subsingleton.elim _ _
      subst this; rfl
    | _, Sum.inl Language.ORing.Func.add => 
      have : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
      rw [this]; rfl
    | _, Sum.inl Language.ORing.Func.mul => 
      have : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
      rw [this]; rfl
    | _, Sum.inr e => exact e.elim
  · funext k r v
    match k, r with
    | _, Sum.inl Language.ORing.Rel.eq =>
      exact propext (rel_eq_iff (M := M) v).symm
    | _, Sum.inl Language.ORing.Rel.lt =>
      have : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
      rw [this]; rfl
    | _, Sum.inr OrdinalAnalysis.Gentzen.XRel.X =>
      have : v = ![v 0] := by ext i; fin_cases i; rfl
      rw [this]; rfl
end

end Bridge
end GentzenEpsilon0
