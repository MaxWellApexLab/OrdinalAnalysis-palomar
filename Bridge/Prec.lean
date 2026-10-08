/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
import Bridge.PA
import OrdinalAnalysis.Gentzen.CodedNotation

/-!
# Bridge, step 4: the ordering formula and the arithmetic reading of a model of `PA`

* `interpOf V X` is the `Interp` of a type with an `ORingStructure` and a predicate `X`; every
  `I : Interp M` is `interpOf M X` for the `ringStr I` (`interpOf_ringStr`, by `rfl`).
* `models_ISigma1`: a model of `PA[X]` has `𝗜𝚺₁` as a model of arithmetic (so that everything the
  development proves about `V ⊧* 𝗜𝚺₁` applies to it).
* `toPrec P` is the `Formula (Fin 2)` of a Foundation formula `P` in two bound variables, and
  `prec_iff` says `x ≺ y` in `I` is `P` evaluated at `![x, y]`.
* `prec_precCode_iff` specializes this to `precCode`, whose value does not depend on the free
  variables.
-/

set_option linter.style.haveILetI false

namespace GentzenEpsilon0
namespace Bridge

open LO.FirstOrder
open LO LO.FirstOrder.Arithmetic

/-- The `Interp` of an `ORingStructure` and a predicate. -/
def interpOf (V : Type) [ORingStructure V] (X : V → Prop) : Interp V :=
  ⟨0, 1, (· + ·), (· * ·), (· < ·), X⟩

theorem interpOf_ringStr {M : Type} (I : Interp M) : @interpOf M (ringStr I) I.X = I := rfl

/-- A model of `PA[X]` is a model of `𝗜𝚺₁` in the language of arithmetic. -/
theorem models_ISigma1 {M : Type} [Nonempty M] (I : Interp M) (h : IsPA I) :
    (@standardModel M (ringStr I)).toStruc ⊧* 𝗜𝚺₁ := by
  letI := fstr I
  haveI : M↓[LXF] ⊧* OrdinalAnalysis.Gentzen.paLX := (models_paLX_iff I).mpr h
  have := OrdinalAnalysis.Gentzen.CodedNotation.paLX_models_ISigmaOne_reduct (M := M)
  rw [reduct_eq] at this
  exact this

/-! ### The ordering formula -/

/-- The `Formula (Fin 2)` of a Foundation formula `P` in two bound variables: `x ≺ y` is `P(x, y)`. -/
def toPrec (P : Semiformula LXF ℕ 2) : LX.Formula (Fin 2) :=
  (fmM P).toFormula.relabel (Sum.elim (fun _ => (0 : Fin 2)) Fin.rev)

theorem prec_iff {M : Type} (I : Interp M) (P : Semiformula LXF ℕ 2) (x y : M) :
    I.prec (toPrec P) x y ↔ Semiformula.Eval (s := fstr I) ![x, y] (fun _ => x) P := by
  letI := I.structure
  have h1 : (![x, y] : Fin 2 → M) ∘ (Sum.elim (fun _ : ℕ => (0 : Fin 2)) Fin.rev) =
      Sum.elim (fun _ : ℕ => x) (fun i : Fin 2 => (![x, y] : Fin 2 → M) i.rev) := by
    funext i
    rcases i with i | i <;> rfl
  rw [eval_fmM I P (fun _ => x) ![x, y]]
  unfold Interp.prec toPrec
  rw [FirstOrder.Language.Formula.realize_relabel, h1,
    FirstOrder.Language.BoundedFormula.realize_toFormula]
  exact Iff.rfl

/-- `precCode` does not depend on the free variables. -/
theorem eval_precCode_indep {M : Type} (I : Interp M) (b : Fin 2 → M) (f g : ℕ → M) :
    Semiformula.Eval (s := fstr I) b f OrdinalAnalysis.Gentzen.CodedNotation.precCode ↔
      Semiformula.Eval (s := fstr I) b g OrdinalAnalysis.Gentzen.CodedNotation.precCode := by
  simp only [OrdinalAnalysis.Gentzen.CodedNotation.precCode,
    OrdinalAnalysis.Gentzen.CodedNotation.liftCode, Semiformula.eval_lMap, Semiformula.eval_emb]

/-- The ordering of the development, as a `Formula (Fin 2)`. -/
noncomputable def precM : LX.Formula (Fin 2) :=
  toPrec OrdinalAnalysis.Gentzen.CodedNotation.precCode

theorem prec_precCode_iff {M : Type} (I : Interp M) (f : ℕ → M) (x y : M) :
    I.prec precM x y ↔
      Semiformula.Eval (s := fstr I) ![x, y] f OrdinalAnalysis.Gentzen.CodedNotation.precCode :=
  (prec_iff I _ x y).trans (eval_precCode_indep I _ _ _)

end Bridge
end GentzenEpsilon0
