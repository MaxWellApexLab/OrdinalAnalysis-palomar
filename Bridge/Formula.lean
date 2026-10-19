/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/

module

public import Bridge.Structure

/-!
# Bridge, step 2: formulas

Two translations, with evaluation lemmas, between Mathlib's `LX`-formulas (`Challenge`) and
Foundation's `Semiformula LX ξ n` (the development).

* `fmF : BoundedFormula ξ n → Semiformula LXF ξ n`,
* `fmM : Semiformula LXF ξ n → BoundedFormula ξ n`.

Bound variables are numbered from the other end in the two libraries (Mathlib quantifies the
*last* variable, `Fin.snoc`; Foundation the *first*, `x :> b`), so a bound variable `i : Fin n` is
translated to `Fin.rev i`, and both evaluation lemmas read

    Eval (s := fstr I) b f (translation φ) ↔ I.satG φ f (fun i => b i.rev)      (resp. the converse).

Both translations are structural recursions that are only ever *applied to abstract formulas* in
lemmas; nothing here is unfolded on a concrete formula.
-/

@[expose] public section

namespace GentzenEpsilon0
namespace Bridge

open LO.FirstOrder

/-! ### Symbols -/

/-- Mathlib's function symbols of `LX`, as Foundation's. -/
def fnF : ∀ {k}, Fn k → LXF.Func k
  | _, .zero => Sum.inl Language.ORing.Func.zero
  | _, .one => Sum.inl Language.ORing.Func.one
  | _, .add => Sum.inl Language.ORing.Func.add
  | _, .mul => Sum.inl Language.ORing.Func.mul

/-- Mathlib's relation symbols of `LX`, as Foundation's. -/
def rlF : ∀ {k}, Rl k → LXF.Rel k
  | _, .lt => Sum.inl Language.ORing.Rel.lt
  | _, .X => Sum.inr OrdinalAnalysis.Gentzen.XRel.X

/-- Foundation's function symbols of `LX`, as Mathlib's. -/
def fnM : ∀ {k}, LXF.Func k → Fn k
  | _, Sum.inl Language.ORing.Func.zero => .zero
  | _, Sum.inl Language.ORing.Func.one => .one
  | _, Sum.inl Language.ORing.Func.add => .add
  | _, Sum.inl Language.ORing.Func.mul => .mul
  | _, Sum.inr e => e.elim

/-! ### Reversal of bound variables -/

theorem cons_comp_rev {M : Type} {n : ℕ} (b : Fin n → M) (x : M) :
    (fun i : Fin (n + 1) => (x :> b) i.rev) = Fin.snoc (fun i : Fin n => b i.rev) x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · rw [Fin.snoc_castSucc, Fin.rev_castSucc]
    rfl

/-! ### Mathlib to Foundation -/

/-- Terms, Mathlib to Foundation. -/
def tmF {α : Type} {n : ℕ} : FirstOrder.Language.Term LX (α ⊕ Fin n) → Semiterm LXF α n
  | .var (Sum.inl a) => Semiterm.fvar a
  | .var (Sum.inr i) => Semiterm.bvar i.rev
  | .func f ts => Semiterm.func (fnF f) (fun i => tmF (ts i))

/-- Formulas, Mathlib to Foundation. -/
def fmF {α : Type} : ∀ {n : ℕ}, FirstOrder.Language.BoundedFormula LX α n → Semiformula LXF α n
  | _, .falsum => Semiformula.falsum
  | _, .equal t₁ t₂ =>
      Semiformula.rel (Sum.inl Language.ORing.Rel.eq) ![tmF t₁, tmF t₂]
  | _, .rel R ts => Semiformula.rel (rlF R) (fun i => tmF (ts i))
  | _, .imp φ ψ => Semiformula.or (Semiformula.neg (fmF φ)) (fmF ψ)
  | _, .all φ => Semiformula.all (fmF φ)

theorem val_tmF {M : Type} (I : Interp M) {α : Type} {n : ℕ}
    (t : FirstOrder.Language.Term LX (α ⊕ Fin n)) (f : α → M) (b : Fin n → M) :
    Semiterm.val (s := fstr I) b f (tmF t) =
      @FirstOrder.Language.Term.realize LX M I.structure _ (Sum.elim f (fun i => b i.rev)) t := by
  induction t with
  | var a => rcases a with a | i <;> simp [tmF]
  | func g ts ih =>
    have h : (fun i => Semiterm.val (s := fstr I) b f (tmF (ts i))) =
        fun i => @FirstOrder.Language.Term.realize LX M I.structure _
          (Sum.elim f (fun i => b i.rev)) (ts i) := funext ih
    show (fstr I).func (fnF g) (fun i => Semiterm.val (s := fstr I) b f (tmF (ts i))) = _
    rw [h]
    cases g <;> rfl

/-- Satisfaction with an arbitrary type of free variables. -/
abbrev _root_.GentzenEpsilon0.Interp.satG {M : Type} (I : Interp M) {α : Type} {n : ℕ}
    (φ : FirstOrder.Language.BoundedFormula LX α n) (f : α → M) (xs : Fin n → M) : Prop :=
  @FirstOrder.Language.BoundedFormula.Realize LX M I.structure α n φ f xs

theorem eval_fmF {M : Type} (I : Interp M) {α : Type} :
    ∀ {n : ℕ} (φ : FirstOrder.Language.BoundedFormula LX α n) (f : α → M) (b : Fin n → M),
      Semiformula.Eval (s := fstr I) b f (fmF φ) ↔ I.satG φ f (fun i => b i.rev)
  | _, .falsum, f, b => Iff.rfl
  | _, .equal t₁ t₂, f, b => by
    simp only [fmF]
    change (Semiterm.val (s := fstr I) b f (tmF t₁) = Semiterm.val (s := fstr I) b f (tmF t₂)) ↔ _
    rw [val_tmF, val_tmF]; exact Iff.rfl
  | _, .rel R ts, f, b => by
    show ((fstr I).rel (rlF R) _) ↔ _
    have h : (fun i => Semiterm.val (s := fstr I) b f (tmF (ts i))) =
        fun i => @FirstOrder.Language.Term.realize LX M I.structure _
          (Sum.elim f (fun i => b i.rev)) (ts i) := funext fun i => val_tmF I (ts i) f b
    show (fstr I).rel (rlF R) (fun i => Semiterm.val (s := fstr I) b f (tmF (ts i))) ↔ _
    rw [h]
    cases R <;> exact Iff.rfl
  | _, .imp φ ψ, f, b => by
    have h1 := eval_fmF I φ f b
    have h2 := eval_fmF I ψ f b
    have e : fmF (φ.imp ψ) = (∼(fmF φ) ⋎ fmF ψ) := rfl
    rw [e, LO.LogicalConnective.HomClass.map_or, LO.LogicalConnective.HomClass.map_neg]
    exact (or_congr (not_congr h1) h2).trans imp_iff_not_or.symm
  | _, .all φ, f, b => by
    show (∀ x, Semiformula.Eval (s := fstr I) (x :> b) f (fmF φ)) ↔
      ∀ x, I.satG φ f (Fin.snoc (fun i => b i.rev) x)
    refine forall_congr' fun x => ?_
    rw [eval_fmF I φ f (x :> b), cons_comp_rev]

/-! ### Foundation to Mathlib -/

/-- Terms, Foundation to Mathlib. -/
def tmM {ξ : Type} {n : ℕ} : Semiterm LXF ξ n → FirstOrder.Language.Term LX (ξ ⊕ Fin n)
  | .bvar i => .var (Sum.inr i.rev)
  | .fvar x => .var (Sum.inl x)
  | .func f v => .func (fnM f) (fun i => tmM (v i))

/-- An atomic formula of `LXF`, as a Mathlib formula (the equality symbol becomes `equal`). -/
def relM {ξ : Type} {n : ℕ} :
    ∀ {k}, LXF.Rel k → (Fin k → FirstOrder.Language.Term LX (ξ ⊕ Fin n)) →
      FirstOrder.Language.BoundedFormula LX ξ n
  | _, Sum.inl Language.ORing.Rel.eq, ts => FirstOrder.Language.BoundedFormula.equal (ts 0) (ts 1)
  | _, Sum.inl Language.ORing.Rel.lt, ts => FirstOrder.Language.BoundedFormula.rel Rl.lt ts
  | _, Sum.inr OrdinalAnalysis.Gentzen.XRel.X, ts => FirstOrder.Language.BoundedFormula.rel Rl.X ts

/-- Formulas, Foundation to Mathlib. -/
def fmM {ξ : Type} : ∀ {n : ℕ}, Semiformula LXF ξ n → FirstOrder.Language.BoundedFormula LX ξ n
  | _, .verum => FirstOrder.Language.BoundedFormula.imp .falsum .falsum
  | _, .falsum => .falsum
  | _, .rel r v => relM r (fun i => tmM (v i))
  | _, .nrel r v => .imp (relM r (fun i => tmM (v i))) .falsum
  | _, .and φ ψ => .imp (.imp (fmM φ) (.imp (fmM ψ) .falsum)) .falsum
  | _, .or φ ψ => .imp (.imp (fmM φ) .falsum) (fmM ψ)
  | _, .all φ => .all (fmM φ)
  | _, .exs φ => .imp (.all (.imp (fmM φ) .falsum)) .falsum

theorem val_tmM {M : Type} (I : Interp M) {ξ : Type} {n : ℕ}
    (t : Semiterm LXF ξ n) (f : ξ → M) (b : Fin n → M) :
    Semiterm.val (s := fstr I) b f t =
      @FirstOrder.Language.Term.realize LX M I.structure _ (Sum.elim f (fun i => b i.rev))
        (tmM t) := by
  induction t with
  | bvar i => simp [tmM]
  | fvar x => simp [tmM]
  | @func k g ts ih =>
    have h : (fun i => Semiterm.val (s := fstr I) b f (ts i)) =
        fun i => @FirstOrder.Language.Term.realize LX M I.structure _
          (Sum.elim f (fun i => b i.rev)) (tmM (ts i)) := funext ih
    show (fstr I).func g (fun i => Semiterm.val (s := fstr I) b f (ts i)) = _
    rw [h]
    rcases g with g | e
    · cases g <;> rfl
    · exact e.elim

theorem eval_relM {M : Type} (I : Interp M) {ξ : Type} {n : ℕ} {k : ℕ} (r : LXF.Rel k)
    (v : Fin k → Semiterm LXF ξ n) (f : ξ → M) (b : Fin n → M) :
    (fstr I).rel r (fun i => Semiterm.val (s := fstr I) b f (v i)) ↔
      I.satG (relM r (fun i => tmM (v i))) f (fun i => b i.rev) := by
  have h : (fun i => Semiterm.val (s := fstr I) b f (v i)) =
      fun i => @FirstOrder.Language.Term.realize LX M I.structure _
        (Sum.elim f (fun i => b i.rev)) (tmM (v i)) := funext fun i => val_tmM I (v i) f b
  rw [h]
  rcases r with r | r
  · cases r <;> exact Iff.rfl
  · cases r; exact Iff.rfl

theorem eval_fmM {M : Type} (I : Interp M) {ξ : Type} :
    ∀ {n : ℕ} (φ : Semiformula LXF ξ n) (f : ξ → M) (b : Fin n → M),
      Semiformula.Eval (s := fstr I) b f φ ↔ I.satG (fmM φ) f (fun i => b i.rev)
  | _, .verum, f, b => by
    simp only [fmM]
    exact ⟨fun _ h => h, fun _ => trivial⟩
  | _, .falsum, f, b => Iff.rfl
  | _, .rel r v, f, b => by
    simp only [fmM, Semiformula.eval_rel]
    exact eval_relM I r v f b
  | _, .nrel r v, f, b => by
    simp only [fmM, Semiformula.eval_nrel]
    exact (not_congr (eval_relM I r v f b)).trans Iff.rfl
  | _, .and φ ψ, f, b => by
    have h1 := eval_fmM I φ f b
    have h2 := eval_fmM I ψ f b
    show (Semiformula.Eval (s := fstr I) b f φ ∧ Semiformula.Eval (s := fstr I) b f ψ) ↔ _
    rw [h1, h2]
    exact (and_congr Iff.rfl not_not.symm).trans Classical.not_imp.symm
  | _, .or φ ψ, f, b => by
    have h1 := eval_fmM I φ f b
    have h2 := eval_fmM I ψ f b
    show (Semiformula.Eval (s := fstr I) b f φ ∨ Semiformula.Eval (s := fstr I) b f ψ) ↔ _
    rw [h1, h2]
    exact or_iff_not_imp_left
  | _, .all φ, f, b => by
    show (∀ x, Semiformula.Eval (s := fstr I) (x :> b) f φ) ↔
      ∀ x, I.satG (fmM φ) f (Fin.snoc (fun i => b i.rev) x)
    refine forall_congr' fun x => ?_
    rw [eval_fmM I φ f (x :> b), cons_comp_rev]
  | _, .exs φ, f, b => by
    show (∃ x, Semiformula.Eval (s := fstr I) (x :> b) f φ) ↔
      ¬ ∀ x, ¬ I.satG (fmM φ) f (Fin.snoc (fun i => b i.rev) x)
    rw [not_forall_not]
    refine exists_congr fun x => ?_
    rw [eval_fmM I φ f (x :> b), cons_comp_rev]

end Bridge
end GentzenEpsilon0
