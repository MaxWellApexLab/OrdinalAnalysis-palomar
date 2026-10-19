/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/

module

public import Bridge.Order
public import OrdinalAnalysis.Gentzen.GentzenTheorem

/-!
# Bridge, step 6: the two halves

`upper_precM : Upper precM` and `lower_precM : Lower precM`, from the development's
`gentzen_upper_bound` and `gentzen_lower_bound` (`OrdinalAnalysis/Gentzen/`), which are stated with
Foundation's proof system.

* Upper: a model of `PA[X]` of `Challenge` is a model of `paLX` (`models_paLX_iff`), so soundness
  gives `closedTI φ ⌜a⌝` in it; `eval_tiUptoAt` reads that sentence, `val_numeral` reads the
  numeral, and `prec_precCode_iff` and `eval_fmF` translate the ordering and the formula.
* Lower: completeness turns non-provability of `TI ≺` into a model of `paLX` with real equality
  in which `TI ≺` fails; `isPA_ofF` makes it a model of `Challenge`, and `eval_TI` reads the failure.

The two reading lemmas `eval_tiUptoAt` and `eval_TI` are generic in the ordering formula and the
formula `φ`: no concrete formula of the development is ever unfolded (this keeps the kernel work of
the second-kernel check small).
-/

@[expose] public section

set_option linter.style.haveILetI false

namespace GentzenEpsilon0
namespace Bridge

open LO.FirstOrder
open LO LO.FirstOrder.Arithmetic

/-! ## The upper bound -/

/-- Propositional core of `eval_tiUptoAt`. -/
theorem prog_aux {M : Type} (A : M → M → Prop) (B : M → Prop) (c : M) :
    ((∃ x, (∀ z, ¬A z x ∨ B z) ∧ ¬B x) ∨ ∀ x, ¬A x c ∨ B x) ↔
      ((∀ x, (∀ y, A y x → B y) → B x) → ∀ x, A x c → B x) := by
  constructor
  · rintro (⟨x, h1, h2⟩ | h) hprog
    · exfalso; exact h2 (hprog x fun y hy => (h1 y).resolve_left (not_not.mpr hy))
    · intro x hx; exact (h x).resolve_left (not_not.mpr hx)
  · intro h
    by_cases hp : ∀ x, (∀ y, A y x → B y) → B x
    · right
      intro x
      by_cases hx : A x c
      · exact Or.inr (h hp x hx)
      · exact Or.inl hx
    · left
      push Not at hp
      obtain ⟨x, h1, h2⟩ := hp
      refine ⟨x, fun z => ?_, h2⟩
      by_cases hz : A z x
      · exact Or.inr (h1 z hz)
      · exact Or.inl hz

/-- Reading of `TI(P, φ, t)` (generic in `P`, `φ`, `t`, and in the structure): the
formula `tiUptoAt P φ t` says "if `φ` is progressive along `P` then `φ` holds below the value
of `t`".  `precAt P y x` is `P` with the two bound variables replaced by `y`, `x`; it is read
`P` at `![y, x]`.  No concrete formula is unfolded. -/
theorem eval_tiUptoAt {M : Type} (I : Interp M) (P : Semiformula LXF ℕ 2)
    (φ : Semiformula LXF ℕ 1) (t : Semiterm LXF ℕ 0) (f : ℕ → M) :
    Semiformula.Eval (s := fstr I) ![] f (OrdinalAnalysis.Gentzen.tiUptoAt P φ t) ↔
      ((∀ x, (∀ y, Semiformula.Eval (s := fstr I) ![y, x] f P →
            Semiformula.Eval (s := fstr I) ![y] f φ) →
          Semiformula.Eval (s := fstr I) ![x] f φ) →
        ∀ x, Semiformula.Eval (s := fstr I) ![x, Semiterm.val (s := fstr I) ![] f t] f P →
          Semiformula.Eval (s := fstr I) ![x] f φ) := by
  simp only [OrdinalAnalysis.Gentzen.tiUptoAt, OrdinalAnalysis.Gentzen.progAt, OrdinalAnalysis.Gentzen.belowAt,
    OrdinalAnalysis.Gentzen.formulaAt, OrdinalAnalysis.Gentzen.precAt]
  simp
  exact prog_aux (fun y x => Semiformula.Eval (s := fstr I) ![y, x] f P)
    (fun x => Semiformula.Eval (s := fstr I) ![x] f φ) (Semiterm.val (s := fstr I) ![] f t)

/-- The `ORingStructure` numeral of `ringStr I` is `Interp.nat`. -/
theorem numeral_eq_nat {M : Type} (I : Interp M) (h : PAminus I) :
    ∀ n : ℕ, @ORingStructure.numeral M (ringStr I) n = I.nat n
  | 0 => rfl
  | 1 => by
    show I.one = I.add I.zero I.one
    rw [h.add_comm, h.add_zero]
  | n + 2 => by
    show I.add (@ORingStructure.numeral M (ringStr I) (n + 1)) I.one = I.add (I.nat (n + 1)) I.one
    rw [numeral_eq_nat I h (n + 1)]

/-- The numeral of the development, evaluated in a model of `PA⁻`, is `Interp.nat`.
-/
theorem val_numeral {M : Type} (I : Interp M) (h : PAminus I) (f : ℕ → M) (n : ℕ) :
    Semiterm.val (s := fstr I) ![] f ((n : ℕ) : Semiterm LXF ℕ 0) = I.nat n := by
  letI := ringStr I
  letI := fstr I
  haveI := fstr_oring I
  have e : ((n : ℕ) : Semiterm LXF ℕ 0) =
      (Semiterm.Operator.numeral LXF n).operator ![] := rfl
  rw [e, Semiterm.val_operator]
  have := Structure.numeral_eq_numeral (L := LXF) (M := M) n
  have h0 : (Semiterm.val (s := fstr I) ![] f ∘ (![] : Fin 0 → Semiterm LXF ℕ 0)) = ![] :=
    Subsingleton.elim _ _
  rw [h0]
  exact this.trans (numeral_eq_nat I h n)

/-- `Upper precM`, from `gentzen_upper_bound`. -/
theorem upper_precM : Upper precM := by
  intro φ a ha M I hI v hprog x hx
  haveI : Nonempty M := ⟨I.zero⟩
  have hmodel : (fstr I).toStruc ⊧* OrdinalAnalysis.Gentzen.paLX := (models_paLX_iff I).mpr hI
  have hprov := OrdinalAnalysis.Gentzen.UpperBound.gentzen_upper_bound (fmF φ) a ha
  have hsem := (Theory.Proof.sound hprov) hmodel
  letI := fstr I
  have hcl : ∀ f : ℕ → M, Semiformula.Evalf f (OrdinalAnalysis.Gentzen.tiUptoAt
      OrdinalAnalysis.Gentzen.CodedNotation.precCode (fmF φ)
      (OrdinalAnalysis.Gentzen.UpperBound.notationTerm ⟨a, ha⟩)) :=
    models_iff_proposition.mp hsem
  have h1 := (eval_tiUptoAt I OrdinalAnalysis.Gentzen.CodedNotation.precCode (fmF φ)
    (OrdinalAnalysis.Gentzen.UpperBound.notationTerm ⟨a, ha⟩) v).mp (hcl v)
  have hval : Semiterm.val (s := fstr I) ![] v
      (OrdinalAnalysis.Gentzen.UpperBound.notationTerm ⟨a, ha⟩) = I.nat (code a) := by
    show Semiterm.val (s := fstr I) ![] v
      ((OrdinalAnalysis.Gentzen.NotationBridge.nonoteCode ⟨a, ha⟩ : ℕ) : Semiterm LXF ℕ 0)
        = _
    rw [val_numeral I hI.1 v]
    exact congrArg I.nat (code_eq a).symm
  have E1 : ∀ y, Semiformula.Eval (s := fstr I) ![y] v (fmF φ) ↔ I.sat φ v ![y] :=
    fun y => by rw [eval_fmF I φ v ![y], rev_one]; exact Iff.rfl
  have E2 : ∀ y z, Semiformula.Eval (s := fstr I) ![y, z] v
      OrdinalAnalysis.Gentzen.CodedNotation.precCode ↔ I.prec precM y z :=
    fun y z => (prec_precCode_iff I v y z).symm
  rw [hval] at h1
  exact (E1 x).mp (h1 (fun z hz => (E1 z).mpr
    (hprog z (fun y hy => (E1 y).mp (hz y ((E2 y z).mpr hy))))) x ((E2 x _).mpr hx))

/-! ## The lower bound -/

/-- Propositional core of `eval_TI`. -/
theorem ti_aux {M : Type} (A : M → M → Prop) (B : M → Prop) :
    ((∃ x, (∀ z, ¬A z x ∨ B z) ∧ ¬B x) ∨ ∀ x, B x) ↔
      ((∀ x, (∀ y, A y x → B y) → B x) → ∀ x, B x) := by
  constructor
  · rintro (⟨x, h1, h2⟩ | h) hprog
    · exfalso; exact h2 (hprog x fun y hy => (h1 y).resolve_left (not_not.mpr hy))
    · exact h
  · intro h
    by_cases hp : ∀ x, (∀ y, A y x → B y) → B x
    · exact Or.inr (h hp)
    · left
      push Not at hp
      obtain ⟨x, h1, h2⟩ := hp
      refine ⟨x, fun z => ?_, h2⟩
      by_cases hz : A z x
      · exact Or.inr (h1 z hz)
      · exact Or.inl hz

/-- Reading of `TI(P)` (generic in `P`): progressiveness of `X` along `P` implies `X`
everywhere.  `TI P = ∼Prog P ⋎ ∀¹ X(#0)`.  -/
theorem eval_TI {M : Type} (I : Interp M) (P : Semiformula LXF ℕ 2) (f : ℕ → M) :
    Semiformula.Eval (s := fstr I) ![] f (OrdinalAnalysis.Gentzen.TI P) ↔
      ((∀ x, (∀ y, Semiformula.Eval (s := fstr I) ![y, x] f P → I.X y) → I.X x) →
        ∀ x, I.X x) := by
  simp only [OrdinalAnalysis.Gentzen.TI, OrdinalAnalysis.Gentzen.Prog, OrdinalAnalysis.Gentzen.below,
    OrdinalAnalysis.Gentzen.Xat, OrdinalAnalysis.Gentzen.precAt]
  have hX : ∀ {n : ℕ} (b : Fin (n + 1) → M),
      Semiformula.Eval (s := fstr I) b f
        (Semiformula.rel (Sum.inr OrdinalAnalysis.Gentzen.XRel.X) ![(#0 : Semiterm LXF ℕ (n + 1))]) ↔ I.X (b 0) :=
    fun b => Iff.rfl
  simp [hX]
  exact ti_aux (fun y x => Semiformula.Eval (s := fstr I) ![y, x] f P) I.X

/-- `Lower precM`, from `gentzen_lower_bound` and completeness. -/
theorem lower_precM : Lower precM := by
  intro hall
  apply OrdinalAnalysis.Gentzen.LowerBound.gentzen_lower_bound
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ s _ hM
  have hpa : IsPA (ofF s) := isPA_ofF s hM
  have hX := hall M (ofF s) hpa
  rw [models_iff_proposition]
  intro f
  have h := eval_TI (ofF s) OrdinalAnalysis.Gentzen.CodedNotation.precCode f
  rw [fstr_ofF] at h
  refine h.mpr ?_
  intro hprog
  refine hX (fun x hx => hprog x fun y hy => hx y ?_)
  exact (prec_precCode_iff (ofF s) f y x).mpr (by rwa [fstr_ofF])

end Bridge
end GentzenEpsilon0
