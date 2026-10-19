/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/

module

public import Bridge.Formula

/-!
# Bridge, step 3: `IsPA` is "model of `paLX`"

For `I : Interp M`:

    (fstr I).toStruc ⊧* paLX   ↔   IsPA I        (`models_paLX_iff`)

where `paLX` is the theory of the development: `𝗘𝗤 LX`, `𝗣𝗔⁻` transported into `LX`, and
the induction scheme for every formula of `LX`.  The equality axioms hold because equality is
real, `𝗣𝗔⁻` is `PAminus` (through the identification of the arithmetic reduct with the standard
structure of an `ORingStructure`), and the induction scheme is `Induction` through the formula
translations of `Bridge.Formula`.

Also `isPA_ofF`: a Foundation structure with real equality that models `paLX` gives an
`IsPA`-interpretation.
-/

@[expose] public section

set_option linter.style.haveILetI false

namespace GentzenEpsilon0
namespace Bridge

open LO.FirstOrder
open LO LO.FirstOrder.Arithmetic

/-- The `ORingStructure` of an `Interp`. -/
abbrev ringStr {M : Type} (I : Interp M) : ORingStructure M :=
  { zero := I.zero, one := I.one, add := I.add, mul := I.mul, lt := I.lt }

theorem fstr_oring {M : Type} (I : Interp M) :
    @Structure.ORing LXF _ M (ringStr I) (fstr I) := by
  letI := ringStr I
  letI := fstr I
  haveI := fstr_eq I
  exact
  { zero := rfl
    one := rfl
    add := fun _ _ => rfl
    mul := fun _ _ => rfl
    eq := (fstr_eq I).eq
    lt := fun _ _ => Iff.rfl }

/-- The arithmetic reduct of `fstr I` is the standard structure of `ringStr I`. -/
theorem reduct_eq {M : Type} (I : Interp M) :
    (fstr I).lMap OrdinalAnalysis.Gentzen.toLX = @standardModel M (ringStr I) := by
  apply Structure.ext
  · funext k f v
    cases f <;> rfl
  · funext k r v
    cases r <;> rfl

/-! ### `PA⁻` -/

/-- `𝗣𝗔⁻` holds in the arithmetic reduct of `fstr I` exactly when `PAminus I` does. -/
theorem models_peanoMinus_iff {M : Type} [Nonempty M] (I : Interp M) :
    (@standardModel M (ringStr I)).toStruc ⊧* 𝗣𝗔⁻ ↔ PAminus I := by
  letI := ringStr I
  constructor
  · intro h
    have H : ∀ {σ : ArithmeticSentence}, σ ∈ 𝗣𝗔⁻ → M↓[ℒₒᵣ] ⊧ σ :=
      fun hσ => Semantics.modelsSet_iff.mp h hσ
    clear h
    exact
    { add_zero := by have := H PeanoMinus.addZero; simp [models_iff] at this; exact this
      add_assoc := by have := H PeanoMinus.addAssoc; simp [models_iff] at this; exact this
      add_comm := by have := H PeanoMinus.addComm; simp [models_iff] at this; exact this
      add_eq_of_lt := by have := H PeanoMinus.addEqOfLt; simp [models_iff] at this; exact this
      zero_le := by
        have := H PeanoMinus.zeroLe; simp only [models_iff] at this
        exact fun x => (this x).imp Eq.symm id
      zero_lt_one := by have := H PeanoMinus.zeroLtOne; simp [models_iff] at this; exact this
      one_le_of_zero_lt := by
        have := H PeanoMinus.oneLeOfZeroLt
        simp only [models_iff, Semiformula.eval_all, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.Fin1.eq_one, Fin.isValue,
          LogicalConnective.HomClass.map_imply, Semiformula.eval_operator, Matrix.comp₂, Semiterm.val_operator, Matrix.comp₀,
          Structure.numeral_eq_numeral, ORingStructure.zero_eq_zero, Semiterm.val_bvar, Matrix.cons_val_fin_one,
          Structure.lt_iff_lt, Matrix.cons_val_zero, Matrix.cons_val_one, ORingStructure.one_eq_one,
          LogicalConnective.Prop.arrow_eq] at this
        exact this
      add_lt_add := by have := H PeanoMinus.addLtAdd; simp [models_iff] at this; exact this
      mul_zero := by have := H PeanoMinus.mulZero; simp [models_iff] at this; exact this
      mul_one := by have := H PeanoMinus.mulOne; simp [models_iff] at this; exact this
      mul_assoc := by have := H PeanoMinus.mulAssoc; simp [models_iff] at this; exact this
      mul_comm := by have := H PeanoMinus.mulComm; simp [models_iff] at this; exact this
      mul_lt_mul := by have := H PeanoMinus.mulLtMul; simp [models_iff] at this; exact this
      distr := by have := H PeanoMinus.distr; simp [models_iff] at this; exact this
      lt_irrefl := by have := H PeanoMinus.ltIrrefl; simp [models_iff] at this; exact this
      lt_trans := by have := H PeanoMinus.ltTrans; simp [models_iff] at this; exact this
      lt_tri := by have := H PeanoMinus.ltTri; simp [models_iff] at this; exact this }
  · intro h
    refine Semantics.modelsSet_iff.mpr fun σ hσ => ?_
    cases hσ with
    | equal φ hφ =>
      have : M↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance
      exact Semantics.modelsSet_iff.mp this hφ
    | addZero => simp [models_iff]; exact h.add_zero
    | addAssoc => simp [models_iff]; exact h.add_assoc
    | addComm => simp [models_iff]; exact h.add_comm
    | addEqOfLt => simp [models_iff]; exact h.add_eq_of_lt
    | zeroLe =>
      simp only [models_iff]
      exact fun x => (h.zero_le x).imp Eq.symm id
    | zeroLtOne => simp [models_iff]; exact h.zero_lt_one
    | oneLeOfZeroLt =>
      simp only [models_iff, Semiformula.eval_all, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.Fin1.eq_one, Fin.isValue,
          LogicalConnective.HomClass.map_imply, Semiformula.eval_operator, Matrix.comp₂, Semiterm.val_operator, Matrix.comp₀,
          Structure.numeral_eq_numeral, ORingStructure.zero_eq_zero, Semiterm.val_bvar, Matrix.cons_val_fin_one,
          Structure.lt_iff_lt, Matrix.cons_val_zero, Matrix.cons_val_one, ORingStructure.one_eq_one,
          LogicalConnective.Prop.arrow_eq]
      exact h.one_le_of_zero_lt
    | addLtAdd => simp [models_iff]; exact h.add_lt_add
    | mulZero => simp [models_iff]; exact h.mul_zero
    | mulOne => simp [models_iff]; exact h.mul_one
    | mulAssoc => simp [models_iff]; exact h.mul_assoc
    | mulComm => simp [models_iff]; exact h.mul_comm
    | mulLtMul => simp [models_iff]; exact h.mul_lt_mul
    | distr => simp [models_iff]; exact h.distr
    | ltIrrefl => simp [models_iff]; exact h.lt_irrefl
    | ltTrans => simp [models_iff]; exact h.lt_trans
    | ltTri => simp [models_iff]; exact h.lt_tri

/-! ### The induction scheme and `paLX` -/

/-- The instance of `succInd` at `φ`, unfolded. -/
theorem eval_succInd_iff {L : Language} [L.ORing] {M : Type} [Structure L M]
    (φ : Semiformula L ℕ 1) (f : ℕ → M) :
    Semiformula.Eval ![] f (succInd φ) ↔
      (Semiformula.Eval ![Semiterm.val ![] f ((0 : ℕ) : Semiterm L ℕ 0)] f φ →
        (∀ x, Semiformula.Eval ![x] f φ →
          Semiformula.Eval ![Semiterm.val ![x] f (‘(#0 + 1)’ : Semiterm L ℕ 1)] f φ) →
        ∀ x, Semiformula.Eval ![x] f φ) := by
  show Semiformula.Eval ![] f ((φ/[((0 : ℕ) : Semiterm L ℕ 0)]) 🡒
      (∀¹ (φ/[(#0 : Semiterm L ℕ 1)] 🡒 φ/[(‘(#0 + 1)’ : Semiterm L ℕ 1)])) 🡒
      ∀¹ (φ/[(#0 : Semiterm L ℕ 1)])) ↔ _
  simp only [LogicalConnective.HomClass.map_imply, Semiformula.eval_all, Semiformula.eval_substs]
  simp [Matrix.empty_eq]

theorem val_zero_term {M : Type} (I : Interp M) (f : ℕ → M) :
    Semiterm.val (s := fstr I) ![] f ((0 : ℕ) : Semiterm LXF ℕ 0) = I.zero := by
  letI := ringStr I
  haveI := fstr_oring I
  simp [Semiterm.val_operator]
  exact rfl

theorem val_succ_term {M : Type} (I : Interp M) (f : ℕ → M) (x : M) :
    Semiterm.val (s := fstr I) ![x] f (‘(#0 + 1)’ : Semiterm LXF ℕ 1) = I.add x I.one := by
  letI := ringStr I
  haveI := fstr_oring I
  simp [Semiterm.val_operator]
  exact rfl

theorem rev_one {M : Type} (x : M) : (fun i : Fin 1 => (![x] : Fin 1 → M) i.rev) = ![x] := by
  funext i
  fin_cases i
  rfl

/-- The induction scheme of `paLX` holds in `fstr I` iff `Induction I`. -/
theorem models_induction_iff {M : Type} [Nonempty M] (I : Interp M) :
    (fstr I).toStruc ⊧* InductionScheme LXF Set.univ ↔ Induction I := by
  letI := fstr I
  constructor
  · intro h φ v h0 hs x
    have hmem : (succInd (fmF φ)).univCl ∈ InductionScheme LXF Set.univ := ⟨fmF φ, trivial, rfl⟩
    have hm := Semantics.modelsSet_iff.mp h hmem
    have hf := (models_iff_proposition.mp hm) v
    have E : ∀ y, Semiformula.Eval (s := fstr I) ![y] v (fmF φ) ↔ I.sat φ v ![y] := fun y => by
      rw [eval_fmF I φ v ![y], rev_one]; exact Iff.rfl
    simp only [Semiformula.Evalf] at hf
    rw [eval_succInd_iff] at hf
    simp only [val_zero_term, val_succ_term] at hf
    exact (E x).mp (hf ((E _).mpr h0) (fun y hy => (E _).mpr (hs y ((E y).mp hy))) x)
  · intro hind
    refine Semantics.modelsSet_iff.mpr fun σ hσ => ?_
    rcases hσ with ⟨ψ, -, rfl⟩
    rw [models_iff_proposition]
    intro f
    have E : ∀ y, Semiformula.Eval (s := fstr I) ![y] f ψ ↔ I.sat (fmM ψ) f ![y] := fun y => by
      rw [eval_fmM I ψ f ![y], rev_one]; exact Iff.rfl
    simp only [Semiformula.Evalf]
    rw [eval_succInd_iff]
    simp only [val_zero_term, val_succ_term]
    intro h0 hs x
    exact (E x).mpr (hind (fmM ψ) f ((E _).mp h0) (fun y hy => (E _).mp (hs y ((E y).mpr hy))) x)

/-- **`IsPA` is "model of `paLX`".** -/
theorem models_paLX_iff {M : Type} [Nonempty M] (I : Interp M) :
    (fstr I).toStruc ⊧* OrdinalAnalysis.Gentzen.paLX ↔ IsPA I := by
  letI := fstr I
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · refine (models_peanoMinus_iff I).mp (Semantics.modelsSet_iff.mpr fun σ hσ => ?_)
      have := Semantics.modelsSet_iff.mp h
        (Set.mem_union_right _ (Set.mem_union_left _ ⟨σ, hσ, rfl⟩))
      rw [Semiformula.models_lMap, reduct_eq] at this
      exact this
    · exact (models_induction_iff I).mp
        (Semantics.ModelsSet.of_subset h
          (Set.subset_union_of_subset_right (Set.subset_union_right) _))
  · rintro ⟨hpa, hind⟩
    haveI := fstr_eq I
    refine Semantics.modelsSet_iff.mpr fun σ hσ => ?_
    rcases hσ with h1 | ⟨σ', hσ', rfl⟩ | h3
    · exact Semantics.modelsSet_iff.mp (Structure.Eq.models_eq LXF M) h1
    · rw [Semiformula.models_lMap, reduct_eq]
      exact Semantics.modelsSet_iff.mp ((models_peanoMinus_iff I).mpr hpa) hσ'
    · exact Semantics.modelsSet_iff.mp ((models_induction_iff I).mpr hind) h3

/-- A Foundation structure with real equality that models `paLX` is an `IsPA`-interpretation. -/
theorem isPA_ofF {M : Type} [Nonempty M] (s : Structure LXF M) [Structure.Eq LXF M]
    (h : s.toStruc ⊧* OrdinalAnalysis.Gentzen.paLX) : IsPA (ofF s) := by
  have := (models_paLX_iff (ofF s)).mp
  rw [fstr_ofF] at this
  exact this h

end Bridge
end GentzenEpsilon0
