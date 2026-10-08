/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
import Bridge.Prec
import OrdinalAnalysis.Gentzen.CodeSurj
import OrdinalAnalysis.Gentzen.PrecStandard

/-!
# Bridge, step 5: the clauses of `Challenge` for the development's ordering

`precM` is the coded ordering `precCode` of the development, read as a Mathlib formula.  This file
proves the three clauses of `Challenge` that concern the ordering alone:

* `isCNFOrder_precM : IsCNFOrder precM`, from the internal recursion equations of
  `OrdinalAnalysis/Gentzen/InternalONote.lean` (`icmp_ocOadd`, `isNF_ocOadd`, ...), stated for an
  arbitrary type `V` with `𝗜𝚺₁` (`cnf_zero_below`, `cnf_oadd_oadd`, ...) and transported to every
  model of `PA[X]` through `interpOf`, `ringStr` and `models_ISigma1`;
* `standard_precM : Standard precM` and `field_precM : Field precM`, from `PrecStandard` and
  `CodeSurj`.

Conventions: `V` is a type with `[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`, exactly as in the
`InternalONote` layer.
-/

set_option linter.style.haveILetI false

namespace GentzenEpsilon0
namespace Bridge

open LO.FirstOrder
open LO LO.FirstOrder.Arithmetic

/-! ## `IsCNFOrder` from the internal recursion equations -/

section VLevel

open OrdinalAnalysis.Gentzen.InternalONote

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `a ≺ b` on the codes of `V`, as the development reads it: `precDef`. -/
def cLt (a b : V) : Prop := isNF a ∧ isNF b ∧ icmp a b = 0

/-- `Interp.pair` of `interpOf V X` is Szudzik's pairing `⟪ , ⟫` of `V`. -/
theorem interp_pair_eq (X : V → Prop) (a b : V) :
    (interpOf V X).pair a b = ⟪a, b⟫ := by
  unfold Interp.pair pair
  by_cases h : a < b
  · have h' : (interpOf V X).lt a b := h
    rw [if_pos h', if_pos h]
    rfl
  · have h' : ¬ (interpOf V X).lt a b := h
    rw [if_neg h', if_neg h]
    rfl

/-- The `Interp.oadd` of `interpOf V X` is the development's `ocOadd`. -/
theorem interp_oadd_eq (X : V → Prop) (e n r : V) :
    (interpOf V X).oadd e n r = ocOadd e n r := by
  unfold Interp.oadd ocOadd
  rw [interp_pair_eq, interp_pair_eq]
  rfl

/-- The formula `precM` of `Challenge`, read in `interpOf V X`, is `cLt`.
Proof: `prec_precCode_iff`, the reading of `precDef` (`CodedNotation.eval_precDef`) through the
reduct identification `reduct_eq`. -/
theorem prec_iff_cLt (X : V → Prop) (x y : V) :
    (interpOf V X).prec precM x y ↔ cLt x y := by
  rw [prec_precCode_iff _ (fun _ => x)]
  simp only [OrdinalAnalysis.Gentzen.CodedNotation.precCode,
    OrdinalAnalysis.Gentzen.CodedNotation.liftCode, Semiformula.eval_lMap, Semiformula.eval_emb]
  rw [reduct_eq]
  exact OrdinalAnalysis.Gentzen.CodedNotation.eval_precDef x y

/-- `icmp a c = 1` is equality. -/
theorem icmp_eq_one_iff {a c : V} : icmp a c = 1 ↔ a = c :=
  ⟨fun h => icmp_eq_imp_eq (max a c) a (le_max_left _ _) c (le_max_right _ _) h,
    fun h => h ▸ icmp_self a a le_rfl⟩

/-- `nf x` of `IsCNFOrder` is `isNF x`. -/
theorem nfc_iff (x : V) : (x = 0 ∨ cLt 0 x) ↔ isNF x := by
  by_cases hx : x = 0
  · subst hx; simp
  · constructor
    · rintro (h | ⟨-, h, -⟩)
      · exact absurd h hx
      · exact h
    · intro h; exact Or.inr ⟨isNF_zero, h, icmp_zero_pos hx⟩

/-- Nothing lies below `0`. -/
theorem cnf_nothing_below (x : V) : ¬ cLt x 0 := by
  rintro ⟨-, -, h⟩
  by_cases hx : x = 0
  · subst hx; simp at h
  · rw [icmp_pos_zero hx] at h
    exact absurd h (by simp)

/-- `0 ≺ ω^e·n + r` is the normal-form condition.  -/
theorem cnf_zero_below (e n r : V) :
    cLt 0 (ocOadd e n r) ↔
      n ≠ 0 ∧ (e = 0 ∨ cLt 0 e) ∧ (r = 0 ∨ cLt 0 r) ∧
        (r = 0 ∨ ∃ e₂ n₂ r₂, r = ocOadd e₂ n₂ r₂ ∧ cLt e₂ e) := by
  have hL : cLt 0 (ocOadd e n r) ↔ isNF (ocOadd e n r) :=
    ⟨fun h => h.2.1, fun h => ⟨isNF_zero, h, icmp_zero_ocOadd e n r⟩⟩
  rw [hL, isNF_ocOadd, nfc_iff, nfc_iff]
  constructor
  · rintro ⟨hn, he, hr, htail⟩
    refine ⟨hn, he, hr, ?_⟩
    by_cases hr0 : r = 0
    · exact Or.inl hr0
    · right
      have hr' : isNF (ocOadd (ocExp r) (ocCoeff r) (ocTail r)) := by
        rw [ocOadd_destruct hr0]; exact hr
      have hexp := ((isNF_ocOadd _ _ _).mp hr').2.1
      have hlt : icmp (ocExp r) e = 0 := htail.resolve_left hr0
      exact ⟨ocExp r, ocCoeff r, ocTail r, (ocOadd_destruct hr0).symm, hexp, he, hlt⟩
  · rintro ⟨hn, he, hr, htail⟩
    refine ⟨hn, he, hr, ?_⟩
    rcases htail with h0 | ⟨e₂, n₂, r₂, hr', hlt⟩
    · exact Or.inl h0
    · right
      rw [hr', ocExp_ocOadd]
      exact hlt.2.2

/-- Lexicographic comparison of two nonzero normal forms.  -/
theorem cnf_oadd_oadd (e n r e₂ n₂ r₂ : V) :
    cLt (ocOadd e n r) (ocOadd e₂ n₂ r₂) ↔
      ((ocOadd e n r = 0 ∨ cLt 0 (ocOadd e n r)) ∧
        (ocOadd e₂ n₂ r₂ = 0 ∨ cLt 0 (ocOadd e₂ n₂ r₂)) ∧
        (cLt e e₂ ∨ (e = e₂ ∧ (n < n₂ ∨ (n = n₂ ∧ cLt r r₂))))) := by
  rw [nfc_iff, nfc_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    have i1 := (isNF_ocOadd e n r).mp h1
    have i2 := (isNF_ocOadd e₂ n₂ r₂).mp h2
    rw [icmp_ocOadd, thenV_eq_zero] at h3
    rcases h3 with h | ⟨h, h'⟩
    · exact Or.inl ⟨i1.2.1, i2.2.1, h⟩
    · right
      refine ⟨icmp_eq_one_iff.mp h, ?_⟩
      rw [thenV_eq_zero] at h'
      rcases h' with h'' | ⟨h'', h'''⟩
      · exact Or.inl (cmpV_eq_zero.mp h'')
      · exact Or.inr ⟨cmpV_eq_one.mp h'', i1.2.2.1, i2.2.2.1, h'''⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [icmp_ocOadd, thenV_eq_zero]
    rcases h3 with ⟨-, -, h⟩ | ⟨h, h'⟩
    · exact Or.inl h
    · right
      refine ⟨icmp_eq_one_iff.mpr h, ?_⟩
      rw [thenV_eq_zero]
      rcases h' with h'' | ⟨h'', h'''⟩
      · exact Or.inl (cmpV_eq_zero.mpr h'')
      · exact Or.inr ⟨cmpV_eq_one.mpr h'', h'''.2.2⟩

end VLevel

/-- The body of `IsCNFOrder` for one model. -/
def CNFBody {M : Type} (I : Interp M) (prec : LX.Formula (Fin 2)) : Prop :=
  let lt := I.prec prec
  let nf := fun x => x = I.zero ∨ lt I.zero x
  (∀ x, ¬ lt x I.zero) ∧
    (∀ e n r, lt I.zero (I.oadd e n r) ↔
      n ≠ I.zero ∧ nf e ∧ nf r ∧
        (r = I.zero ∨ ∃ e₂ n₂ r₂, r = I.oadd e₂ n₂ r₂ ∧ lt e₂ e)) ∧
    (∀ e n r e₂ n₂ r₂, lt (I.oadd e n r) (I.oadd e₂ n₂ r₂) ↔
      nf (I.oadd e n r) ∧ nf (I.oadd e₂ n₂ r₂) ∧
        (lt e e₂ ∨ (e = e₂ ∧ (I.lt n n₂ ∨ (n = n₂ ∧ lt r r₂)))))

/-- `IsCNFOrder` is the body `CNFBody` in every model of `PA[X]`. -/
theorem isCNFOrder_iff (prec : LX.Formula (Fin 2)) :
    IsCNFOrder prec ↔ ∀ (M : Type) (I : Interp M), IsPA I → CNFBody I prec :=
  Iff.rfl

section VLevel

open OrdinalAnalysis.Gentzen.InternalONote

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The clauses of `IsCNFOrder` for `interpOf V X`, from the internal recursion equations. -/
theorem cnfBody_precM (X : V → Prop) : CNFBody (interpOf V X) precM := by
  unfold CNFBody
  simp only [interp_oadd_eq, prec_iff_cLt]
  refine ⟨fun x => cnf_nothing_below x, fun e n r => cnf_zero_below e n r, ?_⟩
  intro e n r e₂ n₂ r₂
  exact cnf_oadd_oadd e n r e₂ n₂ r₂

end VLevel

/-- `IsCNFOrder precM`. -/
theorem isCNFOrder_precM : IsCNFOrder precM := by
  intro M I hI
  haveI : Nonempty M := ⟨I.zero⟩
  letI := ringStr I
  haveI := models_ISigma1 I hI
  exact cnfBody_precM (V := M) I.X

/-- The `code` of `Challenge` is the development's. -/
theorem code_eq (a : ONote) : code a = OrdinalAnalysis.Gentzen.NotationBridge.code a := by
  induction a with
  | zero => rfl
  | oadd e n r ihe ihr => simp [code, OrdinalAnalysis.Gentzen.NotationBridge.code, ihe, ihr]

/-! ## The standard model -/

/-- On codes of normal forms, `precM` is Mathlib's order on `ONote`.
Via `stdInterp = interpOf ℕ (fun _ => False)` (`rfl`), `prec_iff_cLt`, `PrecStandard.precN_iff`,
`PrecStandard.precN_code_iff`. -/
theorem standard_precM : Standard precM := by
  intro a b ha hb
  have h1 := (OrdinalAnalysis.Gentzen.PrecStandard.precN_code_iff ⟨a, ha⟩ ⟨b, hb⟩)
  rw [OrdinalAnalysis.Gentzen.PrecStandard.precN_iff] at h1
  have h2 : stdInterp = interpOf ℕ (fun _ => False) := rfl
  rw [h2, prec_iff_cLt]
  simp only [code_eq]
  exact h1.symm

/-- In `ℕ`, `precM` relates only codes of normal forms.
Via `CodeSurj.isNF_iff_exists_nonote`, as in `OrderType`. -/
theorem field_precM : Field precM := by
  intro x y h
  have h2 : stdInterp = interpOf ℕ (fun _ => False) := rfl
  rw [h2, prec_iff_cLt] at h
  obtain ⟨hx, hy, -⟩ := h
  obtain ⟨o, ho⟩ := (OrdinalAnalysis.Gentzen.CodeSurj.isNF_iff_exists_nonote x).mp hx
  obtain ⟨p, hp⟩ := (OrdinalAnalysis.Gentzen.CodeSurj.isNF_iff_exists_nonote y).mp hy
  exact ⟨⟨o.1, o.2, by rw [code_eq]; exact ho⟩, ⟨p.1, p.2, by rw [code_eq]; exact hp⟩⟩

end Bridge
end GentzenEpsilon0
