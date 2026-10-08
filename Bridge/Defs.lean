/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
import Mathlib

/-!
# The definitions of `Challenge`, verbatim

This file is generated from `Challenge.lean`: it is that file from `open FirstOrder` up to the
statement of `gentzen_theorem`, character for character.  It exists so that the `Solution`
environment contains the same declarations, with the same names and bodies, as the `Challenge`
environment, which is what the Comparator compares.  Do not edit by hand.
-/

open FirstOrder FirstOrder.Language

namespace GentzenEpsilon0

/-! ### The language: `0, 1, +, ·, <` and one fresh unary predicate `X` -/

inductive Fn : ℕ → Type
  | zero : Fn 0
  | one : Fn 0
  | add : Fn 2
  | mul : Fn 2

inductive Rl : ℕ → Type
  | lt : Rl 2
  | X : Rl 1

def LX : Language := ⟨Fn, Rl⟩

/-- The data of an `LX`-structure on a type `M` (equality is Mathlib's). -/
structure Interp (M : Type) where
  zero : M
  one : M
  add : M → M → M
  mul : M → M → M
  lt : M → M → Prop
  X : M → Prop

abbrev Interp.structure {M : Type} (I : Interp M) : LX.Structure M where
  funMap := fun {n} f xs =>
    match n, f with
    | _, Fn.zero => I.zero
    | _, Fn.one => I.one
    | _, Fn.add => I.add (xs 0) (xs 1)
    | _, Fn.mul => I.mul (xs 0) (xs 1)
  RelMap := fun {n} r xs =>
    match n, r with
    | _, Rl.lt => I.lt (xs 0) (xs 1)
    | _, Rl.X => I.X (xs 0)

/-- `φ(v, xs)` holds in the structure `I`. -/
def Interp.sat {M : Type} (I : Interp M) {n : ℕ} (φ : LX.BoundedFormula ℕ n)
    (v : ℕ → M) (xs : Fin n → M) : Prop :=
  @BoundedFormula.Realize LX M I.structure ℕ n φ v xs

/-- `x ≺ y` for a formula `prec` in two free variables. -/
def Interp.prec {M : Type} (I : Interp M) (prec : LX.Formula (Fin 2)) (x y : M) : Prop :=
  @Formula.Realize LX M I.structure (Fin 2) prec ![x, y]

/-! ### Models of `PA[X]`: `PA⁻` plus induction for every formula of `LX`, with parameters -/

structure PAminus {M : Type} (I : Interp M) : Prop where
  add_zero : ∀ x, I.add x I.zero = x
  add_assoc : ∀ x y z, I.add (I.add x y) z = I.add x (I.add y z)
  add_comm : ∀ x y, I.add x y = I.add y x
  add_eq_of_lt : ∀ x y, I.lt x y → ∃ z, I.add x z = y
  zero_le : ∀ x, x = I.zero ∨ I.lt I.zero x
  zero_lt_one : I.lt I.zero I.one
  one_le_of_zero_lt : ∀ x, I.lt I.zero x → I.one = x ∨ I.lt I.one x
  add_lt_add : ∀ x y z, I.lt x y → I.lt (I.add x z) (I.add y z)
  mul_zero : ∀ x, I.mul x I.zero = I.zero
  mul_one : ∀ x, I.mul x I.one = x
  mul_assoc : ∀ x y z, I.mul (I.mul x y) z = I.mul x (I.mul y z)
  mul_comm : ∀ x y, I.mul x y = I.mul y x
  mul_lt_mul : ∀ x y z, I.lt x y → I.lt I.zero z → I.lt (I.mul x z) (I.mul y z)
  distr : ∀ x y z, I.mul x (I.add y z) = I.add (I.mul x y) (I.mul x z)
  lt_irrefl : ∀ x, ¬ I.lt x x
  lt_trans : ∀ x y z, I.lt x y → I.lt y z → I.lt x z
  lt_tri : ∀ x y, I.lt x y ∨ x = y ∨ I.lt y x

def Induction {M : Type} (I : Interp M) : Prop :=
  ∀ (φ : LX.BoundedFormula ℕ 1) (v : ℕ → M),
    I.sat φ v ![I.zero] → (∀ x, I.sat φ v ![x] → I.sat φ v ![I.add x I.one]) →
    ∀ x, I.sat φ v ![x]

/-- `I` is a model of `PA[X]`. -/
def IsPA {M : Type} (I : Interp M) : Prop := PAminus I ∧ Induction I

/-! ### Cantor normal form codes -/

open scoped Classical in
noncomputable def Interp.pair {M : Type} (I : Interp M) (a b : M) : M :=
  if I.lt a b then I.add (I.mul b b) a else I.add (I.add (I.mul a a) a) b

/-- `oadd e n r` is `ω^e · n + r`, coded by `pair (pair e n) r + 1`. -/
noncomputable def Interp.oadd {M : Type} (I : Interp M) (e n r : M) : M :=
  I.add (I.pair (I.pair e n) r) I.one

/-- The numeral `n` of the model. -/
def Interp.nat {M : Type} (I : Interp M) : ℕ → M
  | 0 => I.zero
  | n + 1 => I.add (I.nat n) I.one

/-- The code of a Cantor normal form, in `ℕ`. -/
def code : ONote → ℕ
  | 0 => 0
  | .oadd e n r => Nat.pair (Nat.pair (code e) (n : ℕ)) (code r) + 1

/-- `prec` obeys the Cantor-normal-form comparison recursion in every model of `PA[X]`. -/
def IsCNFOrder (prec : LX.Formula (Fin 2)) : Prop :=
  ∀ (M : Type) (I : Interp M), IsPA I →
    let lt := I.prec prec
    let nf := fun x => x = I.zero ∨ lt I.zero x
    (∀ x, ¬ lt x I.zero) ∧
    (∀ e n r, lt I.zero (I.oadd e n r) ↔
      n ≠ I.zero ∧ nf e ∧ nf r ∧
        (r = I.zero ∨ ∃ e₂ n₂ r₂, r = I.oadd e₂ n₂ r₂ ∧ lt e₂ e)) ∧
    (∀ e n r e₂ n₂ r₂, lt (I.oadd e n r) (I.oadd e₂ n₂ r₂) ↔
      nf (I.oadd e n r) ∧ nf (I.oadd e₂ n₂ r₂) ∧
        (lt e e₂ ∨ (e = e₂ ∧ (I.lt n n₂ ∨ (n = n₂ ∧ lt r r₂)))))

/-- The standard model `ℕ`, with `X` empty. -/
def stdInterp : Interp ℕ := ⟨0, 1, (· + ·), (· * ·), (· < ·), fun _ => False⟩

/-- On codes of normal forms, `prec` is Mathlib's order on notations (that of the ordinals). -/
def Standard (prec : LX.Formula (Fin 2)) : Prop :=
  ∀ a b : ONote, a.NF → b.NF → (a < b ↔ stdInterp.prec prec (code a) (code b))

/-- In `ℕ`, `prec` relates only codes of normal forms. -/
def Field (prec : LX.Formula (Fin 2)) : Prop :=
  ∀ x y : ℕ, stdInterp.prec prec x y →
    (∃ a : ONote, a.NF ∧ code a = x) ∧ (∃ b : ONote, b.NF ∧ code b = y)

/-- `PA[X] ⊢ TI(≺, φ, ⌜a⌝)` for every formula `φ` and every normal form `a`. -/
def Upper (prec : LX.Formula (Fin 2)) : Prop :=
  ∀ (φ : LX.BoundedFormula ℕ 1) (a : ONote), a.NF →
    ∀ (M : Type) (I : Interp M), IsPA I → ∀ v : ℕ → M,
      (∀ x, (∀ y, I.prec prec y x → I.sat φ v ![y]) → I.sat φ v ![x]) →
      ∀ x, I.prec prec x (I.nat (code a)) → I.sat φ v ![x]

/-- `PA[X] ⊬ TI(≺, X)`: a model of `PA[X]` where `X` is progressive along `≺` but not total. -/
def Lower (prec : LX.Formula (Fin 2)) : Prop :=
  ¬ ∀ (M : Type) (I : Interp M), IsPA I →
      (∀ x, (∀ y, I.prec prec y x → I.X y) → I.X x) → ∀ x, I.X x

end GentzenEpsilon0
