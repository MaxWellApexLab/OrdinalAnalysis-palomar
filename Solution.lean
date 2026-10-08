/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
import Bridge.Bounds

/-!
# Solution file: the proof-theoretic ordinal of Peano arithmetic is `ε₀` (Gentzen 1943)

This module supplies a declaration whose type is exactly the type stated in `Challenge`,
together with its proof.

The definitions of `Challenge` (the language `LX`, `Interp`, `IsPA`, `IsCNFOrder`, `Upper`, ...)
are present here with the same names and bodies: they are `Bridge/Defs.lean`, which is
`Challenge.lean` up to its last declaration, character for character (the Comparator checks
this).

The proof delegates to the development:

* `Bridge.Structure`, `Bridge.Formula`, `Bridge.PA` translate between the `Interp` and Mathlib
  formulas of `Challenge` and Foundation's structures and formulas, and show that a model of
  `PA[X]` in the sense of `Challenge` (`IsPA`) is exactly a model of the development's theory
  `paLX` (`Bridge.models_paLX_iff`);
* `Bridge.Prec` reads the coded ordering `precCode` of the development as a Mathlib formula
  `precM`;
* `Bridge.Order` proves `IsCNFOrder precM` from the internal recursion equations of the
  arithmetized notations (`OrdinalAnalysis/Gentzen/InternalONote.lean`), and `Standard precM` and
  `Field precM` from `PrecStandard.lean` and `CodeSurj.lean`;
* `Bridge.Bounds` proves `Upper precM` and `Lower precM` from `gentzen_upper_bound` and
  `gentzen_lower_bound` of the development (`OrdinalAnalysis/Gentzen/`), read through that
  translation.
-/

namespace GentzenEpsilon0

/-- **Gentzen's theorem**, `|PA| = ε₀`. -/
theorem gentzen_theorem :
    ∃ prec : LX.Formula (Fin 2),
      IsCNFOrder prec ∧ Standard prec ∧ Field prec ∧ Upper prec ∧ Lower prec :=
  ⟨Bridge.precM, Bridge.isCNFOrder_precM, Bridge.standard_precM, Bridge.field_precM,
    Bridge.upper_precM, Bridge.lower_precM⟩

end GentzenEpsilon0
