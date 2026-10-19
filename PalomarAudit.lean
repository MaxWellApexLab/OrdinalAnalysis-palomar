/-
  Kernel axiom audit for the Comparator solution declaration.

  The `#print axioms` below makes the Lean kernel traverse the entire dependency graph of the
  named declaration.  Expected output:
    [propext, Classical.choice, Quot.sound]
  -- Lean 4's three foundational axioms, and exactly the `permitted_axioms` list of
  `comparator.json`.  A `sorry` anywhere in a dependency graph would appear as `sorryAx`.

  Run on its own:
      lake env lean PalomarAudit.lean

  The `Challenge` module is deliberately not audited: it states its theorem and proves it by
  `sorry`, which is the Comparator protocol.
-/

module

public import Solution

-- comparator.json

@[expose] public section

#print axioms GentzenEpsilon0.gentzen_theorem
