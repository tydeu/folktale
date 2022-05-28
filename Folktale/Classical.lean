/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under the MIT license described in the file LICENSE.
Authors: Mac Malone
-/

/-!
Some additions to `Classical` namespace to provide shorthand definitions
for common inference rules in classical logic.
-/

namespace Classical

/-- Double negation elimination -/
theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp => hp)
    (fun hnp => absurd hnp h)

/--
De Morgan's law for conjunctions (i.e., `And`):
the negation of a conjunction is the disjunction of the negations.
-/
theorem dm_and (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp => Or.inr fun hq => h ⟨hp, hq⟩)
    (fun hnp => Or.inl hnp)

/--
De Morgan's law for disjunctions (i.e., `Or`):
The negation of a disjunction is the conjunction of the negations
-/
theorem dm_or (h : ¬(p ∨ q)) : ¬p ∧ ¬q :=
  And.intro
    (Or.elim (em p)
      (fun hp => absurd (Or.inl hp) h)
      (fun hnp => hnp))
    (Or.elim (em q)
      (fun hq => absurd (Or.inr hq) h)
      (fun hnq => hnq))
