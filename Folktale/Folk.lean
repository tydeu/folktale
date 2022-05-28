/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under the MIT license described in the file LICENSE.
Authors: Mac Malone
-/

/-!
Folktale's formalization of the concept of knights and knaves.
-/

namespace Folktale

-- # Basics

/-- The type of knights and knaves. -/
constant Folk : Type

/-- The proposition of being a knight. -/
constant knight : Folk → Prop

/-- The proposition of being a knave. -/
constant knave : Folk → Prop

/-- The axiom that all folks are either knights or knaves. -/
axiom knight_or_knave (K : Folk) :
  knight K ∨ knave K

/-- The axiom that no folks are both a knight and a knave. -/
axiom knight_not_knave {K : Folk} :
  knight K → knave K → False

/-- A folk that is not a knight is a knave. -/
theorem not_knight_knave {K : Folk} : ¬ knight K → knave K := by
  intro not_knight_K
  cases knight_or_knave K with
  | inl knight_K => exact absurd knight_K not_knight_K
  | inr knave_K => exact knave_K

/-- A folk that is not a knave is a knight. -/
theorem not_knave_knight {K : Folk} : ¬ knave K → knight K := by
  intro not_knave_K
  cases knight_or_knave K with
  | inl knight_K => exact knight_K
  | inr knave_K => exact absurd knave_K not_knave_K

/-- Binary connective representing a statement by a knight or knave. -/
constant Folk.say : Folk → Prop → Prop

/-- The axiom that knights always tell the truth. -/
axiom knight_truth  {K : Folk} {P : Prop} :
  knight K → K.say P → P

/-- The axiom that knaves always lie. -/
axiom knave_lie {K : Folk} {P : Prop} :
  knave K → K.say P → ¬ P

-- # Helpers

/--
The proposition that two folks are of the same type
(i.e., either both knights or both knaves).
-/
def same2 (k1 k2 : Folk) :=
  (knight k1 ∧ knight k2) ∨ (knave k1 ∧ knave k2)
