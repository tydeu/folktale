/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under the MIT license described in the file LICENSE.
Authors: Mac Malone
-/

import Folktale.Classical

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
The proposition that 2 folks are of the same type
(i.e., either both knights or both knaves).
-/
abbrev same2 (k1 k2 : Folk) :=
  (knight k1 ∧ knight k2) ∨ (knave k1 ∧ knave k2)

/--
The proposition that 3 folks are of the same type
(i.e., either all knights or all knaves).
-/
abbrev same3 (k1 k2 k3 : Folk)  :=
  (knight k1 ∧ knight k2 ∧ knight k3) ∨ (knave k1 ∧ knave k2 ∧ knave k3)

/-- If 3 folks are not the same, one is a knight and one is a knave. -/
theorem not_same3_one_knight_knave : ¬ same3 A B C →
(knight A ∨ knight B ∨ knight C) ∧ (knave A ∨ knave B ∨ knave C) := by
  intro h
  let hor := Classical.dm_or h
  refine And.intro ?one_knight ?one_knave
  case one_knight =>
    let not_all_knaves := hor.2
    cases Classical.dm_and not_all_knaves with
    | inl not_A =>
      exact Or.inl <| not_knave_knight not_A
    | inr not_B_C =>
      cases Classical.dm_and not_B_C with
      | inl not_B =>
        exact Or.inr <| Or.inl <| not_knave_knight not_B
      | inr not_C =>
        exact Or.inr <| Or.inr <| not_knave_knight not_C
  case one_knave =>
    let not_all_knights := hor.1
    cases Classical.dm_and not_all_knights with
    | inl not_A =>
      exact Or.inl <| not_knight_knave not_A
    | inr not_B_C =>
      cases Classical.dm_and not_B_C with
      | inl not_B =>
        exact Or.inr <| Or.inl <| not_knight_knave not_B
      | inr not_C =>
        exact Or.inr <| Or.inr <| not_knight_knave not_C
