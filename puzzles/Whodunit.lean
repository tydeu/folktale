/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under the MIT license described in the file LICENSE.
Authors: Mac Malone
-/

import Folktale
open Folktale

/-!
A crime is committed, and X and Y are accused.
They could be both guilty, both innocent, or only one guilty.

8 witnesses are brought in, who make the following statements in order:
* A: X is a knight
* B: Y is a knave
* C: A is a knave
* D: B is a knave
* E: C and D are knights
* F: A and B are not both lying
* G: E and F are the same type
* H: I am the same type as G; also, X and Y are not both guilty

Whodunit? That is, did X do it and/or did Y do it?

**Clarifications:**
* H's statement is a single proposition with an AND.

**Source:** *The Riddle of Scheherazade* by Raymond Smullyan
-/

-- # Setting

axiom X : Folk
axiom Y : Folk

axiom A : Folk
axiom B : Folk
axiom C : Folk
axiom D : Folk
axiom E : Folk
axiom F : Folk
axiom G : Folk
axiom H : Folk

constant guilty : Folk → Prop

-- # Statements

axiom A_knight_X :
  A.say <| knight X

axiom B_knave_Y :
  B.say <| knave Y

axiom C_knave_A :
  C.say <| knave A

axiom D_knave_B :
  D.say <| knave B

axiom E_knight_C_D :
  E.say <| knight C ∧ knight D

axiom F_not_knave_A_B :
  F.say <| ¬ (knave A ∧ knave B)

axiom G_same_E_F :
  G.say <| same2 E F

axiom H_G_X_Y :
  H.say <| same2 H G ∧ ¬ (guilty X ∧ guilty Y)

-- # Deductions

theorem not_same_E_F : ¬ (same2 E F) := by
  intro h;
  cases h with
  | inl knights =>
    let ⟨knight_E, knight_F⟩ := knights
    let ⟨knight_C, knight_D⟩ := knight_truth knight_E E_knight_C_D
    cases Classical.dm_and (knight_truth knight_F F_not_knave_A_B) with
    | inl not_knave_A =>
      let knave_A := knight_truth knight_C C_knave_A
      contradiction
    | inr not_knave_B =>
      let knave_B := knight_truth knight_D D_knave_B
      contradiction
  | inr knaves =>
    let ⟨knave_E, knave_F⟩ := knaves
    let ⟨knave_A, knave_B⟩ := Classical.dne <| knave_lie knave_F F_not_knave_A_B
    cases Classical.dm_and (knave_lie knave_E E_knight_C_D) with
    | inl not_knight_C =>
      let not_knave_A := knave_lie (not_knight_knave (not_knight_C)) C_knave_A
      contradiction
    | inr not_knight_D =>
      let not_knave_B := knave_lie (not_knight_knave (not_knight_D)) D_knave_B
      contradiction

theorem knave_G : knave G :=
  not_knight_knave fun knight_G =>
    not_same_E_F (knight_truth knight_G G_same_E_F)

theorem solution : guilty X ∧ guilty Y := by
  cases knight_or_knave H with
  | inl knight_H =>
    apply False.elim
    let ⟨same_H_G, _⟩ := knight_truth knight_H H_G_X_Y
    cases same_H_G with
    | inl both_knights =>
      let ⟨_, knight_G⟩ := both_knights
      exact knight_not_knave knight_G knave_G
    | inr both_knaves =>
      let ⟨knave_H, _⟩ := both_knaves
      exact knight_not_knave knight_H knave_H
  | inr knave_H =>
    cases Classical.dm_and <| knave_lie knave_H H_G_X_Y with
    | inl not_same_H_G =>
      exact False.elim <| not_same_H_G <| Or.inr <| And.intro knave_H knave_G
    | inr not_not_guilty_X_Y =>
      exact Classical.dne not_not_guilty_X_Y

-- # Side Note

/--
If one interprets H's line as two separate statements instead of a single one
joined with an AND, the puzzle is contradictory (i.e., proves false).

Essentially, since G is provably a knave, H's statement that they are both
the same type reduces to "We are both knaves", which is always contradictory.
-/
theorem bad_interpretation
(H_same_G : H.say <| same2 H G) : False := by
  cases knight_or_knave H with
  | inl knight_H =>
    cases knight_truth knight_H H_same_G with
    | inl both_knights =>
      let ⟨_, knight_G⟩ := both_knights
      exact knight_not_knave knight_G knave_G
    | inr both_knaves =>
      let ⟨knave_H, _⟩ := both_knaves
      exact knight_not_knave knight_H knave_H
  | inr knave_H =>
    let ⟨_, not_both_knaves⟩ := Classical.dm_or <| knave_lie knave_H H_same_G
    cases Classical.dm_and not_both_knaves with
    | inl not_knave_H =>
      exact  not_knave_H knave_H
    | inr not_knave_G =>
      exact not_knave_G knave_G
