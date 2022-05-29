/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under the MIT license described in the file LICENSE.
Authors: Mac Malone
-/

import Folktale
open Folktale

/-!
Either A, B, or C is a traitor. A accuses B, B accuses C.

When asked by the judge,
"Are all you the same type?" (i.e. all knights or all knaves),
C answers either yes or no.

The judge hears this answer and is not able to convict someone,
but is able to acquit someone.

After that folk is acquitted, the judge asks one of the others:
"Are the two of you the same type?" (i.e. both knights or both knaves).
The folk answers yes.

Who is the traitor?

**Clarifications:**
* Exactly one of A, B, or C is a traitor.
* The traitor can be a knight.
* A, B, C know who the traitor is.
* The second question is asked to one of them who was not acquitted.

**Source:** *The Riddle of Scheherazade* by Raymond Smullyan
-/

/-! # Setting -/

axiom A : Folk
axiom B : Folk
axiom C : Folk

constant traitor : Folk → Prop

/-! # Rules -/

axiom one_traitor :
  traitor A ∨ traitor B ∨ traitor C

axiom exactly_one_traitor :
  ¬ (traitor A ∧ traitor B) ∧
  ¬ (traitor A ∧ traitor C) ∧
  ¬ (traitor B ∧ traitor C)

axiom A_accuses_B :
  A.say <| traitor B

axiom B_accuses_C :
  B.say <| traitor C

/-- Of the two folks, one of them says they are both the same. -/
abbrev answer2 (k1 k2 : Folk) :=
  k1.say (same2 k1 k2) ∨ k2.say (same2 k1 k2)

/-- The folk that is acquitted determines which of the other two are asked. -/
abbrev question2 (k : Folk) :=
  ((k = A) → answer2 B C) ∧
  ((k = B) → answer2 A C) ∧
  ((k = C) → answer2 A B)

/--
If C-answered yes (i.e., said they are all the same type),
then that lead to the acquittal of one and questioning of the other two.
Then, with that information, the traitor was able to be determined.
-/
axiom question1_same {a t : Folk} :
  (C.say (same3 A B C) → ¬ traitor a) →
  (C.say (same3 A B C) ∧ question2 a → traitor t) →
  traitor t

/--
If C-answered no ((i.e., said they are not all the same type),
then that lead to the acquittal of one and questioning of the other two.
Then, with that information, the traitor was able to be determined.
-/
axiom question1_not_same {a t : Folk} :
  (C.say (¬ same3 A B C) → ¬ traitor a) →
  (C.say (¬ same3 A B C) ∧ question2 a → traitor t) →
  traitor t

/-! # Deductions -/

/-- If B and C are asked and C is a knave, then C is the traitor. -/
theorem answer2_B_C_traitor
(answer2_B_C : answer2 B C) (knave_C : knave C) : traitor C := by
  cases answer2_B_C with
  | inl B_same =>
    apply False.elim
    cases knight_or_knave B with
    | inl knight_B =>
      let both_same := knight_truth knight_B B_same
      cases both_same with
      | inl both_knights =>
        exact knight_not_knave both_knights.2 knave_C
      | inr both_knaves =>
        exact knight_not_knave knight_B both_knaves.1
    | inr knave_B =>
      let not_both_same := knave_lie knave_B B_same
      exact not_both_same <| Or.inr <| And.intro knave_B knave_C
  | inr C_same =>
    let not_both_same := knave_lie knave_C C_same
    let not_both_knave := Classical.dm_and (Classical.dm_or not_both_same).2
    cases not_both_knave with
    | inl not_knave_B =>
      let knight_B := not_knave_knight not_knave_B
      exact knight_truth knight_B B_accuses_C
    | inr not_knave_C =>
      contradiction

/- If C said all were the same, then A is not the traitor and C is a knave. -/
theorem C_same_acquit_A_knave :
C.say (same3 A B C) → ¬ traitor A ∧ knave C := by
  intro C_same
  cases knight_or_knave C with
  | inl knight_C =>
    apply False.elim
    let all_same := knight_truth knight_C C_same
    cases all_same with
    | inl all_knights =>
      let traitor_B := knight_truth all_knights.1 A_accuses_B
      let traitor_C := knight_truth all_knights.2.1 B_accuses_C
      exact exactly_one_traitor.2.2 <| And.intro traitor_B traitor_C
    | inr all_knaves =>
      exact knight_not_knave knight_C all_knaves.2.2
  | inr knave_C =>
    apply And.intro _ knave_C; intro traitor_A
    let not_all_same := knave_lie knave_C C_same
    let one_knight := not_same3_one_knight_knave not_all_same |>.1
    cases one_knight with
    | inl knight_A =>
      let traitor_B := knight_truth knight_A A_accuses_B
      exact exactly_one_traitor.1 <| And.intro traitor_A traitor_B
    | inr knight_B_C =>
      cases knight_B_C with
      | inl knight_B =>
        let traitor_C := knight_truth knight_B B_accuses_C
        exact exactly_one_traitor.2.1 <| And.intro traitor_A traitor_C
      | inr knight_C =>
        exact knight_not_knave knight_C knave_C

/-- C is the traitor. -/
theorem solution : traitor C := by
  apply question1_same ?acquit ?convict
  case acquit =>
    intro C_same
    exact C_same_acquit_A_knave C_same |>.1
  case convict =>
    intro ⟨all_same, question2_A⟩
    let answer2_B_C := question2_A.1 rfl
    let knave_C := C_same_acquit_A_knave all_same |>.2
    exact answer2_B_C_traitor answer2_B_C knave_C

/-! # Side Note -/

/-- If both A and B are knaves, the traitor is A. -/
theorem knave_A_B_traitor
(knave_A : knave A) (knave_B : knave B) : traitor A := by
  cases one_traitor with
  | inl traitor_A =>
    exact traitor_A
  | inr traitor_B_C =>
    cases traitor_B_C with
    | inl traitor_B =>
      let not_traitor_B := knave_lie knave_A A_accuses_B
      contradiction
    | inr traitor_C =>
      let not_traitor_C := knave_lie knave_B B_accuses_C
      contradiction

/--
If C said they were not all the same,
there is not enough information to acquit anyone.

Such a result is hard to formalize, so it is skipped,
but the content of the proof here helps demonstrate it.
-/
theorem C_not_same_insufficient :
C.say (¬ same3 A B C) → traitor A ∨ traitor B ∨ traitor C := by
  intro C_not_same
  cases knight_or_knave C with
  | inl knight_C =>
    let not_all_same := knight_truth knight_C C_not_same
    let one_knave := not_same3_one_knight_knave not_all_same |>.2
    cases one_knave with
    | inl knave_A =>
      cases knight_or_knave B with
      | inl knight_B =>
        let traitor_C := knight_truth knight_B B_accuses_C
        exact Or.inr <| Or.inr traitor_C
      | inr knave_B =>
        let traitor_A := knave_A_B_traitor knave_A knave_B
        exact Or.inl <| traitor_A
    | inr knave_B_C =>
      cases knave_B_C with
      | inl knave_B =>
        cases knight_or_knave A with
        | inl knight_A =>
          let traitor_B := knight_truth knight_A A_accuses_B
          exact Or.inr <| Or.inl traitor_B
        | inr knave_A =>
          let traitor_A := knave_A_B_traitor knave_A knave_B
          exact Or.inl <| traitor_A
      | inr knave_C =>
        exact False.elim <| knight_not_knave knight_C knave_C
  | inr knave_C =>
    let all_same := Classical.dne <| knave_lie knave_C C_not_same
    cases all_same with
    | inl all_knights =>
      exact False.elim <| knight_not_knave all_knights.2.2 knave_C
    | inr all_knaves =>
      let traitor_A := knave_A_B_traitor all_knaves.1 all_knaves.2.1
      exact Or.inl <| traitor_A
