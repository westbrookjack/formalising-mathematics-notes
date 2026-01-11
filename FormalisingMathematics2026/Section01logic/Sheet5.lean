/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor

  intro h1
  rw[h1]

  intro h2
  rw[h2]


example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  rwa[h1]

  -- The pattern `rw` then `assumption` is common enough that it can be abbreviated to `rwa`

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro h
  constructor
  exact h.2
  exact h.1

  intro h
  constructor
  exact h.2
  exact h.1

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor

  rintro ⟨left, right⟩
  constructor
  exact left.1

  constructor
  exact left.2
  exact right

  rintro ⟨left, right⟩
  constructor
  constructor
  exact left
  exact right.1
  exact right.2



example : P ↔ P ∧ True := by
  constructor
  intro hP
  constructor
  exact hP
  trivial

  intro h
  exact h.1

example : False ↔ P ∧ False := by
  constructor

  intro hF
  exfalso
  exact hF

  rintro⟨left, right⟩
  exfalso
  exact right

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro h1 h2

  rw[h1]
  rw[h2]

example : ¬(P ↔ ¬P) := by
  rintro⟨left, right⟩
  by_cases hP : P

  have h1 : ¬P := by
    apply left
    exact hP
  apply h1
  exact hP

  have h2 : P := by
    apply right
    exact hP
  apply hP
  exact h2
