/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (`∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP

example : Q → P ∨ Q := by
  intro h
  right
  exact h

-- Here are a few ways to break down a disjunction
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ hPR hQR
  cases hPoQ with
  | inl h => apply hPR at h; exact h
  | inr h => apply hQR at h; exact h

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ hPR hQR
  obtain h | h := hPoQ
  · apply hPR
    exact h
  · apply hQR
    exact h

example : P ∨ Q → (P → R) → (Q → R) → R := by
  rintro (h | h) hPR hQR
  · apply hPR
    exact h
  · apply hQR
    exact h

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  rintro (h | h)
  · right
    exact h
  · left
    exact h

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  rintro (h1 | h1)
  · obtain h2 | h2 := h1
    · left
      exact h2
    · right; left
      exact h2
  · right; right
    exact h1
  rintro (h1 | h1)
  · left; left
    exact h1
  · obtain h2 | h2 := h1
    · left; right
      exact h2
    · right
      exact h2




example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPR hQS
  rintro (h | h)
  · left
    apply hPR
    exact h
  · right
    apply hQS
    exact h



example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ
  rintro (h | h)
  · left
    apply hPQ
    exact h
  · right
    exact h

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1 h2
  rw[h1]
  rw[h2]



-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor

  intro h
  constructor
  by_contra hP
  have hPoQ : P ∨ Q := by
    left
    exact hP
  apply h
  exact hPoQ

  by_contra hQ
  apply h
  right
  exact hQ

  rintro⟨left, right⟩
  by_contra h
  obtain h1 | h1 := h
  · apply left
    exact h1
  · apply right
    exact h1

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor

  intro h
  by_cases hP : P

  right
  by_contra hQ
  apply h
  constructor
  exact hP
  exact hQ

  left
  exact hP

  intro h
  by_contra hC
  obtain ⟨left, right⟩ := hC

  obtain h1 | h1 := h
  · apply h1
    exact left
  · apply h1
    exact right
