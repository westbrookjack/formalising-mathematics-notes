/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part 1 of the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro h
  apply h
  trivial



example : False → ¬True := by
  intro h1
  change True → False
  intro h2
  exact h1

example : ¬False → True := by
  trivial

example : True → ¬False := by
    intro h1
    change False→False
    intro h2
    exact h2

example : False → ¬P := by
  intro hF
  exfalso
  exact hF

example : P → ¬P → False := by
  intro hP hNP
  apply hNP
  exact hP

example : P → ¬¬P := by
  intro hP
  change (P→False)→False
  intro h
  apply h at hP
  exact hP

example : (P → Q) → ¬Q → ¬P := by
  intro h1 h2
  change P →False
  intro hP
  apply h1 at hP
  apply h2
  exact hP

example : ¬¬False → False := by
  intro h
  apply h
  change False → False
  intro hF
  exact hF

example : ¬¬P → P := by
  intro h
  by_contra hnP
  apply h
  exact hnP


example : (¬Q → ¬P) → P → Q := by
  intro h1 hP
  by_contra hnQ
  apply h1 at hnQ
  apply hnQ
  exact hP
