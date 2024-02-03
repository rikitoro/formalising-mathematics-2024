/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro h
  left
  apply h
  done

example : Q → P ∨ Q := by
  intro h
  right
  apply h
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hpq hpr hqr
  cases' hpq with hp hq
  . apply hpr hp
  . apply hqr hq
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro hpq
  cases' hpq with hp hq
  . right
    exact hp
  . left
    exact hq
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  apply Iff.intro
  . intro h
    cases' h with hpq hr
    . cases' hpq with hp hp
      . left
        exact hp
      . right
        left
        exact hp
    . right
      right
      exact hr
  . intro h
    cases' h with hp hqr
    . left
      left
      apply hp
    . cases' hqr with hq hr
      . left
        right
        apply hq
      . right
        assumption
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hpr hqs hpq
  cases' hpq with hp hq
  . left
    apply hpr hp
  . right
    apply hqs hq
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hpq hpr
  cases' hpr with hp hr
  . left
    apply hpq hp
  . right
    apply hr
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro hpr hqs
  constructor
  . intro hpq
    rw [← hpr,← hqs]
    assumption
  . intro hrs
    rw [hpr, hqs]
    assumption
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  . intro h
    constructor
    . intro hp
      apply h
      left
      assumption
    . intro hq
      apply h
      right
      assumption
  . intro h
    intro hpq
    cases' hpq with hp hq
    . apply h.left
      assumption
    . apply h.right
      assumption
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  . intro h
    by_cases hp : P
    . right
      intro hq
      apply h
      constructor
      . assumption
      . assumption
    . left
      assumption
  . intro h
    intro h'
    cases' h with hnp hnq
    . apply hnp
      apply h'.left
    . apply hnq
      apply h'.right
  done
