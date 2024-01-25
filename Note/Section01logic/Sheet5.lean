/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  repeat
    intro h
    rw [h]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hpq hqr
  rw [hpq, hqr]
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  repeat
    intro h
    constructor
    . apply h.right
    . apply h.left
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  . intro h
    constructor
    . apply h.left.left
    . constructor
      . apply h.left.right
      . apply h.right
  . intro h
    constructor
    . constructor
      . apply h.left
      . apply h.right.left
    . apply h.right.right
  done

example : P ↔ P ∧ True := by
  constructor
  . intro h
    constructor
    . apply h
    . triv
  . intro h
    apply h.left
  done

example : False ↔ P ∧ False := by
  apply Iff.intro
  . intro hf
    exfalso
    apply hf
  . intro h
    apply h.right
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hpq hrs
  apply Iff.intro
  . intro hpr
    apply And.intro
    . rw [← hpq]
      apply hpr.left
    . rw [← hrs]
      apply hpr.right
  . intro hqs
    cases' hqs with hq hs
    apply And.intro
    . rw [hpq]
      apply hq
    . rw [hrs]
      apply hs
  done

example : ¬(P ↔ ¬P) := by
  intro h
  cases' h with h1 h2
  by_cases h : P
  . apply h1
    . apply h
    . apply h
  . apply h
    apply h2
    apply h
  done
