/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro hpq
  cases' hpq with hp hq
  apply hp
  done

example : P ∧ Q → Q := by
  intro hpq
  cases' hpq with hp hq
  apply hq
  done

example : (P → Q → R) → P ∧ Q → R := by
  intro hpqr hpq
  cases' hpq with hp hq
  apply hpqr
  . apply hp
  . apply hq
  done

example : P → Q → P ∧ Q := by
  intro hp hq
  constructor
  . apply hp
  . apply hq
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro hpq
  cases' hpq with hp hq
  constructor
  . apply hq
  . apply hp
  done

example : P → P ∧ True := by
  intro hp
  constructor
  . apply hp
  . triv
  done

example : False → P ∧ False := by
  intro hf
  constructor
  . exfalso
    apply hf
  . apply hf
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro hpq hqr
  constructor
  . apply hpq.left
  . apply hqr.right
  done

example : (P ∧ Q → R) → P → Q → R := by
  intro h hp hq
  apply h
  constructor
  . apply hp
  . apply hq
  done
